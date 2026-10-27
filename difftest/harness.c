#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <setjmp.h>
#include <signal.h>
#include <unistd.h>

#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/bigarray.h>

struct reg_state {
    uint64_t x[31];     // 0..247
    uint64_t sp;        // 248
    uint64_t nzcv;      // 256
    uint64_t tpidr;     // 264
    int64_t pc_delta;   // 272
    int status;         // 280
};

#define INPUT_OFF     0x000
#define OUTPUT_OFF    0x200
#define HOST_SAVE_OFF 0x400
#define STACK_TOP_OFF 0x4ff0
#define PROLOGUE_OFF  0x5000
#define TARGET_OFF    0x5100
#define FALLTHRU_OFF  0x5200
#define TAKEN_OFF     0x5300

static uint8_t *g_page = NULL;
static uint8_t *g_scratch_mem = NULL;
static sigjmp_buf g_jmpbuf;
static volatile sig_atomic_t g_got_signal = 0;
static uint8_t g_alt_stack[65536];

static void sig_handler(int sig, siginfo_t *info, void *uc) {
    uint64_t guest_tpidr;
    __asm__ volatile("mrs %0, tpidr_el0" : "=r"(guest_tpidr));
    if (g_page) {
        uint64_t *host_save = (uint64_t *)(g_page + HOST_SAVE_OFF);
        __asm__ volatile("msr tpidr_el0, %0" :: "r"(host_save[1]));
    }
    g_got_signal = sig;

    // Any signal raised at a PC other than the instruction under test means that
    // instruction completed (a branch) and the fault belongs to its landing site.
    if (uc && g_page) {
        ucontext_t *ctx = (ucontext_t *)uc;
        uint64_t fault_pc = (uint64_t)ctx->uc_mcontext.pc;
        uint64_t target_pc = (uint64_t)(g_page + TARGET_OFF);
        if (fault_pc != target_pc) {
            // The instruction at target_pc succeeded and branched to fault_pc!
            struct reg_state *out = (struct reg_state *)(g_page + OUTPUT_OFF);
            for (int i = 0; i < 31; i++) {
                out->x[i] = ctx->uc_mcontext.regs[i];
            }
            out->sp = ctx->uc_mcontext.sp;
            out->nzcv = (ctx->uc_mcontext.pstate & 0xf0000000ULL);
            out->tpidr = guest_tpidr;
            out->pc_delta = (int64_t)(fault_pc - target_pc);
            out->status = 0; // Branch itself completed normally
            g_got_signal = 0;
            siglongjmp(g_jmpbuf, 1);
        }
    }

    siglongjmp(g_jmpbuf, 1);
}

static void emit32(uint32_t *p, uint32_t insn) { *p = insn; }

static uint32_t a64_b(int32_t byte_offset) {
    int32_t imm26 = (byte_offset >> 2) & 0x3ffffff;
    return 0x14000000 | (uint32_t)imm26;
}

static uint32_t a64_adr(int rd, int32_t byte_offset) {
    uint32_t immlo = (byte_offset & 3) << 29;
    uint32_t immhi = ((byte_offset >> 2) & 0x7ffff) << 5;
    return 0x10000000 | immlo | immhi | (rd & 0x1f);
}

void harness_init(void) {
    if (g_page) return;

    g_page = (uint8_t *)mmap(NULL, 0x10000, PROT_READ | PROT_WRITE | PROT_EXEC,
                             MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (g_page == MAP_FAILED) {
        perror("mmap g_page");
        exit(1);
    }

    g_scratch_mem = (uint8_t *)mmap((void*)0x20000000, 0x10000, PROT_READ | PROT_WRITE,
                                    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (g_scratch_mem == MAP_FAILED) {
        g_scratch_mem = (uint8_t *)mmap(NULL, 0x10000, PROT_READ | PROT_WRITE,
                                        MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    }

    stack_t ss = { .ss_sp = g_alt_stack, .ss_size = sizeof(g_alt_stack), .ss_flags = 0 };
    sigaltstack(&ss, NULL);

    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = sig_handler;
    sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
    sigaction(SIGILL, &sa, NULL);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
    sigaction(SIGTRAP, &sa, NULL);
    sigaction(SIGALRM, &sa, NULL);
}

static void build_epilogue(uint32_t *code_start, uint32_t epilogue_off, int64_t pc_delta) {
    uint32_t *code = code_start;
    emit32(code++, 0x9e67001f); // fmov d31, x0
    emit32(code++, 0xd53b4200); // mrs x0, nzcv
    emit32(code++, 0x9e67001e); // fmov d30, x0
    int32_t cur = epilogue_off + (code - code_start) * 4;
    emit32(code++, a64_adr(0, OUTPUT_OFF - cur));
    for (int r = 1; r < 31; r += 2) {
        uint32_t imm7 = (r * 8 / 8) & 0x7f;
        emit32(code++, 0xa9000000 | (imm7 << 15) | ((r + 1) << 10) | (0 << 5) | r);
    }
    emit32(code++, 0x910003e1); // mov x1, sp
    emit32(code++, 0xf9000000 | ((248 / 8) << 10) | (0 << 5) | 1); // str x1, [x0, #248]
    emit32(code++, 0x9e6603e1); // fmov x1, d31
    emit32(code++, 0xf9000000 | ((0 / 8) << 10) | (0 << 5) | 1); // str x1, [x0, #0]
    emit32(code++, 0x9e6603c1); // fmov x1, d30
    emit32(code++, 0xf9000000 | ((256 / 8) << 10) | (0 << 5) | 1); // str x1, [x0, #256]
    emit32(code++, 0xd53bd041); // mrs x1, tpidr_el0
    emit32(code++, 0xf9000000 | ((264 / 8) << 10) | (0 << 5) | 1); // str x1, [x0, #264]

    if (pc_delta >= 0 && pc_delta <= 65535) {
        emit32(code++, 0xd2800001 | ((uint32_t)pc_delta << 5)); // mov x1, #pc_delta
    } else {
        *(int64_t *)(g_page + HOST_SAVE_OFF + 128) = pc_delta;
        cur = epilogue_off + (code - code_start) * 4;
        emit32(code++, a64_adr(1, (HOST_SAVE_OFF + 128) - cur));
        emit32(code++, 0xf9400021); // ldr x1, [x1, #0]
    }
    emit32(code++, 0xf9000000 | ((272 / 8) << 10) | (0 << 5) | 1); // str x1, [x0, #272]

    cur = epilogue_off + (code - code_start) * 4;
    emit32(code++, a64_adr(0, HOST_SAVE_OFF - cur));
    emit32(code++, 0xf9400401); // ldr x1, [x0, #8] (host tpidr)
    emit32(code++, 0xd51bd041); // msr tpidr_el0, x1
    emit32(code++, 0xf9400001); // ldr x1, [x0, #0] (host sp)
    emit32(code++, 0x9100003f); // mov sp, x1
    emit32(code++, 0xa941781d); // ldp x29, x30, [x0, #16] (host fp, lr)
    for (int r = 19; r <= 27; r += 2) {
        uint32_t imm7 = ((32 + (r - 19) * 8) / 8) & 0x7f;
        emit32(code++, 0xa9400000 | (imm7 << 15) | ((r + 1) << 10) | (0 << 5) | r);
    }
    emit32(code++, 0xd65f03c0); // ret
}

static void build_trampoline(uint32_t test_insn, int32_t branch_target_offset) {
    build_epilogue((uint32_t *)(g_page + FALLTHRU_OFF), FALLTHRU_OFF, 4);
    build_epilogue((uint32_t *)(g_page + TAKEN_OFF), TAKEN_OFF, branch_target_offset);

    uint32_t *code = (uint32_t *)(g_page + TARGET_OFF);
    emit32(code++, test_insn);
    emit32(code++, a64_b(FALLTHRU_OFF - (TARGET_OFF + 4)));

    if (branch_target_offset != 0 && branch_target_offset != 4) {
        uint32_t *target_pad = (uint32_t *)(g_page + TARGET_OFF + branch_target_offset);
        emit32(target_pad, a64_b(TAKEN_OFF - (TARGET_OFF + branch_target_offset)));
    }

    code = (uint32_t *)(g_page + PROLOGUE_OFF);
    int32_t cur = PROLOGUE_OFF + (code - (uint32_t *)(g_page + PROLOGUE_OFF)) * 4;
    emit32(code++, a64_adr(0, HOST_SAVE_OFF - cur));
    emit32(code++, 0x910003e1); // mov x1, sp
    emit32(code++, 0xf9000001); // str x1, [x0, #0]
    emit32(code++, 0xd53bd041); // mrs x1, tpidr_el0
    emit32(code++, 0xf9000401); // str x1, [x0, #8]
    emit32(code++, 0xa901781d); // stp x29, x30, [x0, #16]
    for (int r = 19; r <= 27; r += 2) {
        uint32_t imm7 = ((32 + (r - 19) * 8) / 8) & 0x7f;
        emit32(code++, 0xa9000000 | (imm7 << 15) | ((r + 1) << 10) | (0 << 5) | r);
    }

    cur = PROLOGUE_OFF + (code - (uint32_t *)(g_page + PROLOGUE_OFF)) * 4;
    emit32(code++, a64_adr(0, INPUT_OFF - cur));
    emit32(code++, 0xf9400000 | ((264 / 8) << 10) | (0 << 5) | 1); // ldr x1, [x0, #264] (tpidr)
    emit32(code++, 0xd51bd041); // msr tpidr_el0, x1
    emit32(code++, 0xf9400000 | ((256 / 8) << 10) | (0 << 5) | 1); // ldr x1, [x0, #256] (nzcv)
    emit32(code++, 0xd51b4201); // msr nzcv, x1
    emit32(code++, 0xf9400000 | ((248 / 8) << 10) | (0 << 5) | 1); // ldr x1, [x0, #248] (sp)
    emit32(code++, 0x9100003f); // mov sp, x1
    for (int r = 1; r < 31; r += 2) {
        uint32_t imm7 = (r * 8 / 8) & 0x7f;
        emit32(code++, 0xa9400000 | (imm7 << 15) | ((r + 1) << 10) | (0 << 5) | r);
    }
    emit32(code++, 0xf9400000 | ((0 / 8) << 10) | (0 << 5) | 0); // ldr x0, [x0, #0]
    cur = PROLOGUE_OFF + (code - (uint32_t *)(g_page + PROLOGUE_OFF)) * 4;
    emit32(code++, a64_b(TARGET_OFF - cur));

    __builtin___clear_cache((char *)g_page, (char *)(g_page + 0x10000));
}

int harness_run(const struct reg_state *input, struct reg_state *output,
                uint32_t insn, int32_t branch_offset) {
    memcpy(g_page + INPUT_OFF, input, sizeof(*input));
    memset(g_page + OUTPUT_OFF, 0, sizeof(*output));

    build_trampoline(insn, branch_offset);

    g_got_signal = 0;
    if (sigsetjmp(g_jmpbuf, 1) == 0) {
        alarm(1);
        void (*func)() = (void (*)())(g_page + PROLOGUE_OFF);
        func();
        alarm(0);
        memcpy(output, g_page + OUTPUT_OFF, sizeof(*output));
        output->status = 0;
        return 0;
    } else {
        alarm(0);
        uint64_t *host_save = (uint64_t *)(g_page + HOST_SAVE_OFF);
        __asm__ volatile("msr tpidr_el0, %0" :: "r"(host_save[1]));
        if (g_got_signal == 0) {
            // Branch to unmapped address successfully recovered!
            memcpy(output, g_page + OUTPUT_OFF, sizeof(*output));
            output->status = 0;
            return 0;
        }
        output->status = g_got_signal;
        return g_got_signal;
    }
}

uint64_t harness_get_default_sp(void) {
    return (uint64_t)(g_page + STACK_TOP_OFF);
}

uint64_t harness_get_scratch_base(void) {
    return (uint64_t)g_scratch_mem;
}

// OCaml FFI functions

CAMLprim value ocaml_harness_init(value unit) {
    CAMLparam1(unit);
    harness_init();
    CAMLreturn(Val_unit);
}

CAMLprim value ocaml_harness_get_scratch_base(value unit) {
    CAMLparam1(unit);
    harness_init();
    CAMLreturn(caml_copy_int64((int64_t)g_scratch_mem));
}

CAMLprim value ocaml_harness_get_target_pc(value unit) {
    CAMLparam1(unit);
    harness_init();
    CAMLreturn(caml_copy_int64((int64_t)(g_page + TARGET_OFF)));
}

CAMLprim value ocaml_harness_get_default_sp(value unit) {
    CAMLparam1(unit);
    harness_init();
    CAMLreturn(caml_copy_int64((int64_t)(g_page + STACK_TOP_OFF)));
}

CAMLprim value ocaml_harness_run(value v_in, value v_out, value v_insn, value v_boff) {
    CAMLparam4(v_in, v_out, v_insn, v_boff);
    harness_init();

    uint64_t *in_raw = (uint64_t *)Caml_ba_data_val(v_in);
    uint64_t *out_raw = (uint64_t *)Caml_ba_data_val(v_out);

    struct reg_state input, output;
    memset(&input, 0, sizeof(input));
    memset(&output, 0, sizeof(output));

    for (int i = 0; i < 31; i++) {
        input.x[i] = in_raw[i];
    }
    input.sp = in_raw[31];
    input.nzcv = in_raw[32];
    input.tpidr = in_raw[33];

    uint32_t insn = (uint32_t)Long_val(v_insn);
    int32_t boff = (int32_t)Long_val(v_boff);

    int status = harness_run(&input, &output, insn, boff);

    for (int i = 0; i < 31; i++) {
        out_raw[i] = output.x[i];
    }
    out_raw[31] = output.sp;
    out_raw[32] = output.nzcv;
    out_raw[33] = output.tpidr;
    out_raw[34] = (uint64_t)output.pc_delta;
    out_raw[35] = (uint64_t)output.status;

    CAMLreturn(Val_int(status));
}

CAMLprim value ocaml_harness_mem_copy_in(value v_src, value v_len) {
    CAMLparam2(v_src, v_len);
    harness_init();
    void *src = Caml_ba_data_val(v_src);
    size_t len = (size_t)Long_val(v_len);
    if (len > 0x10000) len = 0x10000;
    memcpy(g_scratch_mem, src, len);
    CAMLreturn(Val_unit);
}

CAMLprim value ocaml_harness_mem_copy_out(value v_dst, value v_len) {
    CAMLparam2(v_dst, v_len);
    harness_init();
    void *dst = Caml_ba_data_val(v_dst);
    size_t len = (size_t)Long_val(v_len);
    if (len > 0x10000) len = 0x10000;
    memcpy(dst, g_scratch_mem, len);
    CAMLreturn(Val_unit);
}

CAMLprim value ocaml_disasm(value v_insn) {
    CAMLparam1(v_insn);
    uint32_t insn = (uint32_t)Long_val(v_insn);

    char tmp_path[] = "/tmp/difftest_insn_XXXXXX";
    int fd = mkstemp(tmp_path);
    if (fd < 0) {
        CAMLreturn(caml_copy_string("disasm_error"));
    }
    write(fd, &insn, 4);
    close(fd);

    char cmd[256];
    snprintf(cmd, sizeof(cmd), "objdump -D -b binary -m aarch64 %s 2>/dev/null", tmp_path);
    FILE *fp = popen(cmd, "r");
    char result[256] = "unknown";
    if (fp) {
        char line[256];
        while (fgets(line, sizeof(line), fp)) {
            if (strstr(line, "0:")) {
                char *tab = strchr(line, '\t');
                if (tab) {
                    char *tab2 = strchr(tab + 1, '\t');
                    if (tab2) {
                        // instruction is after tab2
                        char *p = tab2 + 1;
                        size_t l = strlen(p);
                        while (l > 0 && (p[l-1] == '\n' || p[l-1] == '\r')) p[--l] = '\0';
                        strncpy(result, p, sizeof(result) - 1);
                        break;
                    }
                }
            }
        }
        pclose(fp);
    }
    unlink(tmp_path);
    CAMLreturn(caml_copy_string(result));
}
