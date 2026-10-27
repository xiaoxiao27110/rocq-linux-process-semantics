#!/bin/bash
set -e

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORKSPACE="$(cd "$DIR/.." && pwd)"

echo "============================================================"
echo "ARM64 Coq Model vs Apple M4 Differential Testing"
echo "============================================================"

if [ -f /.dockerenv ]; then
  # Running inside container
  cd /workspace/difftest

  echo "[1/4] Extracting ARM64 model from Coq to OCaml..."
  coqc -Q /workspace/references/rocq-linux-process-semantics/compat/Stdlib Stdlib \
       -Q /workspace/references/rocq-linux-process-semantics/compat/stdpp/bitvector stdpp.bitvector \
       -Q /workspace/references/rocq-linux-process-semantics/theories LinuxProcessSemantics \
       Extract.v

  echo "[2/4] Compiling extracted model (arm64_model)..."
  ocamlfind ocamlopt -package zarith -c arm64_model.mli arm64_model.ml

  echo "[3/4] Compiling native hardware harness (harness.c)..."
  gcc -c -O2 -I$(ocamlfind printconf stdlib) harness.c -o harness.o

  echo "[4/4] Compiling and linking differential tester..."
  ocamlfind ocamlopt -linkpkg -package zarith,bigarray harness.o arm64_model.cmx difftest.ml -o difftest_runner

  echo "============================================================"
  echo "Executing Differential Test Suite (>250,000 cases)..."
  echo "============================================================"
  ./difftest_runner

else
  # Running on macOS host
  echo "Target container: aegis-arm64-env"

  echo "[Host] Syncing difftest files to container..."
  docker exec aegis-arm64-env mkdir -p /workspace/difftest
  docker cp "$DIR/Extract.v" aegis-arm64-env:/workspace/difftest/Extract.v
  docker cp "$DIR/harness.c" aegis-arm64-env:/workspace/difftest/harness.c
  docker cp "$DIR/difftest.ml" aegis-arm64-env:/workspace/difftest/difftest.ml
  docker cp "$DIR/run.sh" aegis-arm64-env:/workspace/difftest/run.sh
  docker exec aegis-arm64-env chmod +x /workspace/difftest/run.sh

  echo "[Host] Running differential tester inside container..."
  docker exec aegis-arm64-env bash -c "/workspace/difftest/run.sh"

  echo "[Host] Retrieving REPORT.md..."
  docker cp aegis-arm64-env:/workspace/difftest/REPORT.md "$DIR/REPORT.md"

  echo "============================================================"
  echo "Differential Testing Finished Successfully!"
  echo "Report saved to: $DIR/REPORT.md"
  echo "============================================================"
fi
