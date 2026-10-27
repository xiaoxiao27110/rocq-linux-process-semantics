#!/bin/bash
# Rebuild the tinyxml2/xmltest chain (Core -> images -> Images/Distribution/Statements -> Arm64Verify)
# against the current LinuxProcessSemantics build. Runs inside aegis-arm64-env.
set -euo pipefail
LPS=/workspace/references/rocq-linux-process-semantics
OVP=/workspace/references/oss-verify-proofs
Q="-Q $LPS/compat/Stdlib Stdlib -Q $LPS/compat/stdpp/bitvector stdpp.bitvector -Q $LPS/theories LinuxProcessSemantics -Q $OVP/theories OssFuzzTheorems.Core -Q $OVP/projects/tinyxml2 OssFuzzTheorems.tinyxml2"
cd "$OVP"
for f in theories/Images.v theories/Shapes.v theories/Driver.v \
         projects/tinyxml2/xmltest/images/Plain.v projects/tinyxml2/xmltest/images/Ubsan.v \
         projects/tinyxml2/xmltest/images/Asan.v projects/tinyxml2/xmltest/images/AsanUbsan.v \
         projects/tinyxml2/xmltest/Images.v projects/tinyxml2/xmltest/Distribution.v \
         projects/tinyxml2/xmltest/Statements.v projects/tinyxml2/xmltest/Characterise.v \
         projects/tinyxml2/xmltest/Arm64Verify.v; do
  echo "COQC $f"; s=$(date +%s)
  coqc $Q "$f" > /tmp/coqc_out.txt 2>&1 || { cat /tmp/coqc_out.txt; exit 1; }
  echo "  ok ($(( $(date +%s) - s ))s)"
done
tail -40 /tmp/coqc_out.txt
