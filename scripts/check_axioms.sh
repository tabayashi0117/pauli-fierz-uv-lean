#!/usr/bin/env bash
# Build the library, check the sources for forbidden keywords, and verify that every declaration
# depends only on the standard axioms [propext, Classical.choice, Quot.sound].
set -euo pipefail
cd "$(dirname "$0")/.."

lake build

# 1. No `sorry`, `admit`, `native_decide` and no `axiom` declarations in the sources.
if grep -rnwE 'sorry|admit|native_decide' PauliFierzUV --include='*.lean' \
     | grep -v '^PauliFierzUV/Axioms.lean:'; then
  echo "error: forbidden keyword found (see above)" >&2
  exit 1
fi
if grep -rnE '^[[:space:]]*(private[[:space:]]+)?axiom[[:space:]]' PauliFierzUV --include='*.lean'; then
  echo "error: axiom declaration found (see above)" >&2
  exit 1
fi

# 2. #print axioms for every theorem, and a programmatic check of all declarations
#    (PauliFierzUV/Axioms.lean raises an error on any non-standard axiom).
out=$(lake env lean PauliFierzUV/Axioms.lean 2>&1) || { echo "$out" >&2; exit 1; }
echo "$out" | grep "depends on axioms" | sed 's/.*depends on axioms: //' | sort | uniq -c
if echo "$out" | grep "depends on axioms" \
     | grep -vq "depends on axioms: \[propext, Classical.choice, Quot.sound\]"; then
  echo "$out" >&2
  echo "error: unexpected axioms" >&2
  exit 1
fi
echo "$out" | grep "^OK:\|OK:"
