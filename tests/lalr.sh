#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build
task_tmp=$(mktemp -d "$PWD/build/lalr.XXXXXX")
trap 'task_status=$?; if [ "$task_status" -eq 0 ]; then rm -rf "$task_tmp"; else printf "LALR logs retained: %s\n" "$task_tmp" >&2; fi' EXIT
generator=packages/parser/.lake/build/bin/lalrgen
packages/modelica-parser/.lake/build/bin/lalr-tests packages/modelica-parser/grammar/Modelica.ebnf
"$generator" packages/modelica-parser/grammar/Modelica.ebnf "$task_tmp/Modelica.lean"
"$generator" packages/modelica-parser/grammar/Modelica.ebnf "$task_tmp/Again.lean"
cmp "$task_tmp/Modelica.lean" "$task_tmp/Again.lean"
cat >> "$task_tmp/Modelica.lean" <<'LEAN'
#print axioms Parser.LALRGenerated.safety_checked
#print axioms Parser.LALRGenerated.execution_safe
#print axioms Parser.LALRGenerated.first_checked
#print axioms Parser.LALRGenerated.nullable_coverage
#print axioms Parser.LALRGenerated.lookahead_coverage
LEAN
lake env lean "$task_tmp/Modelica.lean" > "$task_tmp/modelica-audit.txt"
bash scripts/audit-lean.sh "$task_tmp/modelica-audit.txt"

# Readable recursive EBNF, emitted Lean tables, and kernel execution of those
# actual tables. This does not assert the missing universal completeness proof.
printf '%s\n' "s : '(' s ')' s | '';" > "$task_tmp/recursive.ebnf"
"$generator" "$task_tmp/recursive.ebnf" "$task_tmp/Recursive.lean"
cat >> "$task_tmp/Recursive.lean" <<'LEAN'
set_option maxRecDepth 10000 in
example : (Parser.LALR.parse Parser.LALRGenerated.grammar
    Parser.LALRGenerated.tables 100 [0, 0, 1, 1]).isOk = true := by decide +kernel
LEAN
cat >> "$task_tmp/Recursive.lean" <<'LEAN'
#print axioms Parser.LALRGenerated.safety_checked
#print axioms Parser.LALRGenerated.execution_safe
#print axioms Parser.LALRGenerated.first_checked
#print axioms Parser.LALRGenerated.nullable_coverage
#print axioms Parser.LALRGenerated.lookahead_coverage
LEAN
lake env lean "$task_tmp/Recursive.lean" > "$task_tmp/recursive-audit.txt"
bash scripts/audit-lean.sh "$task_tmp/recursive-audit.txt"

# The exact emitted table/edge constants participate in the certificate.
sed 's/some (.shift [0-9][0-9]*)/some (.shift 999)/' "$task_tmp/Recursive.lean" > "$task_tmp/BadShift.lean"
if lake env lean "$task_tmp/BadShift.lean" > "$task_tmp/bad-shift.log" 2>&1; then
  echo 'corrupted shift passed its structural certificate' >&2; exit 1
fi
rg -q 'Safety.validate' "$task_tmp/bad-shift.log"
sed 's/^def edges : List LALR.Edge := .*/def edges : List LALR.Edge := []/' \
  "$task_tmp/Recursive.lean" > "$task_tmp/MissingEdges.lean"
if lake env lean "$task_tmp/MissingEdges.lean" > "$task_tmp/missing-edges.log" 2>&1; then
  echo 'omitted transitions passed their structural certificate' >&2; exit 1
fi
rg -q 'Safety.validate' "$task_tmp/missing-edges.log"

# Facts are certified about the emitted grammar; stripping them cannot pass.
sed 's/^def firstFacts : Array LALR.First := .*/def firstFacts : Array LALR.First := #[]/' \
  "$task_tmp/Recursive.lean" > "$task_tmp/MissingFirst.lean"
if lake env lean "$task_tmp/MissingFirst.lean" > "$task_tmp/missing-first.log" 2>&1; then
  echo 'omitted nullable/FIRST facts passed their certificate' >&2; exit 1
fi
# cbv exposes the false certificate obligation before reporting its failure.
rg -q '^⊢ false = true$' "$task_tmp/missing-first.log"
rg -q 'first_checked.*sorryAx' "$task_tmp/missing-first.log"

# A conflict or undefined reference must not replace an existing output.
cp "$task_tmp/Recursive.lean" "$task_tmp/preserved.lean"
printf '%s\n' "s : s '+' s | 'id';" > "$task_tmp/conflict.ebnf"
if "$generator" "$task_tmp/conflict.ebnf" "$task_tmp/Recursive.lean" > "$task_tmp/conflict.log" 2>&1; then
  echo 'ambiguous grammar unexpectedly generated tables' >&2; exit 1
fi
rg -q 'LALR conflict in state' "$task_tmp/conflict.log"
cmp "$task_tmp/Recursive.lean" "$task_tmp/preserved.lean"
printf '%s\n' 's : undefined;' > "$task_tmp/undefined.ebnf"
if "$generator" "$task_tmp/undefined.ebnf" "$task_tmp/Recursive.lean" > "$task_tmp/undefined.log" 2>&1; then
  echo 'undefined grammar rule unexpectedly generated tables' >&2; exit 1
fi
rg -q 'undefined rule undefined' "$task_tmp/undefined.log"
cmp "$task_tmp/Recursive.lean" "$task_tmp/preserved.lean"
echo 'LALR safety/FIRST certificates, recursive execution, mutation and conflict checks passed'
