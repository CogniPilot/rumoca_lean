#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build
task_tmp=$(mktemp -d "$PWD/build/efmi-algorithm.XXXXXX")
trap 'task_status=$?; if [ "$task_status" -eq 0 ]; then rm -rf "$task_tmp"; else printf "eFMI logs retained: %s\n" "$task_tmp" >&2; fi' EXIT
# The positive certificate inputs live at a stable path so the actual-file
# certificate is reused across gate runs. Stale contents are removed first so a
# previous run's bytes cannot make a check pass vacuously; the .lake certificate
# products live under the compiler package and are never touched here.
stage="$PWD/build/efmi-algorithm"
rm -rf "$stage"
mkdir -p "$stage"
generator=packages/parser/.lake/build/bin/lalrgen
compiler=packages/compiler/.lake/build/bin/rumoca

"$generator" --namespace Rumoca.GALEC.Generated packages/galec-parser/grammar/GALEC.ebnf "$task_tmp/GALEC.lean"
cmp "$task_tmp/GALEC.lean" packages/galec-parser/GALECParser/Generated.lean
lake env lean --run packages/galec-parser/Tests/GALECNative.lean

# Both grammar instances use the same engine, without colliding declarations.
printf '%s\n' "s : '(' s ')' s | '';" > "$task_tmp/other.ebnf"
"$generator" --namespace AnotherGrammar "$task_tmp/other.ebnf" "$task_tmp/Other.lean"
sed -i '1i import GALECParser.Generated' "$task_tmp/Other.lean"
lake env lean "$task_tmp/Other.lean"
cp "$task_tmp/Other.lean" "$task_tmp/preserved.lean"
if "$generator" --namespace 'Bad; end' "$task_tmp/other.ebnf" "$task_tmp/Other.lean" > "$task_tmp/namespace.log" 2>&1; then
  echo 'invalid namespace accepted' >&2; exit 1
fi
rg -q 'namespace' "$task_tmp/namespace.log"
cmp "$task_tmp/Other.lean" "$task_tmp/preserved.lean"

"$compiler" examples/Integrator.mo -o "$stage/model.alg" > "$task_tmp/export.log"
cmp "$stage/model.alg" examples/UnitIntegrator.alg
cp examples/Integrator.mo "$stage/Source.mo"
cp packages/modelica-parser/grammar/Modelica.ebnf "$stage/Modelica.ebnf"
cp packages/galec-parser/grammar/GALEC.ebnf "$stage/GALEC.ebnf"
check_files() {
  "$compiler" verify-algorithm "$stage/model.alg" --source "$stage/Source.mo" \
    --grammar "$stage/Modelica.ebnf" --galec-grammar "$stage/GALEC.ebnf"
}
check_files > "$task_tmp/actual-audit.txt"
bash scripts/audit-lean.sh "$task_tmp/actual-audit.txt"
reject_files() {
  if check_files > "$task_tmp/$1.log" 2>&1; then
    printf 'actual-file mutation accepted: %s\n' "$1" >&2; exit 1
  fi
}
sed -i 's/+ 1.0/+ 2.0/' "$stage/model.alg"
reject_files arithmetic
cp examples/UnitIntegrator.alg "$stage/model.alg"
sed -i 's/samplePeriod := 1.0/samplePeriod := 0.0/' "$stage/model.alg"
reject_files period
cp examples/UnitIntegrator.alg "$stage/model.alg"
sed -i 's/der(x) = 1/der(x) = 2/' "$stage/Source.mo"
reject_files source
cp examples/Integrator.mo "$stage/Source.mo"
printf '\n(* changed actual grammar *)\n' >> "$stage/GALEC.ebnf"
reject_files galec-grammar
cp packages/galec-parser/grammar/GALEC.ebnf "$stage/GALEC.ebnf"
printf '\n(* changed actual grammar *)\n' >> "$stage/Modelica.ebnf"
reject_files modelica-grammar
cp packages/modelica-parser/grammar/Modelica.ebnf "$stage/Modelica.ebnf"

# Failed compilation cannot replace an earlier published Algorithm Code member.
cp "$stage/model.alg" "$task_tmp/preserved.alg"
printf '%s\n' 'invalid Modelica' > "$task_tmp/invalid.mo"
if "$compiler" "$task_tmp/invalid.mo" -o "$stage/model.alg" > "$task_tmp/rejected-source.log" 2>&1; then
  echo 'invalid source unexpectedly published Algorithm Code' >&2; exit 1
fi
cmp "$stage/model.alg" "$task_tmp/preserved.alg"
echo 'GALEC EBNF freshness, reuse, actual-file certificate and mutation checks passed'
