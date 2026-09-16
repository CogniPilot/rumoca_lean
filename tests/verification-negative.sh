#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
verified="$PWD/build/verified-lean"
task_tmp=$(mktemp -d "$PWD/build/verification-negative.XXXXXX")
trap 'task_status=$?; if [ "$task_status" -eq 0 ]; then rm -rf "$task_tmp"; else printf "Verification logs retained: %s\n" "$task_tmp" >&2; fi' EXIT

# No-build succeeds only when Lake can reuse the actual checked proof product.
lake run verify-artifact --check-only c "$verified/Source.mo" "$verified/Model.c" \
  packages/modelica-parser/grammar/Modelica.ebnf > "$task_tmp/cached.log"
bash scripts/audit-lean.sh "$task_tmp/cached.log"

# The kernel must reject altered actual output even if the native generator lies.
sed 's/1\.0/2.0/g' "$verified/Model.c" > "$task_tmp/Bad.c"
packages/compiler/.lake/build/bin/certify "$verified/Source.mo" "$task_tmp/Bad.c" "$task_tmp/Bad.lean"
if lake env lean "$task_tmp/Bad.lean" > "$task_tmp/lean.log" 2>&1; then
  echo 'mutated C passed the Lean artifact certificate' >&2; exit 1
fi
rg -q 'Tactic.*decide|evaluated to' "$task_tmp/lean.log"

# Mutate the same cached input path, then restore it. A failed verification
# cannot authorize new bytes or destroy the reusable proof for the old bytes.
cp "$verified/Model.c" "$task_tmp/Original.c"
cp "$task_tmp/Bad.c" "$verified/Model.c"
cache_status=0
lake run verify-artifact c "$verified/Source.mo" "$verified/Model.c" \
  packages/modelica-parser/grammar/Modelica.ebnf > "$task_tmp/cached-mutation.log" 2>&1 || cache_status=$?
cp "$task_tmp/Original.c" "$verified/Model.c"
test "$cache_status" -ne 0
rg -q 'actual numerical C differs' "$task_tmp/cached-mutation.log"
lake run verify-artifact --check-only c "$verified/Source.mo" "$verified/Model.c" \
  packages/modelica-parser/grammar/Modelica.ebnf > "$task_tmp/restored-cache.log"
bash scripts/audit-lean.sh "$task_tmp/restored-cache.log"

# Bypass the generator and corrupt the source embedded in a checked certificate.
sed 's/der(x) = 1/der(x) = 2/' "$verified/Candidate.lean" > "$task_tmp/BadSource.lean"
if lake env lean "$task_tmp/BadSource.lean" > "$task_tmp/source.log" 2>&1; then
  echo 'mutated Modelica source passed its certificate' >&2; exit 1
fi
rg -q 'error:' "$task_tmp/source.log"

# The audit must reject an additional assumption.
sed 's/propext/unapproved_axiom/' "$verified/lean-audit.log" > "$task_tmp/changed-audit.log"
if bash scripts/audit-lean.sh "$task_tmp/changed-audit.log" > "$task_tmp/audit.log" 2>&1; then
  echo 'an unapproved Lean assumption passed the axiom audit' >&2; exit 1
fi

printf 'model M_2\tReal y9;\nequation der(y9)=1;\r\nend M_2;\n' > "$task_tmp/Renamed.mo"
packages/compiler/.lake/build/bin/certify "$task_tmp/Renamed.mo" "$verified/Model.c" "$task_tmp/Renamed.lean"
lake env lean "$task_tmp/Renamed.lean" > "$task_tmp/renamed-lean.log" 2>&1
bash scripts/audit-lean.sh "$task_tmp/renamed-lean.log"

# The trusted adapter must fix its proposition from the ACTUAL files. Neither
# a trivial theorem nor a complete valid proof about a different C file may
# cause acceptance. These reproduce both review counterexamples end to end.
cat > "$task_tmp/fake-rumoca" <<'FAKE'
#!/usr/bin/env bash
cp "$RUMOCA_BAD_C" "$3"
FAKE
cat > "$task_tmp/trivial-certify" <<'FAKE'
#!/usr/bin/env bash
printf '#print axioms True.intro\n' > "$3"
FAKE
cat > "$task_tmp/seed-certify" <<'FAKE'
#!/usr/bin/env bash
"$RUMOCA_REAL_CERTIFY" "$1" "$RUMOCA_GOOD_C" "$3"
FAKE
chmod +x "$task_tmp/fake-rumoca" "$task_tmp/trivial-certify" "$task_tmp/seed-certify"
for producer in trivial-certify seed-certify; do
  if RUMOCA_COMPILER="$task_tmp/fake-rumoca" RUMOCA_CERTIFY="$task_tmp/$producer" \
      RUMOCA_BAD_C="$task_tmp/Bad.c" RUMOCA_GOOD_C="$verified/Model.c" \
      RUMOCA_REAL_CERTIFY="$PWD/packages/compiler/.lake/build/bin/certify" \
      bash scripts/verify-artifact.sh "$verified/Source.mo" "$task_tmp/$producer-output" \
      > "$task_tmp/$producer.log" 2>&1; then
    echo "forged producer $producer passed actual-file verification" >&2; exit 1
  fi
  test ! -e "$task_tmp/$producer-output/manifest.sha256"
  rg -q 'error:' "$task_tmp/$producer-output/lake-build.log"
done

sed 's/der(x) = 1/der(x) = 2/' "$verified/Source.mo" > "$task_tmp/Wrong.mo"
if RUMOCA_SOURCE="$task_tmp/Wrong.mo" RUMOCA_C="$verified/Model.c" \
    lake env lean packages/compiler/Tools/CheckArtifact.lean > "$task_tmp/wrong-source.log" 2>&1; then
  echo 'actual changed source passed the trusted checker' >&2; exit 1
fi
RUMOCA_SOURCE="$task_tmp/Renamed.mo" RUMOCA_C="$verified/Model.c" \
  lake env lean packages/compiler/Tools/CheckArtifact.lean > "$task_tmp/renamed-actual.log" 2>&1
bash scripts/audit-lean.sh "$task_tmp/renamed-actual.log"
sed "s/'1'/'2'/" packages/modelica-parser/grammar/Modelica.ebnf > "$task_tmp/Wrong.ebnf"
if cmp -s packages/modelica-parser/grammar/Modelica.ebnf "$task_tmp/Wrong.ebnf"; then
  echo 'grammar mutation did not change the actual grammar' >&2; exit 1
fi
if RUMOCA_SOURCE="$verified/Source.mo" RUMOCA_C="$verified/Model.c" \
    RUMOCA_GRAMMAR="$task_tmp/Wrong.ebnf" \
    lake env lean packages/compiler/Tools/CheckArtifact.lean > "$task_tmp/wrong-grammar.log" 2>&1; then
  echo 'actual changed EBNF passed the trusted checker' >&2; exit 1
fi
echo 'Actual-file binding, forged producers, mutation rejection controls passed'
