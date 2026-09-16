#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source_path=${1:-examples/Integrator.mo}
artifact_dir=${2:-build/verified-lean}
mkdir -p "$artifact_dir"
artifact_dir=$(realpath "$artifact_dir")
rm -f "$artifact_dir/manifest.sha256"
cp "$source_path" "$artifact_dir/Source.mo"
# Both producers are untrusted. Overrides support fault-injection regressions.
"${RUMOCA_COMPILER:-packages/compiler/.lake/build/bin/rumoca}" "$artifact_dir/Source.mo" -o "$artifact_dir/Model.c"
"${RUMOCA_CERTIFY:-packages/compiler/.lake/build/bin/certify}" "$artifact_dir/Source.mo" "$artifact_dir/Model.c" "$artifact_dir/Candidate.lean"
cp packages/compiler/Tools/CheckArtifact.lean "$artifact_dir/Artifact.lean"
if ! lake run verify-artifact c "$artifact_dir/Source.mo" "$artifact_dir/Model.c" \
    "${RUMOCA_GRAMMAR:-packages/modelica-parser/grammar/Modelica.ebnf}" \
    > "$artifact_dir/lean-audit.log" 2> "$artifact_dir/lake-build.log"; then
  cat "$artifact_dir/lake-build.log" >&2
  exit 1
fi
bash scripts/audit-lean.sh "$artifact_dir/lean-audit.log"
sha256sum "$artifact_dir/Source.mo" "$artifact_dir/Model.c" \
  "$artifact_dir/Artifact.lean" lean-toolchain lake-manifest.json \
  "$artifact_dir/Candidate.lean" \
  packages/compiler/Tools/CheckArtifact.lean packages/compiler/Rumoca/ArtifactCheck.lean "${RUMOCA_GRAMMAR:-packages/modelica-parser/grammar/Modelica.ebnf}" \
  > "$artifact_dir/manifest.sha256"
echo "Lean source, C syntax, execution and rounding certificate passed: $artifact_dir"
