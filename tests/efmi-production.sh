#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build
# A stable stage path (with an embedded space to exercise path handling) keeps
# the source identity constant, so the archive certificate is reused across
# gate runs. Stale contents are cleared first so a previous run cannot satisfy a
# check vacuously; the certificate products under the compiler package stay.
stage="$PWD/build/efmi production"
rm -rf "$stage"
mkdir -p "$stage"
trap 'status=$?; if [ "$status" -eq 0 ]; then rm -rf "$stage"; else echo "Failure logs: $stage" >&2; fi' EXIT
compiler=packages/compiler/.lake/build/bin/rumoca
# Reproducible eFMU identities and generation time make the archive bytes
# stable across runs: version 5 name-based UUIDs and this fixed UTC instant.
export SOURCE_DATE_EPOCH=1700000000
cp examples/Integrator.mo "$stage/Source.mo"
archive="$stage/model.efmu"
"$compiler" "$stage/Source.mo" -o "$archive" > "$stage/checked.log"
bash scripts/audit-lean.sh "$stage/checked.log"
rg 'Rumoca.CheckedEFMIFiles.source_to_archive depends on axioms:' "$stage/checked.log"
# The published ZIP moved out of staging, but its checked bytes and source
# identity are unchanged. Require reuse of the native proof, not a fresh run.
lake run verify-artifact --check-only efmi-archive "$stage/Source.mo" "$archive" \
  packages/modelica-parser/grammar/Modelica.ebnf packages/galec-parser/grammar/GALEC.ebnf \
  > "$stage/cached-archive.log"
bash scripts/audit-lean.sh "$stage/cached-archive.log"
# The same bytes under another source identity are a different proposition:
# no-build reuse must fail rather than borrow the checked declarations.
if lake run verify-artifact --check-only efmi-archive "$stage/Source.mo" "$archive" \
    packages/modelica-parser/grammar/Modelica.ebnf packages/galec-parser/grammar/GALEC.ebnf \
    "$stage/Other.mo" > "$stage/foreign-identity.log" 2>&1; then
  echo "eFMU certificate reused under a different source identity" >&2; exit 1
fi
rg -q "out-of-date" "$stage/foreign-identity.log"
# Check the I/O boundary after archive preparation: a failed checker must not
# replace a published archive or leave a new destination or staging directory.
cp "$archive" "$stage/preserved.efmu"
mkdir "$stage/failing-tools"
cat > "$stage/failing-tools/lake" <<'SH'
#!/usr/bin/env bash
echo 'deliberate eFMU checker failure' >&2
exit 91
SH
chmod +x "$stage/failing-tools/lake"
for destination in "$archive" "$stage/unpublished.efmu"; do
  if PATH="$stage/failing-tools:$PATH" "$compiler" "$stage/Source.mo" -o "$destination" > "$stage/rejected-publication.log" 2>&1; then
    echo 'eFMU publication accepted a failed checker' >&2
    exit 1
  fi
  rg -q 'deliberate eFMU checker failure' "$stage/rejected-publication.log"
done
cmp "$archive" "$stage/preserved.efmu"
test ! -e "$stage/unpublished.efmu"
for leftover in "$stage"/.rumoca-efmu.*; do
  if [ -e "$leftover" ]; then
    echo 'failed eFMU publication left staging files' >&2
    exit 1
  fi
done
(cd packages/backend-efmi/vendor/efmi && sha256sum --quiet -c SHA256SUMS)
root="$stage/extracted"
python - "$archive" "$root" <<'PY'
from pathlib import Path
from hashlib import sha1
from datetime import datetime, timezone
from lxml import etree
from zipfile import ZipFile
from uuid import UUID
import os
import sys

stage = Path(sys.argv[2])
with ZipFile(sys.argv[1]) as archive:
    assert len(archive.namelist()) == 50
    assert len(set(archive.namelist())) == 50
    assert archive.testzip() is None
    archive.extractall(stage)
schemas = stage / 'schemas'
upstream = Path('packages/backend-efmi/vendor/efmi/schemas')
assert {p.relative_to(schemas) for p in schemas.rglob('*') if p.is_file()} == {
    p.relative_to(upstream) for p in upstream.rglob('*') if p.is_file()}
for path in schemas.rglob('*'):
    if path.is_file():
        assert path.read_bytes() == (upstream / path.relative_to(schemas)).read_bytes()
for name, schema in [
    ('AlgorithmCode/manifest.xml', 'AlgorithmCode/efmiAlgorithmCodeManifest.xsd'),
    ('ProductionCode/manifest.xml', 'ProductionCode/efmiProductionCodeManifest.xsd'),
    ('__content.xml', 'efmiContainerManifest.xsd'),
]:
    etree.XMLSchema(etree.parse(str(schemas / schema))).assertValid(etree.parse(str(stage / name)))
for name, member in [('AlgorithmCode/manifest.xml', 'AlgorithmCode/model.alg'), ('ProductionCode/manifest.xml', 'ProductionCode/production.c')]:
    root = etree.parse(str(stage / name))
    assert root.find("Files/File[@role='Code']").get('checksum') == sha1((stage / member).read_bytes()).hexdigest()
production = etree.parse(str(stage / 'ProductionCode/manifest.xml'))
algorithm = etree.parse(str(stage / 'AlgorithmCode/manifest.xml'))
error_anchor = algorithm.find('ErrorSignalStatus').get('id')
for function in production.findall('CodeContainer/CodeFiles/CodeFile/Functions/Function'):
    formal = function.find('FormalParameters/FormalParameter')
    mappings = production.xpath('//DataReference[ForeignVariableReference/@foreignRefId=$anchor '
        'and FormalParameter/@formalParameterRefId=$formal]',
        anchor=error_anchor, formal=formal.get('id'))
    assert len(mappings) == 1
    component = mappings[0].find('FormalParameter').get('componentIdentifier')
    fields = production.xpath('//Typedef[@id=$model]/Components/Component[@name=$field]',
        model=formal.get('typeDefRefId'), field=component)
    assert len(fields) == 1
    assert fields[0].get('typeDefRefId') == function.find('ReturnParameter').get('typeDefRefId')
assert production.find('ManifestReferences/ManifestReference').get('checksum') == sha1((stage / 'AlgorithmCode/manifest.xml').read_bytes()).hexdigest()
content = etree.parse(str(stage / '__content.xml'))
roots = [etree.parse(str(stage / name)).getroot() for name in [
    '__content.xml', 'AlgorithmCode/manifest.xml', 'ProductionCode/manifest.xml']]
identities = [UUID(root.get('id')) for root in roots]
assert len(set(identities)) == 3
# Reproducible compile under SOURCE_DATE_EPOCH: version 5 name-based identities
# and the generation time fixed to that epoch.
assert all(identity.version == 5 for identity in identities)
times = {root.get('generationDateAndTime') for root in roots}
assert len(times) == 1
generated = datetime.fromisoformat(times.pop())
assert generated.tzinfo == timezone.utc
assert generated == datetime.fromtimestamp(int(os.environ["SOURCE_DATE_EPOCH"]), tz=timezone.utc)
for rep, name in zip(content.findall('ModelRepresentation'), ['AlgorithmCode/manifest.xml', 'ProductionCode/manifest.xml'], strict=True):
    assert rep.get('checksum') == sha1((stage / name).read_bytes()).hexdigest()
PY
algorithm="$root/AlgorithmCode/model.alg"
production="$root/ProductionCode/production.c"
production_xml="$root/ProductionCode/manifest.xml"
check_files() {
  "$compiler" verify-efmi "$root" --source "$stage/Source.mo"
}
# Exercise the archive file adapter's two independent boundaries: extra bytes,
# and changed pinned content with correct ZIP CRCs and an unchanged XML graph.
python - "$archive" "$stage" <<'PY'
from pathlib import Path
from zipfile import ZipFile
from struct import unpack_from, pack_into
from zlib import crc32
import sys

path, stage = Path(sys.argv[1]), Path(sys.argv[2])
original = path.read_bytes()
(stage / 'trailing.efmu').write_bytes(original + b'unchecked')
changed = bytearray(original)
with ZipFile(path) as archive:
    member = archive.getinfo('schemas/AlgorithmCode/VERSION.txt')
    name_size, extra_size = unpack_from('<HH', changed, member.header_offset + 26)
    start = member.header_offset + 30 + name_size + extra_size
    changed[start] ^= 1
    checksum = crc32(changed[start:start + member.file_size])
    pack_into('<I', changed, member.header_offset + 14, checksum)
    position = unpack_from('<I', original, len(original) - 6)[0]
    for info in archive.infolist():
        assert changed[position:position+4] == b'PK\x01\x02'
        n, x, c = unpack_from('<HHH', changed, position + 28)
        if info.filename == member.filename:
            pack_into('<I', changed, position + 16, checksum)
        position += 46 + n + x + c
(stage / 'changed-schema.efmu').write_bytes(changed)
with ZipFile(stage / 'changed-schema.efmu') as archive:
    assert archive.testzip() is None
PY
for mutation in trailing changed-schema; do
  if "$compiler" verify-efmi "$stage/$mutation.efmu" --source "$stage/Source.mo" > "$stage/rejected-$mutation.log" 2>&1; then
    echo "accepted altered archive: $mutation" >&2
    exit 1
  fi
done
rg -q 'unsupported or inconsistent ZIP header' "$stage/rejected-trailing.log"
rg -q 'archive schema resource differs from the pinned release' "$stage/rejected-changed-schema.log"
gcc -std=c11 -O2 -Wall -Wextra -Werror -pedantic -fno-fast-math -ffp-contract=off \
  -frounding-math -I "$root/ProductionCode" packages/backend-efmi/Tests/production-driver.c -lm -o "$stage/driver"
"$stage/driver"
# A source rename preserves this tiny model's generated GALEC and C bytes.
# Its old XML/checksum graph must nevertheless fail the source-name contract.
cp "$stage/Source.mo" "$stage/original.mo"
sed 's/model Integrator/model RenamedIntegrator/; s/end Integrator/end RenamedIntegrator/' \
  "$stage/original.mo" > "$stage/Source.mo"
if cmp -s "$stage/original.mo" "$stage/Source.mo"; then
  echo 'ineffective source-name mutation' >&2
  exit 1
fi
if check_files > "$stage/rejected-source-name.log" 2>&1; then
  echo 'accepted manifests for a different source model name' >&2
  exit 1
fi
rg -q 'actual manifest differs from the correlated code products' "$stage/rejected-source-name.log"
cp "$stage/original.mo" "$stage/Source.mo"
cp "$production_xml" "$stage/original.xml"
cp "$root/AlgorithmCode/manifest.xml" "$stage/original-algorithm.xml"
cp "$root/__content.xml" "$stage/original-content.xml"
# Preserve the checksum graph while making the shared calendar date invalid.
# This exercises the trusted file adapter, beyond ordinary XML/mapping drift.
python - "$root" <<'PY'
from pathlib import Path
from hashlib import sha1
import re
import sys

root = Path(sys.argv[1])
paths = [root / name for name in ['AlgorithmCode/manifest.xml', 'ProductionCode/manifest.xml', '__content.xml']]
original = [path.read_bytes() for path in paths]
changed = [re.sub(rb'generationDateAndTime="[^"]+"',
                  b'generationDateAndTime="1900-02-29T18:00:00Z"', data) for data in original]
assert all(before != after for before, after in zip(original, changed, strict=True))
changed[1] = changed[1].replace(sha1(original[0]).hexdigest().encode(), sha1(changed[0]).hexdigest().encode())
for index in [0, 1]:
    changed[2] = changed[2].replace(sha1(original[index]).hexdigest().encode(), sha1(changed[index]).hexdigest().encode())
for path, data in zip(paths, changed, strict=True):
    path.write_bytes(data)
PY
if check_files > "$stage/rejected-identity.log" 2>&1; then
  echo 'accepted correlated manifests with an invalid calendar date' >&2
  exit 1
fi
rg -q 'invalid eFMI manifest UUIDs or UTC generation timestamp' "$stage/rejected-identity.log"
cp "$stage/original-algorithm.xml" "$root/AlgorithmCode/manifest.xml"
cp "$stage/original.xml" "$production_xml"
cp "$stage/original-content.xml" "$root/__content.xml"
for field in x errorSignalStatus; do
  sed "s/componentIdentifier=\"$field\"/componentIdentifier=\"samplePeriod\"/" "$stage/original.xml" > "$production_xml"
  if cmp -s "$stage/original.xml" "$production_xml"; then
    echo "ineffective manifest mapping mutation: $field" >&2
    exit 1
  fi
  if check_files > "$stage/rejected-xml-$field.log" 2>&1; then
    echo "accepted manifest with changed logical mapping: $field" >&2
    exit 1
  fi
done
cp "$stage/original.xml" "$production_xml"
cp "$production" "$stage/original.c"
cp "$algorithm" "$stage/original.alg"

reject() {
  if cmp -s "$stage/original.c" "$production" && cmp -s "$stage/original.alg" "$algorithm"; then
    echo "ineffective Production C mutation: $1" >&2
    exit 1
  fi
  if check_files > "$stage/rejected.log" 2>&1; then
    echo "accepted mutated Production C pair: $1" >&2
    exit 1
  fi
}

sed 's/((self->x) + v0)/((self->samplePeriod) + v0)/' "$stage/original.c" > "$production"
reject state-reference
sed 's/double v1 = ((double)1)/double v1 = ((double)0)/' "$stage/original.c" > "$production"
reject clock-initialization
sed 's/(self->x) = v1/(self->samplePeriod) = v1/' "$stage/original.c" > "$production"
reject write-target
cp "$stage/original.c" "$production"
printf '\nvoid injected(void) {}\n' >> "$production"
reject extra-function
cp "$stage/original.c" "$production"
sed 's/+ 1.0/+ 0.0/' "$stage/original.alg" > "$algorithm"
reject mismatched-algorithm
cp "$archive" build/Integrator.efmu
cp "$stage/checked.log" build/efmi-publication-artifact.log
sha256sum build/Integrator.efmu
echo 'eFMU: checked CLI publication, failure preservation, independent extraction, official schemas/checksums, native C and mutation controls passed'

# --- Tensor eFMU: checked CLI publication, reuse, schemas and mutation control ---
# The default CLI admits the fixed TensorSquare array profile to complete tensor
# eFMU output through EFMIExport.writeTensorArchive, gated by the fixed
# tensor-efmi-archive certificate (Rumoca.CheckedTensorEFMIFiles.source_to_archive).
# This certificate peaks at parity with the scalar eFMU archive certificate above,
# dominated by the composed manifest and stored-ZIP payload over all members; it is
# not cheaper. SOURCE_DATE_EPOCH is already exported, and the tensor source identity
# is fixed, so the certificate is reused across this script and tests/tensor-c.sh.
tstage="$PWD/build/efmi tensor"
rm -rf "$tstage"; mkdir -p "$tstage"
tarchive="$tstage/model.efmu"
"$compiler" examples/development/TensorSquare.mo -o "$tarchive" > "$tstage/checked.log"
bash scripts/audit-lean.sh "$tstage/checked.log"
rg 'Rumoca.CheckedTensorEFMIFiles.source_to_archive depends on axioms:' "$tstage/checked.log"
# The published ZIP moved out of staging; require reuse of the native proof.
lake run verify-artifact --check-only tensor-efmi-archive examples/development/TensorSquare.mo "$tarchive" \
  packages/modelica-parser/grammar/Modelica.ebnf packages/galec-parser/grammar/GALEC.ebnf \
  > "$tstage/cached-archive.log"
bash scripts/audit-lean.sh "$tstage/cached-archive.log"
(cd packages/backend-efmi/vendor/efmi && sha256sum --quiet -c SHA256SUMS)
troot="$tstage/extracted"
python - "$tarchive" "$troot" <<'PY'
from pathlib import Path
from hashlib import sha1
from lxml import etree
from zipfile import ZipFile
import sys
stage = Path(sys.argv[2])
with ZipFile(sys.argv[1]) as archive:
    assert len(archive.namelist()) == 50
    assert len(set(archive.namelist())) == 50
    assert archive.testzip() is None
    archive.extractall(stage)
schemas = stage / 'schemas'
upstream = Path('packages/backend-efmi/vendor/efmi/schemas')
assert {p.relative_to(schemas) for p in schemas.rglob('*') if p.is_file()} == {
    p.relative_to(upstream) for p in upstream.rglob('*') if p.is_file()}
for path in schemas.rglob('*'):
    if path.is_file():
        assert path.read_bytes() == (upstream / path.relative_to(schemas)).read_bytes()
for name, schema in [
    ('AlgorithmCode/manifest.xml', 'AlgorithmCode/efmiAlgorithmCodeManifest.xsd'),
    ('ProductionCode/manifest.xml', 'ProductionCode/efmiProductionCodeManifest.xsd'),
    ('__content.xml', 'efmiContainerManifest.xsd'),
]:
    etree.XMLSchema(etree.parse(str(schemas / schema))).assertValid(etree.parse(str(stage / name)))
algorithm = etree.parse(str(stage / 'AlgorithmCode/manifest.xml'))
production = etree.parse(str(stage / 'ProductionCode/manifest.xml'))
assert algorithm.find("Files/File[@role='Code']").get('checksum') == \
    sha1((stage / 'AlgorithmCode/model.alg').read_bytes()).hexdigest()
assert production.find("Files/File[@role='Code']").get('checksum') == \
    sha1((stage / 'ProductionCode/production.c').read_bytes()).hexdigest()
assert production.find('ManifestReferences/ManifestReference').get('checksum') == \
    sha1((stage / 'AlgorithmCode/manifest.xml').read_bytes()).hexdigest()
dims = {v.get('name'): [d.get('size') for d in v.findall('Dimensions/Dimension')]
        for v in algorithm.findall('Variables/RealVariable')}
assert dims['u'] == ['2'] and dims['x'] == ['2'] and dims['J'] == ['2', '2'], dims
print('tensor eFMU: 50 members, schemas match, XSD-valid, checksums correlated, array dimensions declared')
PY
# One Production C mutation control: the extracted directory with a mutated
# Production C must be rejected by the tensor directory checker (before any kernel
# certificate work) and must not certify.
tmut="$tstage/mutant"
rm -rf "$tmut"; mkdir -p "$tmut/AlgorithmCode" "$tmut/ProductionCode"
cp "$troot/AlgorithmCode/model.alg" "$tmut/AlgorithmCode/model.alg"
cp "$troot/AlgorithmCode/manifest.xml" "$tmut/AlgorithmCode/manifest.xml"
cp "$troot/ProductionCode/manifest.xml" "$tmut/ProductionCode/manifest.xml"
cp "$troot/__content.xml" "$tmut/__content.xml"
sed 's/rumoca_tensor_mul(u, u/rumoca_tensor_add(u, u/' \
  "$troot/ProductionCode/production.c" > "$tmut/ProductionCode/production.c"
if cmp -s "$troot/ProductionCode/production.c" "$tmut/ProductionCode/production.c"; then
  echo 'ineffective tensor Production C mutation' >&2; exit 1
fi
if lake run verify-artifact tensor-efmi-directory examples/development/TensorSquare.mo "$tmut" \
    packages/modelica-parser/grammar/Modelica.ebnf packages/galec-parser/grammar/GALEC.ebnf \
    > "$tstage/rejected-production.log" 2>&1; then
  echo 'accepted mutated tensor Production C' >&2; exit 1
fi
rg -q 'actual tensor Production C differs from the certified translation unit' "$tstage/rejected-production.log"
cp "$tarchive" build/TensorSquare.efmu
sha256sum build/TensorSquare.efmu
rm -rf "$tstage"
echo 'Tensor eFMU: checked CLI publication, certificate reuse, official schemas/checksums, array dimensions and Production C mutation control passed'
