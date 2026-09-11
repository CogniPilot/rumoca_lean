#!/usr/bin/env python3
"""Native Task + filesystem + CLI boundary; semantic equivalence is a theorem."""
import json
import resource
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "packages/compiler/.lake/build/bin/rumoca"
# Bound the inherited native stack for the resource regression below. This
# checks the host execution boundary; semantic equivalence is proved in Lean.
_, stack_hard = resource.getrlimit(resource.RLIMIT_STACK)
stack_limit = 8 * 1024 * 1024
if stack_hard != resource.RLIM_INFINITY:
    stack_limit = min(stack_limit, stack_hard)
resource.setrlimit(resource.RLIMIT_STACK, (stack_limit, stack_hard))
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
(ROOT / "build").mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix="parallel parsing α ", dir=ROOT / "build") as folder:
    directory = Path(folder)
    files = []
    for index in range(1000):
        path = directory / f"Model{index}.mo"
        path.write_text(f"model Model{index}\n Real x;\nequation der(x) = 1; end Model{index};\n")
        files.append(str(path))
    wrong = directory / "Wrong.mo"
    wrong.write_text("model Wrong Real x; equation der(y) = 1; end Wrong;")
    malformed = directory / "Malformed.mo"
    malformed.write_text("model Malformed Real x;")
    long_tokens = directory / "LongTokens.mo"
    unit = "model LongTokens Real x; equation der(x) = 1; end LongTokens;\n"
    long_tokens.write_text(unit + ";" * 65536)
    files += [str(wrong), str(malformed), str(directory / "Missing.mo"), str(long_tokens), files[17]]
    outputs = []
    for jobs in (1, 4):
        start = time.perf_counter()
        run = subprocess.run([str(COMPILER), "parse", "--jobs", str(jobs), "--json", *files],
                             capture_output=True, text=True, timeout=60)
        assert run.returncode == 1 and run.stderr == "", (run.returncode, run.stderr)
        outputs.append(json.loads(run.stdout))
        print(f"{len(files)} inputs, jobs={jobs}: {time.perf_counter() - start:.3f}s (includes sequential file reads)")
    assert outputs[0] == outputs[1], "parallel output differs from sequential output"
    results = outputs[1]
    assert [r["path"] for r in results] == files
    assert all(r["ok"] and r["model"] == f"Model{i}" for i, r in enumerate(results[:1000]))
    assert [r["diagnostics"][0]["phase"] for r in results[1000:1003]] == ["resolve", "parse", "io"]
    # The old recursive attachment aborted before reporting this first extra
    # token. Keep one native resource case in the existing multi-file check.
    long_error = results[1003]["diagnostics"][0]
    assert not results[1003]["ok"] and long_error["phase"] == "parse"
    assert (long_error["span"]["startByte"], long_error["span"]["endByte"]) == (len(unit), len(unit) + 1)
    assert results[-1]["ok"] and results[-1]["model"] == "Model17"
    failure = results[1000]["diagnostics"][0]
    assert wrong.read_bytes()[failure["span"]["startByte"]:failure["span"]["endByte"]] == b"y"
    note, = failure["related"]
    assert note["message"] == "state declared here"
    assert wrong.read_bytes()[note["span"]["startByte"]:note["span"]["endByte"]] == b"x"
    pretty = subprocess.run([str(COMPILER), str(wrong)], capture_output=True, text=True)
    parsed_pretty = subprocess.run([str(COMPILER), "parse", str(wrong)], capture_output=True, text=True)
    assert pretty.returncode == parsed_pretty.returncode == 1
    assert pretty.stdout == parsed_pretty.stdout == ""
    assert pretty.stderr == parsed_pretty.stderr
    assert "error[resolve]:" in pretty.stderr and "1 | model Wrong" in pretty.stderr and "^" in pretty.stderr
    assert "note: state declared here" in pretty.stderr
    invalid = subprocess.run([str(COMPILER), "parse", "--jobs", "0", files[0]], capture_output=True)
    assert invalid.returncode != 0 and b"must be positive" in invalid.stderr
print("Parallel parsing preserves native results, paths, ranges, duplicates and failure order")
