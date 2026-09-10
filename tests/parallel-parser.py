#!/usr/bin/env python3
"""Native Task + filesystem + CLI boundary; semantic equivalence is a theorem."""
import json
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "packages/compiler/.lake/build/bin/rumoca"
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
    files += [str(wrong), str(malformed), str(directory / "Missing.mo"), files[17]]
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
