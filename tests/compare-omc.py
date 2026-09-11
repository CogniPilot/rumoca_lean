#!/usr/bin/env python3
"""Compare actual Rumoca ME/CS FMUs with OpenModelica on the admitted unit core.

External integration evidence, not a semantic proof. Run via lake run compare-omc
inside nix develop .#comparison. Each invocation keeps fresh sources, artifacts,
commands, logs and traces under build/omc-comparison; no cached success stamps.
"""

import argparse
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
import time
from xml.etree import ElementTree as ET
from zipfile import BadZipFile, ZipFile


ROOT = Path(__file__).resolve().parents[1]
ATOL = RTOL = 1e-12


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, allow_nan=False) + "\n")


def executable(value):
    path = shutil.which(str(value))
    if path is None:
        raise ValueError(f"Cannot find {value}; enter nix develop .#comparison")
    return str(Path(path).absolute())


def run(command, directory, label, timeout, phases, *, cwd=None):
    """Keep failed command evidence and kill descendants on timeout (POSIX)."""
    command = list(map(str, command))
    cwd = directory if cwd is None else cwd
    phase = {"name": label, "command": command, "cwd": str(cwd)}
    phases.append(phase)
    started = time.perf_counter()
    with (directory / f"{label}.stdout").open("wb") as stdout, \
            (directory / f"{label}.stderr").open("wb") as stderr:
        process = subprocess.Popen(command, cwd=cwd, stdout=stdout,
                                   stderr=stderr, start_new_session=True)
        try:
            code = process.wait(timeout=timeout)
        except BaseException as e:
            # Also reap descendants if the user interrupts the comparison.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
            phase.update(timed_out=isinstance(e, subprocess.TimeoutExpired), exit_code=process.returncode,
                         wall_s=time.perf_counter() - started)
            if isinstance(e, subprocess.TimeoutExpired):
                raise ValueError(f"{label} timed out after {timeout}s; see {directory}") from e
            raise
    phase.update(exit_code=code, wall_s=time.perf_counter() - started)
    if code != 0:
        raise ValueError(f"{label} exited {code}; see {directory / (label + '.stderr')}")
    return (directory / f"{label}.stdout").read_text(errors="replace")


def model_identity(fmu, source):
    # Ask the actual compiler product for names; do not implement a second
    # Modelica parser here. Require exact archived source bytes as well.
    with ZipFile(fmu) as archive:
        if archive.read("extra/org.cognipilot.rumoca/Source.mo") != source.read_bytes():
            raise ValueError("FMU archived source differs from comparison source")
        root = ET.fromstring(archive.read("modelDescription.xml"))
    if root.get("fmiVersion") != "3.0" or any(root.find(tag) is None for tag in
                                              ["ModelExchange", "CoSimulation"]):
        raise ValueError("Comparison requires a combined FMI 3 ME/CS artifact")
    variables = {v.get("valueReference"): v for v in root.findall("ModelVariables/Float64")}
    derivatives = root.findall("ModelStructure/ContinuousStateDerivative")
    if len(derivatives) != 1:
        raise ValueError("Comparison currently supports exactly one continuous state")
    derivative = variables[derivatives[0].get("valueReference")]
    state = variables[derivative.attrib["derivative"]].attrib["name"]
    model = root.attrib["modelName"]
    for name in [model, state]:
        if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", name) is None:
            raise ValueError(f"Comparison requires a simple identifier: {name!r}")
    return model, state


def trace(path, variable, steps, initial):
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream)
        fields = reader.fieldnames or []
        if len(fields) != len(set(fields)) or not {"time", variable} <= set(fields):
            raise ValueError(f"{path}: missing or duplicate CSV columns")
        rows = []
        for row in reader:
            if None in row or any(v is None for v in row.values()):
                raise ValueError(f"{path}: malformed CSV row")
            pair = (float(row["time"]), float(row[variable]))
            if not all(math.isfinite(v) for v in pair):
                raise ValueError(f"{path}: non-finite sample")
            rows.append(pair)
    # No interpolation, event deduplication, overlap truncation or extrapolation.
    # Strict integer times are part of this comparison's current unit profile.
    if [t for t, _ in rows] != list(range(steps + 1)):
        raise ValueError(f"{path}: expected exactly times 0..{steps} at unit intervals")
    if rows[0][1] != initial:
        raise ValueError(f"{path}: first state {rows[0][1]} differs from requested {initial}")
    return [x for _, x in rows]


def deviation(reference, actual):
    errors = [abs(a - b) for a, b in zip(reference, actual, strict=True)]
    if not all(math.isfinite(e) for e in errors):
        return {"passed": False, "error": "absolute difference overflowed binary64"}
    limits = [ATOL + RTOL * abs(a) for a in reference]
    scaled = max(e / bound for e, bound in zip(errors, limits, strict=True))
    return {"passed": all(e <= bound for e, bound in zip(errors, limits, strict=True)),
            "samples": len(errors), "max_absolute_error": max(errors),
            "max_scaled_error": scaled if math.isfinite(scaled) else "overflow",
            "rmse": math.hypot(*(e / math.sqrt(len(errors)) for e in errors))}


def compare(source, directory, args, result):
    directory.mkdir()
    snapshot = directory / "Source.mo"
    snapshot.write_bytes(source.read_bytes())
    result.update(source=str(source), source_sha256=digest(snapshot), directory=str(directory))
    phases = result["phases"]
    fmu = directory / "model.fmu"
    run([args.compiler, snapshot, "-o", fmu], directory, "lean-build",
        args.timeout, phases, cwd=ROOT)
    result["fmu_sha256"] = digest(fmu)
    model, state = model_identity(fmu, snapshot)
    result.update(model=model, variable=state)
    omc_dir = directory / "omc"
    omc_dir.mkdir()
    # JSON quoting supplies the escapes used by these ASCII Modelica strings.
    # The source is passed unchanged to both compilers. OMC receives an ordinary
    # runtime start-value override, with its initialization equations still on.
    script = (f'loadFile({json.dumps(str(snapshot), ensure_ascii=False)});\ngetErrorString();\n'
              f'buildModel({model}, startTime=0, stopTime={args.steps}, '
              f'numberOfIntervals={args.steps}, tolerance=1e-12, method="euler", '
              'outputFormat="csv", fileNamePrefix="reference");\ngetErrorString();\n')
    (omc_dir / "build.mos").write_text(script)
    output = run([args.omc, "--locale=C", "build.mos"], omc_dir, "build", args.timeout, phases)
    # OMC scripting can report errors while returning process exit code zero.
    executable_path = omc_dir / "reference"
    if not executable_path.is_file() or not (omc_dir / "reference_init.xml").is_file() or \
            re.search(r"\bError:", output + (omc_dir / "build.stderr").read_text(errors="replace")):
        raise ValueError(f"OMC build failed; see {omc_dir / 'build.stdout'}")
    result["omc_build_messages"] = output
    run([executable_path, f"-override={state}={args.initial:.17g}", "-noEventEmit", "-r=trace.csv"],
        omc_dir, "simulate", args.timeout, phases)
    reference = trace(omc_dir / "trace.csv", state, args.steps, args.initial)
    result["traces"] = {"omc": reference}
    result["comparisons"] = {}
    # Check both interfaces even if the first one fails.
    for mode in ["me", "cs"]:
        try:
            path = directory / f"lean-{mode}.csv"
            run([args.runner, "simulate", fmu, "--mode", mode, "--start-time", "0",
                 "--start", state, f"{args.initial:.17g}", "--variable", state,
                 "--stop", args.steps, "--step", "1", "--csv", path,
                 "--timeout", args.timeout], directory, f"lean-{mode}", args.timeout, phases)
            values = trace(path, state, args.steps, args.initial)
            result["traces"][mode] = values
            result["comparisons"][mode] = deviation(reference, values)
        except (ValueError, OSError) as e:
            result["comparisons"][mode] = {"passed": False, "error": str(e)}
    result["passed"] = all(item["passed"] for item in result["comparisons"].values())
    if len(result["traces"]) == 3:
        with (directory / "comparison.csv").open("w", newline="") as stream:
            writer = csv.writer(stream)
            writer.writerow(["time", "omc", "lean_me", "lean_cs", "me_minus_omc", "cs_minus_omc"])
            for i, (o, me, cs) in enumerate(zip(reference, result["traces"]["me"], result["traces"]["cs"], strict=True)):
                writer.writerow([i, o, me, cs, me - o, cs - o])
    result["trace_sha256"] = {str(p.relative_to(directory)): digest(p)
                              for p in directory.rglob("*.csv")}


def report_markdown(report):
    lines = ["# Rumoca Lean / OpenModelica comparison", "",
             f"Status: **{'PASS' if report['passed'] else 'FAIL'}**", "",
             f"OMC: `{report['tools']['omc']['version']}`. "
             f"Initial state: `{report['settings']['initial']}`; times: `0..{report['settings']['steps']}`; step: `1`.",
             "OMC and ME use Euler; CS uses the FMU's embedded unit-step solver. "
             "Acceptance: `abs(Lean - OMC) <= 1e-12 + 1e-12 * abs(OMC)`.", "",
             "External numerical evidence only. The source leaves initialization unspecified; "
             "both hosts select the recorded initial state. OMC warnings remain in its build log. "
             "This does not establish formal correctness, standards compliance or full MSL support.", ""]
    for case in report["cases"]:
        lines += [f"## {case['model'] if 'model' in case else 'Uncompiled model'}", "",
                  f"Source: `{case['source']}` — **{'PASS' if case['passed'] else 'FAIL'}**", ""]
        if "error" in case:
            lines += [case["error"], ""]
        for mode, metric in case.get("comparisons", {}).items():
            lines += [f"{mode.upper()}: " + (f"max absolute error `{metric['max_absolute_error']:.6g}`, "
                      f"RMSE `{metric['rmse']:.6g}`, pass `{metric['passed']}`."
                      if "rmse" in metric else metric["error"]), ""]
        traces = case.get("traces", {})
        if len(traces) == 3:
            lines += ["| Time | OMC | Lean ME | Lean CS |", "| ---: | ---: | ---: | ---: |"]
            for i in range(min(len(traces["omc"]), 12)):
                lines.append(f"| {i} | {traces['omc'][i]:.17g} | {traces['me'][i]:.17g} | {traces['cs'][i]:.17g} |")
            lines += ["", "Full samples and differences: `" + str(Path(case["directory"]).relative_to(report["directory"]) / "comparison.csv") + "`.", ""]
        lines += ["| Phase | Wall seconds | Exit |", "| --- | ---: | ---: |"]
        for phase in case["phases"]:
            lines.append(f"| {phase['name']} | {phase.get('wall_s', 0):.3f} | {phase.get('exit_code', 'not started')} |")
        lines += ["", "Lean build includes actual-file kernel checking, native C compilation and FMU packaging. "
                  "OMC build includes Modelica translation and native compilation. "
                  "Simulation process times include host startup and CSV I/O; these are not compiler speed ratios.", ""]
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("models", nargs="*", type=Path, default=[ROOT / "examples/Integrator.mo"])
    parser.add_argument("--omc", default="omc")
    parser.add_argument("--compiler", default=str(ROOT / "packages/compiler/.lake/build/bin/rumoca"))
    parser.add_argument("--runner", default=str(ROOT / "packages/fmu-runner/.lake/build/bin/fmu-runner"))
    parser.add_argument("--out", type=Path, default=ROOT / "build/omc-comparison")
    parser.add_argument("--steps", type=int, default=3, help="Unit steps (1..1000); current certified time profile")
    parser.add_argument("--initial", type=float, default=0.5, help="Explicit shared host-selected initial state")
    parser.add_argument("--timeout", type=int, default=300, help="Wall seconds per external phase")
    args = parser.parse_args()
    if not 1 <= args.steps <= 1000 or not math.isfinite(args.initial) or args.timeout <= 0:
        parser.error("require steps 1..1000, finite initial state, positive timeout")
    output = args.out.resolve()
    if not output.is_relative_to(ROOT / "build"):
        parser.error("comparison artifacts must stay under this checkout's build/")
    try:
        args.omc, args.compiler, args.runner = map(executable, [args.omc, args.compiler, args.runner])
        fmpy = executable("fmpy")
    except ValueError as e:
        parser.error(str(e))
    output.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="run-", dir=output))
    report = {"directory": str(directory), "passed": False, "cases": [],
              "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
              "harness_sha256": digest(Path(__file__)),
              "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
              "settings": {"initial": args.initial, "steps": args.steps, "step": 1,
                           "start_time": 0, "atol": ATOL, "rtol": RTOL,
                           "omc_solver": "euler", "omc_tolerance": 1e-12, "me_solver": "Euler",
                           "cs_solver": "embedded unit step", "alignment": "exact grid, no interpolation",
                           "initialization": "OMC runtime override / FMI host start value; verify first sample"},
              "tools": {}, "setup_phases": [],
              "grammar_sha256": digest(ROOT / "packages/modelica-parser/grammar/Modelica.ebnf"),
              "flake_lock_sha256": digest(ROOT / "flake.lock")}
    print(f"Comparison evidence: {directory}", flush=True)
    try:
        for name, path in [("omc", args.omc), ("rumoca", args.compiler), ("fmpy", fmpy)]:
            version = run([path, "--version"], directory, f"version-{name}", 30, report["setup_phases"]).strip()
            report["tools"][name] = {"path": path, "version": version, "sha256": digest(Path(path))}
        report["tools"]["runner"] = {"path": args.runner, "sha256": digest(Path(args.runner))}
        for i, source in enumerate(args.models):
            case = {"source": str(source.resolve()), "passed": False, "phases": []}
            report["cases"].append(case)
            try:
                compare(source.resolve(), directory / f"model-{i:03d}", args, case)
            except (ValueError, OSError, KeyError, ET.ParseError, BadZipFile) as e:
                case["passed"] = False
                case["error"] = str(e)
            write_json(directory / "report.json", report)
            print(f"{'PASS' if case['passed'] else 'FAIL'} {source}", flush=True)
        report["passed"] = bool(report["cases"]) and all(c["passed"] for c in report["cases"])
        (directory / "report.md").write_text(report_markdown(report))
    finally:
        write_json(directory / "report.json", report)
    print(f"Side-by-side report: {directory / 'report.md'}", flush=True)
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
