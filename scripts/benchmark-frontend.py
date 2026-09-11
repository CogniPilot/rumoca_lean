#!/usr/bin/env python3
"""Native frontend measurement, not a semantic test or an MSL compilation.

Run inside nix develop after lake build rumoca_compiler/rumoca. Uses only
Python's standard library. Inputs, logs and raw measurements stay under build.
Each sample starts a fresh compiler process; the filesystem cache is warmed.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import resource
import statistics
import subprocess
import time


def digest(path):
    # Do not read the 100+ MiB native executable into the harness heap: the
    # child's pre-exec RSS can otherwise contaminate small-process samples.
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def inventory(root, out):
    files = sorted(root.rglob("*.mo"))
    if not files:
        raise ValueError(f"No .mo files under {root}")
    members = [{"path": str(p.relative_to(root)), "bytes": p.stat().st_size,
                "sha256": digest(p)} for p in files]
    sizes = sorted(m["bytes"] for m in members)
    identity = hashlib.sha256(json.dumps(members, sort_keys=True).encode()).hexdigest()
    result = {"root": str(root), "files": len(files), "bytes": sum(sizes),
              "median_bytes": statistics.median(sizes),
              "p95_bytes": sizes[int(.95 * (len(sizes) - 1))],
              "max_bytes": sizes[-1], "inventory_sha256": identity,
              "members": members}
    (out / "corpus.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def sample(command, log, timeout):
    # wait4 reports this child alone; cumulative RUSAGE_CHILDREN cannot supply
    # independent peak-RSS measurements. Capture output to files, not pipes.
    with log.with_suffix(".stdout").open("wb") as stdout, log.with_suffix(".stderr").open("wb") as stderr:
        started = time.perf_counter()
        process = subprocess.Popen(command, stdout=stdout, stderr=stderr)
        timed_out = False
        while True:
            pid, status, usage = os.wait4(process.pid, os.WNOHANG)
            if pid:
                break
            if time.perf_counter() - started > timeout:
                timed_out = True
                process.kill()
                _, status, usage = os.wait4(process.pid, 0)
                break
            time.sleep(.005)
        process.returncode = os.waitstatus_to_exitcode(status)
    result = {"wall_s": time.perf_counter() - started, "user_s": usage.ru_utime,
              "system_s": usage.ru_stime, "peak_rss_kib": usage.ru_maxrss,
              "exit_code": process.returncode, "timed_out": timed_out}
    for line in log.with_suffix(".stdout").read_text().splitlines():
        if line.startswith("VmHWM:"):
            result["post_exec_peak_rss_kib"] = int(line.split()[1])
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", type=Path,
                        default=Path("packages/compiler/.lake/build/bin/rumoca"))
    parser.add_argument("--out", type=Path, default=Path("build/performance-audit"))
    parser.add_argument("--msl", type=Path, help="Exact Modelica library directory; inventory and size proxy only")
    parser.add_argument("--stage-compiler", type=Path, help="Optional modelica-parser frontend-bench executable")
    parser.add_argument("--stages-only", action="store_true")
    parser.add_argument("--workload", nargs="+", help="Run only these named workloads")
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--jobs", type=int, nargs="+", default=[1, 4, 8])
    parser.add_argument("--timeout", type=float, default=45)
    args = parser.parse_args()
    if args.repeats < 1 or any(j < 1 for j in args.jobs) or args.timeout <= 0:
        parser.error("repeats, jobs and timeout must be positive")
    if args.stages_only and not args.stage_compiler:
        parser.error("--stages-only requires --stage-compiler")
    if platform.system() != "Linux":
        parser.error("This runner records Linux wait4 RSS units (KiB)")
    if not args.out.resolve().is_relative_to(Path("build").resolve()):
        parser.error("Measurement output must be under this checkout's build/")
    args.out.mkdir(parents=True, exist_ok=True)
    compiler = args.compiler.resolve(strict=True)
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    meta = {"compiler": str(compiler), "compiler_sha256": digest(compiler),
            "harness_sha256": digest(Path(__file__)),
            "lean_toolchain": Path("lean-toolchain").read_text().strip(),
            "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
            "platform": platform.platform(), "affinity": sorted(os.sched_getaffinity(0)),
            "stack_limit_bytes": resource.getrlimit(resource.RLIMIT_STACK),
            "cpu_model": next((line.split(":", 1)[1].strip() for line in
                               Path("/proc/cpuinfo").read_text().splitlines()
                               if line.startswith("model name")), "unknown"),
            "mode": "warm filesystem, fresh native processes, file I/O + parse + resolve + JSON",
            "repeats": args.repeats, "jobs": args.jobs, "selected_workloads": args.workload}
    if args.stage_compiler:
        args.stage_compiler = args.stage_compiler.resolve(strict=True)
        meta["stage_compiler"] = str(args.stage_compiler)
        meta["stage_compiler_sha256"] = digest(args.stage_compiler)
        meta["stage_source_sha256"] = digest(Path("packages/modelica-parser/Bench/Main.lean"))
    (args.out / "environment.json").write_text(json.dumps(meta, indent=2) + "\n")
    unit = "model Bench Real x; equation der(x) = 1; end Bench;\n"
    workloads = []

    def add(name, texts, expected=0):
        if args.workload and name not in args.workload:
            return
        directory = args.out / "inputs" / name
        directory.mkdir(parents=True, exist_ok=True)
        paths = []
        total = 0
        for i, text in enumerate(texts):
            path = directory / f"{i:05d}.mo"
            path.write_text(text)
            total += len(text.encode())
            paths.append(str(path.resolve()))
        workloads.append((name, paths, total, expected))

    add("startup", [unit])
    for count in [100, 1000, 4000]:
        add(f"tiny_{count}", [unit] * count)
    for size in [64 * 1024, 1024 * 1024, 4 * 1024 * 1024]:
        add(f"whitespace_{size}", [unit + " " * size])
    for length in [4096, 65536]:
        name = "x" * length
        add(f"identifier_{length}", [f"model Bench Real {name}; equation der({name}) = 1; end Bench;\n"])
    for count in [128, 512]:
        add(f"uniform_64k_{count}", [unit + " " * (64 * 1024)] * count)
    add("skewed_64", [unit + " " * (256 * 1024)] * 32 + [unit] * 32)
    add("late_error_1m", [unit + " " * (1024 * 1024) + "@"], expected=1)
    for count in [1024, 16384, 65536]:
        add(f"token_rejection_{count}", [unit + ";" * count], expected=1)
    if args.msl:
        corpus = inventory(args.msl.resolve(strict=True), args.out)
        # Preserve the source byte-size distribution using accepted syntax.
        # This does NOT approximate MSL token density, nesting or semantics.
        add("msl_size_proxy", (unit + " " * max(0, m["bytes"] - len(unit))
                               for m in corpus["members"]))

    requests = []
    if not args.stages_only:
        for name, paths, size, expected in workloads:
            for jobs in args.jobs:
                requests.append((name, paths, size, expected, jobs, "cli",
                                 [str(compiler), "parse", "--json", "--jobs", str(jobs), *paths]))
    if args.stage_compiler:
        for name, paths, size, expected in workloads:
            if name not in ["startup", "whitespace_4194304", "late_error_1m", "token_rejection_65536"]:
                continue
            for stage in ["read", "lex", "parse", "located"]:
                # Lexically valid extra punctuation only fails at parsing.
                stage_exit = 0 if stage == "read" or (stage == "lex" and name.startswith("token_")) else expected
                requests.append((name, paths, size, stage_exit, 1, stage,
                                 [str(args.stage_compiler), stage, paths[0]]))

    records = []
    if args.workload:
        unknown = set(args.workload) - {r[0] for r in requests}
        if unknown:
            parser.error(f"unknown or unavailable workloads: {sorted(unknown)}")
        requests = [r for r in requests if r[0] in args.workload]
    with (args.out / "samples.jsonl").open("w") as raw:
        for name, paths, size, expected, jobs, stage, command in requests:
            # One unrecorded warm-up, with a retained log and failure state.
            prefix = args.out / f"{name}-{stage}-j{jobs}"
            warmup = sample(command, prefix.with_name(prefix.name + "-warmup"), args.timeout)
            runs = []
            for repeat in range(args.repeats):
                result = sample(command, prefix.with_name(prefix.name + f"-r{repeat}"), args.timeout)
                result.update(workload=name, files=len(paths), source_bytes=size, jobs=jobs, stage=stage,
                              repeat=repeat, expected_exit=expected)
                raw.write(json.dumps(result) + "\n")
                raw.flush()
                runs.append(result)
                if result["timed_out"]:
                    break
            record = {"workload": name, "files": len(paths), "source_bytes": size, "stage": stage,
                      "jobs": jobs, "warmup_exit": warmup["exit_code"],
                      "expected_exit": expected,
                      "exit_codes": [r["exit_code"] for r in runs],
                      "median_wall_s": statistics.median(r["wall_s"] for r in runs),
                      "median_peak_rss_kib": statistics.median(r["peak_rss_kib"] for r in runs)}
            if all("post_exec_peak_rss_kib" in r for r in runs):
                record["median_post_exec_peak_rss_kib"] = statistics.median(r["post_exec_peak_rss_kib"] for r in runs)
            records.append(record)
            print(json.dumps(record), flush=True)
            (args.out / "summary.json").write_text(json.dumps(records, indent=2) + "\n")
    return int(any(r["warmup_exit"] != r["expected_exit"] or
                   any(code != r["expected_exit"] for code in r["exit_codes"])
                   for r in records))


if __name__ == "__main__":
    raise SystemExit(main())
