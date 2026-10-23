#!/usr/bin/env python3
"""Measure local CPU scaling and warm-cache Lean elaboration without writing oleans.

Linux, Python standard library, and the project's installed Lake toolchain suffice.
Results include raw timing/resource data and host telemetry; no packages are installed.
"""

import argparse
import concurrent.futures
import datetime
import hashlib
import json
import multiprocessing
import os
from pathlib import Path
import re
import signal
import ssl
import statistics
import subprocess
import sys
import time


LEAN_OPTIONS = [
    "-Dpp.unicode.fun=true", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false",
    "-Dlinter.mathlibStandardSet=true", "-DmaxSynthPendingDepth=3", "-DmaxRecDepth=10000",
]
WORKLOADS = {
    "frodo": "ToVCVio/LatticeCrypto/FrodoKEM/Correctness.lean",
    "ddh": "SecureMessaging/CKA/FromDDH/Security/ReductionRand/RelStep.lean",
}


def read(path):
    try:
        return Path(path).read_text().strip()
    except OSError:
        return None


def cpu_job(iterations):
    return hashlib.pbkdf2_hmac("sha256", b"local-cpu-benchmark", b"fixed-public-salt",
                               iterations, dklen=32).hex()


def worker_mode():
    """Workers inherit the measured process group and its scheduling priority."""
    if len(sys.argv) < 2:
        return False
    if sys.argv[1] == "--cpu-batch":
        workers, iterations = map(int, sys.argv[2:])
        with multiprocessing.get_context("fork").Pool(workers) as pool:
            values = pool.map(cpu_job, [iterations] * 8)
        assert len(set(values)) == 1
        print(values[0])
        return True
    if sys.argv[1] == "--lean-batch":
        workers, module = int(sys.argv[2]), sys.argv[3]
        command = ["lake", "env", "lean", "-j1", *LEAN_OPTIONS, module]
        def job(_):
            result = subprocess.run(command, env={**os.environ, "LEAN_NUM_THREADS": "1"},
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if result.returncode:
                raise RuntimeError(result.stdout)
            return result.returncode
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
            list(pool.map(job, range(4)))
        print("Four independent module elaborations passed; no output files requested.")
        return True
    return False


def snapshot(group=None):
    mem = {}
    for line in (read("/proc/meminfo") or "").splitlines():
        key, value = line.split(":", 1)
        mem[key] = int(value.split()[0])
    vm = dict(line.split() for line in (read("/proc/vmstat") or "").splitlines())
    cpu_line = (read("/proc/stat") or "").splitlines()[0].split()[1:9]
    temps = []
    for hw in Path("/sys/class/hwmon").glob("hwmon*"):
        if read(hw / "name") in {"k10temp", "coretemp", "zenpower"}:
            for sensor in hw.glob("temp*_input"):
                value = read(sensor)
                if value:
                    temps.append(int(value) / 1000)
    frequencies = []
    for cpu in sorted(os.sched_getaffinity(0)):
        value = read(f"/sys/devices/system/cpu/cpu{cpu}/cpufreq/scaling_cur_freq")
        if value:
            frequencies.append(int(value) / 1000)
    pressure = {}
    for name in ["cpu", "memory", "io"]:
        text = read(f"/proc/pressure/{name}") or ""
        pressure[name] = {kind: int(total) for kind, total in
                          re.findall(r"(some|full).*?total=(\d+)", text)}
    group_rss = 0
    group_members = 0
    if group is not None:
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            stat = read(entry / "stat")
            if not stat:
                continue
            fields = stat.rsplit(")", 1)[-1].split()
            if len(fields) > 2 and int(fields[2]) == group:
                match = re.search(r"^VmRSS:\s+(\d+)", read(entry / "status") or "", re.M)
                if match:
                    group_rss += int(match.group(1))
                    group_members += 1
    return {
        "monotonic_s": time.monotonic(), "cpu_ticks": list(map(int, cpu_line)),
        "mem_available_kib": mem.get("MemAvailable"),
        "swap_used_kib": mem.get("SwapTotal", 0) - mem.get("SwapFree", 0),
        "swap_in_pages": int(vm.get("pswpin", 0)), "swap_out_pages": int(vm.get("pswpout", 0)),
        "pressure_total_us": pressure, "load_average": os.getloadavg(),
        "cpu_temperature_c": max(temps) if temps else None,
        "mean_reported_frequency_mhz": statistics.mean(frequencies) if frequencies else None,
        "group_rss_kib": group_rss, "group_members": group_members,
    }


def hardware():
    info = json.loads(subprocess.check_output(["lscpu", "--json"], text=True))
    wanted = {"Architecture", "CPU(s)", "Model name", "Thread(s) per core", "Core(s) per socket",
              "Socket(s)", "CPU max MHz", "CPU min MHz", "L1d cache", "L2 cache", "L3 cache"}
    facts = {item["field"].rstrip(":"): item["data"] for item in info["lscpu"]
             if item["field"].rstrip(":") in wanted}
    cg_path = (read("/proc/self/cgroup") or "").split("::", 1)[-1]
    current = Path("/sys/fs/cgroup") / cg_path.lstrip("/")
    limits = []
    while str(current).startswith("/sys/fs/cgroup"):
        values = {name: read(current / name) for name in ["cpu.max", "memory.max", "cpu.weight"]}
        if any(value is not None for value in values.values()):
            limits.append({"path": str(current), **values})
        if current == Path("/sys/fs/cgroup"):
            break
        current = current.parent
    return {"cpu": facts, "affinity": sorted(os.sched_getaffinity(0)), "cgroup_limits": limits,
            "python": sys.version, "openssl": ssl.OPENSSL_VERSION,
            "governor": read("/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"),
            "boost": read("/sys/devices/system/cpu/cpufreq/boost"),
            "controller_nice": os.getpriority(os.PRIO_PROCESS, 0), "initial": snapshot()}


def source_hashes():
    files = subprocess.check_output(["git", "ls-files", "*.lean", "lean-toolchain",
                                     "lakefile.toml", "lake-manifest.json"], text=True).splitlines()
    return {name: hashlib.sha256(Path(name).read_bytes()).hexdigest() for name in files}


class Benchmark:
    def __init__(self, output, timeout):
        self.output, self.timeout = output, timeout
        output.mkdir(parents=True, exist_ok=False)
        self.data = {"schema": 1, "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                     "hardware": hardware(), "runs": [], "source_hashes_before": source_hashes(),
                     "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                     "lean_toolchain": read("lean-toolchain"), "command": sys.argv,
                     "limitations": ["Warm filesystem/import cache; not a clean full build.",
                                      "Host telemetry includes unrelated workloads.",
                                      "Frequency readings are sampled across allowed logical CPUs.",
                                      "Peak RSS from wait4 is a per-process high-water mark, not a sum.",
                                      "Sampled group RSS sums resident mappings and may count shared pages repeatedly.",
                                      "Synthetic CPU throughput is not a Lean performance prediction."]}
        self.save()

    def save(self):
        (self.output / "results.json").write_text(json.dumps(self.data, indent=2) + "\n")

    def run(self, label, command, *, threads=1, workers=1, nice=19, warmup=False):
        index = len(self.data["runs"]) + 1
        name = f"{index:02d}-{label}-t{threads}-w{workers}-nice{nice}"
        log_path = self.output / f"{name}.log"
        print(f"START {name}", flush=True)
        before = snapshot()
        samples = [before]
        started = time.monotonic()
        reason = None
        full_command = ["nice", "-n", str(nice), *command]
        with log_path.open("w") as log, (self.output / "telemetry.jsonl").open("a") as telemetry:
            process = subprocess.Popen(full_command, stdout=log, stderr=subprocess.STDOUT,
                                       env={**os.environ, "LEAN_NUM_THREADS": str(threads)},
                                       start_new_session=True)
            last_sample = 0.0
            try:
                while True:
                    pid, status, usage = os.wait4(process.pid, os.WNOHANG)
                    if pid:
                        process.returncode = os.waitstatus_to_exitcode(status)
                        break
                    if time.monotonic() - last_sample < 0.5:
                        time.sleep(0.02)
                        continue
                    sample = snapshot(process.pid)
                    last_sample = time.monotonic()
                    samples.append(sample)
                    telemetry.write(json.dumps({"run": name, **sample}) + "\n")
                    telemetry.flush()
                    if time.monotonic() - started > self.timeout:
                        reason = "per-run time limit"
                    if sample["mem_available_kib"] is not None and sample["mem_available_kib"] < 2 * 1024**2:
                        reason = "available memory below 2 GiB guard"
                    if sample["cpu_temperature_c"] is not None and sample["cpu_temperature_c"] > 90:
                        reason = "temperature above conservative 90 C guard (not a vendor limit)"
                    if reason:
                        os.killpg(process.pid, signal.SIGKILL)
                        _, status, usage = os.wait4(process.pid, 0)
                        process.returncode = os.waitstatus_to_exitcode(status)
                        break
                    time.sleep(0.02)
            except BaseException:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                    _, status, _ = os.wait4(process.pid, 0)
                    process.returncode = os.waitstatus_to_exitcode(status)
                except ProcessLookupError:
                    pass
                raise
        wall = time.monotonic() - started
        after = snapshot()
        samples.append(after)
        ticks = [end - start for start, end in zip(before["cpu_ticks"], after["cpu_ticks"])]
        total = sum(ticks) or 1
        temperatures = [s["cpu_temperature_c"] for s in samples if s["cpu_temperature_c"] is not None]
        cpu = usage.ru_utime + usage.ru_stime
        result = {
            "name": name, "label": label, "threads": threads, "workers": workers, "nice": nice,
            "warmup": warmup, "command": full_command, "exit_code": process.returncode,
            "stop_reason": reason, "wall_s": wall, "cpu_s": cpu, "average_cores": cpu / wall,
            "user_s": usage.ru_utime, "system_s": usage.ru_stime,
            "peak_process_rss_mib": usage.ru_maxrss / 1024,
            "peak_sampled_group_rss_mib": max(s["group_rss_kib"] for s in samples) / 1024,
            "min_available_memory_gib": min(s["mem_available_kib"] for s in samples) / 1024**2,
            "minor_faults": usage.ru_minflt, "major_faults": usage.ru_majflt,
            "voluntary_context_switches": usage.ru_nvcsw, "involuntary_context_switches": usage.ru_nivcsw,
            "host_busy_pct": 100 * (total - ticks[3] - ticks[4] - ticks[7]) / total,
            "host_iowait_pct": 100 * ticks[4] / total, "host_steal_pct": 100 * ticks[7] / total,
            "host_swap_in_mib": (after["swap_in_pages"] - before["swap_in_pages"]) * os.sysconf("SC_PAGE_SIZE") / 1024**2,
            "host_swap_out_mib": (after["swap_out_pages"] - before["swap_out_pages"]) * os.sysconf("SC_PAGE_SIZE") / 1024**2,
            "max_cpu_temperature_c": max(temperatures) if temperatures else None,
            "host_pressure_stall_s": {kind: {level: (count - before["pressure_total_us"][kind].get(level, count)) / 1e6
                                             for level, count in levels.items()}
                                      for kind, levels in after["pressure_total_us"].items()},
            "log": log_path.name,
        }
        self.data["runs"].append(result)
        self.save()
        print(f"DONE  {name}: wall={wall:.2f}s CPU={cpu:.2f}s logical_cpus={cpu/wall:.2f} "
              f"RSS={usage.ru_maxrss/1024:.0f}MiB exit={process.returncode}", flush=True)
        if process.returncode:
            raise RuntimeError(f"{name} failed: {reason or 'see log'}")
        return result

    def finish(self):
        self.data["source_hashes_after"] = source_hashes()
        self.data["sources_unchanged"] = self.data["source_hashes_before"] == self.data["source_hashes_after"]
        self.data["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        groups = {}
        for run in self.data["runs"]:
            if not run["warmup"] and run["exit_code"] == 0:
                groups.setdefault((run["label"], run["threads"], run["workers"], run["nice"]), []).append(run)
        summary = []
        for (label, threads, workers, nice), runs in groups.items():
            summary.append({"label": label, "threads": threads, "workers": workers, "nice": nice,
                            "samples": len(runs), "median_wall_s": statistics.median(r["wall_s"] for r in runs),
                            "min_wall_s": min(r["wall_s"] for r in runs), "max_wall_s": max(r["wall_s"] for r in runs),
                            "median_cores": statistics.median(r["average_cores"] for r in runs),
                            "peak_process_rss_mib": max(r["peak_process_rss_mib"] for r in runs),
                            "peak_group_rss_mib": max(r["peak_sampled_group_rss_mib"] for r in runs)})
        self.data["summary"] = summary
        self.save()
        lines = ["# Local CPU and Lean benchmark", "", f"Commit: `{self.data['head']}`", "",
                 f"CPU: {self.data['hardware']['cpu'].get('Model name')}", "",
                 "## Timing summary", "", "Warmups excluded. Lower wall time is better.", "",
                 "| Workload | Lean threads | Workers | Nice | Samples | Median seconds | Range seconds | Logical CPU equivalents | Peak process MiB | Peak summed RSS MiB |",
                 "| --- | ---: | ---: | ---: | ---: | ---: | --- | ---: | ---: | ---: |"]
        for s in summary:
            lines.append(f"| {s['label']} | {s['threads']} | {s['workers']} | {s['nice']} | {s['samples']} | "
                         f"{s['median_wall_s']:.2f} | {s['min_wall_s']:.2f}–{s['max_wall_s']:.2f} | "
                         f"{s['median_cores']:.2f} | {s['peak_process_rss_mib']:.0f} | {s['peak_group_rss_mib']:.0f} |")
        lines += ["", "## Interpretation limits", ""] + [f"- {x}" for x in self.data["limitations"]]
        lines += ["- `average_cores = (user CPU seconds + system CPU seconds) / elapsed seconds`.",
                  "- This ratio measures logical CPU equivalents, not physical cores; parallel tasks can exceed 1.",
                  "- Low utilization can also reflect dependency chains, synchronization, memory access, or scheduling.",
                  "- Synthetic workload: eight fixed PBKDF2 tasks at varying process concurrency.",
                  "- Lean batch workload: four independent Frodo checks with one Lean thread each.",
                  "- Priority comparisons describe this measured load; nice=19 can lose CPU under competition.",
                  "- No cold-cache eviction, package installation, overclocking, or source mutation was performed.",
                  f"- Recorded source files unchanged: {self.data['sources_unchanged']}.", "",
                  "Raw per-run data: [results.json](results.json). Sampled telemetry: [telemetry.jsonl](telemetry.jsonl).", ""]
        (self.output / "REPORT.md").write_text("\n".join(lines))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--threads", default="1,2,4,8")
    parser.add_argument("--repetitions", type=int, default=2)
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--no-synthetic", action="store_true")
    parser.add_argument("--no-lean-batch", action="store_true")
    parser.add_argument("--workloads", default="frodo,ddh")
    args = parser.parse_args()
    os.chdir(Path(__file__).resolve().parents[1])
    if not Path("lean-toolchain").exists():
        parser.error("run inside the Lean project")
    threads = sorted(set(map(int, args.threads.split(","))))
    if min(threads) < 1 or max(threads) > len(os.sched_getaffinity(0)) or args.repetitions < 1:
        parser.error("invalid thread count or repetitions")
    workloads = {key: WORKLOADS[key] for key in args.workloads.split(",")}
    output = args.output or Path(".formalising/benchmarks") / datetime.datetime.now().strftime("local-cpu-%Y%m%d-%H%M%S")
    bench = Benchmark(output, args.timeout)
    script = str(Path(__file__).resolve())
    lean = lambda module, n: ["lake", "env", "lean", f"-j{n}", *LEAN_OPTIONS, module]
    try:
        for rep in range(args.repetitions):
            bench.run("warm-build", ["lake", "build"], threads=4)
        for label, module in workloads.items():
            bench.run(label, lean(module, 4), threads=4, warmup=True)
            for rep in range(args.repetitions):
                # Reverse order on alternate rounds to expose order/thermal effects.
                order = threads if rep % 2 == 0 else threads[::-1]
                for n in order:
                    bench.run(label, lean(module, n), threads=n)
        if "ddh" in workloads:
            for rep in range(args.repetitions):
                for priority in ([0, 19] if rep % 2 == 0 else [19, 0]):
                    bench.run("ddh-priority", lean(workloads["ddh"], 4), threads=4, nice=priority)
        if not args.no_lean_batch:
            for rep in range(args.repetitions):
                for workers in ([1, 2, 4] if rep % 2 == 0 else [4, 2, 1]):
                    bench.run("lean-batch-4", [sys.executable, script, "--lean-batch", str(workers), WORKLOADS["frodo"]],
                              threads=1, workers=workers)
        if not args.no_synthetic:
            start = time.monotonic()
            cpu_job(100000)
            iterations = max(10000, min(5000000, int(100000 * 0.7 / (time.monotonic() - start))))
            bench.data["synthetic_iterations_per_task"] = iterations
            for rep in range(args.repetitions):
                for workers in (threads if rep % 2 == 0 else threads[::-1]):
                    bench.run("cpu-batch-8", [sys.executable, script, "--cpu-batch", str(workers), str(iterations)], workers=workers)
        bench.data["status"] = "complete"
    except BaseException as error:
        bench.data["status"] = "interrupted" if isinstance(error, KeyboardInterrupt) else "failed"
        bench.data["error"] = str(error)
        raise
    finally:
        bench.finish()
        print(f"REPORT {output / 'REPORT.md'}", flush=True)


if __name__ == "__main__" and not worker_mode():
    main()
