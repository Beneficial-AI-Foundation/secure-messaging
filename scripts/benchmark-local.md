# Local CPU and Lean performance measurements

Run from any working directory using the script path. It resolves this repository automatically.

```bash
python3 scripts/benchmark-local.py
```

The default suite uses two repetitions, 1/2/4/8 Lean threads, two existing proof files, normal/low priority comparisons, four independent Lean jobs, and eight fixed synthetic CPU tasks. Results go to a fresh timestamped directory under `.formalising/benchmarks/`.

For a short Frodo-only check:

```bash
python3 scripts/benchmark-local.py --workloads frodo --repetitions 1 --no-lean-batch --no-synthetic
```

## Prerequisites and boundaries

- Linux, Python standard library, the installed project Lean/Lake toolchain, and built dependencies.
- No package installation, cache eviction, CPU-governor changes, or overclocking.
- Lean file checks run without `-o`, `-i`, or `-c`: they elaborate source but do not replace compiled modules.
- The unchanged `lake build` measurement may perform normal Lake cache maintenance. It is not a clean-build benchmark.
- Run alone when possible. The suite records host load, memory pressure, swap activity, frequency and temperature, but cannot eliminate unrelated desktop workloads.
- Per-run timeout defaults to 180 seconds. Runs stop if available RAM drops below 2 GiB or a reported CPU sensor exceeds a conservative 90 °C guard. This guard is not a vendor temperature specification.
- Existing plan/executor activity should remain paused while collecting comparable measurements.

## Saved artifacts

- `REPORT.md`: timing table and scope limitations.
- `results.json`: hardware/toolchain identity, commit, source hashes, per-run CPU/wall times, memory and fault metrics, scheduling counters, host pressure and swap deltas.
- `telemetry.jsonl`: approximately twice-per-second samples, identified by run name.
- Individual logs: exact Lean/Lake diagnostics and synthetic-work checksums.

Completed runs are saved immediately, including when a later run fails. A final report is written on interruption when Python can unwind normally.

## Reading the metrics

**Elapsed seconds** measure the time a user waits. **CPU-seconds** sum time spent executing across measured processes/threads, including waited-for children. Their ratio is **average logical CPU equivalents**: 2 CPU-seconds per elapsed second means about two logical CPUs were occupied on average. On this SMT machine, that does not necessarily mean two physical cores. The JSON field retains the name `average_cores`. A low ratio does not identify the cause by itself: sequential dependencies, synchronization, memory access, I/O and scheduling can all contribute.

The thread sweep measures one file at a time. The Lean batch runs four independent Frodo file checks with one Lean thread each; it models a different source of parallelism. A thread setting that is fastest for one file is not automatically the best setting for an entire build dependency graph.

`peak_process_rss_mib` is the Linux wait4 per-process high-water mark, not combined memory for simultaneous workers. `peak_sampled_group_rss_mib` sums resident mappings and can count shared library/import pages repeatedly. Use both alongside minimum available system RAM; neither RSS field is an exact physical-memory requirement for the whole workload.

Occupied swap alone does not demonstrate a bottleneck. Check **swap-in/out during the measured interval**, process major faults, memory pressure and elapsed-time variation. Host swap/pressure counters include unrelated applications.

Synthetic CPU scaling measures eight fixed PBKDF2 tasks, with the same iteration count throughout one suite. The count is calibrated once and saved. For cross-machine comparisons, normalize total work (`8 × iterations / elapsed time`), and keep Python/OpenSSL versions comparable. It is a hardware throughput indicator, not a prediction of Lean speed or a cryptographic security test.

Normal (`nice=0`) versus low (`nice=19`) priority is measured under the current host load. Similar times on an idle machine do not mean niceness is irrelevant under contention. Do not change normal project scheduling policy based on small differences within the observed run-to-run range.

## Comparing future runs

Keep the commit, dependency manifest, toolchain, workload, repetition count and cache conditions comparable. Prefer medians and ranges over a single fastest run. Inspect the raw telemetry before attributing slowdowns to CPU hardware. The suite deliberately does not claim a whole-project cold-build time, a universal optimal worker count, or an isolated memory-bandwidth measurement.
