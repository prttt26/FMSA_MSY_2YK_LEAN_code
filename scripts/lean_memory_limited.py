#!/usr/bin/env python3
"""Run the pinned Lean compiler with a hard monitored resident-memory cap.

Set FMSA_LEAN_RSS_LIMIT_MIB to lower the 30720 MiB cap for a test. Exceeding
the cap kills the compiler process group and returns failure (exit 137).

Set FMSA_LEAN_LOCK_PER_PROCESS=1 to hold /tmp/fmsa_lean_single.lock around this one compiler
process. A long sequential build then keeps one Lean process at a time across sessions without
blocking other sessions for its whole duration. Do not combine it with an outer `flock` on the same
file: the inner request would wait on the outer holder forever.
"""

import fcntl
import os
from pathlib import Path
import signal
import subprocess
import sys
import time


PIN = (Path(__file__).resolve().parents[1] / "lean-toolchain").read_text().strip()
LEAN = Path.home() / ".elan/toolchains" / PIN.replace("/", "--").replace(":", "---") / "bin/lean"
LIMIT_MIB = int(os.environ.get("FMSA_LEAN_RSS_LIMIT_MIB", "30720"))
if not 0 < LIMIT_MIB <= 30720:
    raise SystemExit("FMSA_LEAN_RSS_LIMIT_MIB must be in 1..30720")
LIMIT_KIB = LIMIT_MIB * 1024


def descendants(pid):
    todo = [pid]
    seen = set()
    while todo:
        child = todo.pop()
        if child in seen:
            continue
        seen.add(child)
        try:
            data = Path(f"/proc/{child}/task/{child}/children").read_text()
        except (FileNotFoundError, ProcessLookupError):
            continue
        todo.extend(int(part) for part in data.split())
    return seen


def rss_kib(pid):
    try:
        for line in Path(f"/proc/{pid}/status").read_text().splitlines():
            if line.startswith("VmRSS:"):
                return int(line.split()[1])
    except (FileNotFoundError, ProcessLookupError):
        pass
    return 0


def stop_group(proc):
    try:
        os.killpg(proc.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    proc.wait()


def main():
    if os.environ.get("FMSA_LEAN_LOCK_PER_PROCESS") == "1":
        lock = open("/tmp/fmsa_lean_single.lock", "a")
        fcntl.flock(lock, fcntl.LOCK_EX)
    command = [str(LEAN), *sys.argv[1:]]
    if not any(arg == "-M" or arg.startswith("--memory") for arg in sys.argv[1:]):
        command[1:1] = ["-M", str(LIMIT_MIB)]
    if not any(arg == "-j" or arg.startswith("--threads") for arg in sys.argv[1:]):
        command[1:1] = ["-j", "1"]
    proc = subprocess.Popen(command, start_new_session=True)
    peak = 0
    try:
        while proc.poll() is None:
            usage = {pid: rss_kib(pid) for pid in descendants(proc.pid)}
            current = sum(usage.values())
            peak = max(peak, current)
            if current > LIMIT_KIB:
                print(
                    f"LEAN_MEMORY_LIMIT_EXCEEDED: peak {peak / 1024:.1f} MiB "
                    f"> cap {LIMIT_MIB} MiB; run failed; "
                    f"processes {usage}",
                    file=sys.stderr,
                    flush=True,
                )
                stop_group(proc)
                return 137
            time.sleep(0.05)
        if os.environ.get("FMSA_LEAN_REPORT_RSS") == "1":
            print(f"LEAN_PEAK_RSS_MIB: {peak / 1024:.1f}", file=sys.stderr)
        return proc.returncode
    except KeyboardInterrupt:
        stop_group(proc)
        return 130


if __name__ == "__main__":
    raise SystemExit(main())
