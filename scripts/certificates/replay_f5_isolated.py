#!/usr/bin/env python3
"""Replay the frozen F5 interval certificate without writing to foundation.

Default mode copies the pinned certificate into a temporary directory and
runs its eta=0.2 positive instance plus eta=0.1 negative control. Pass
--full to run all three positive states. --existing-run DIR checks a
previous isolated run with DIR/f5_competing_tails.py, DIR/run.log and
DIR/results/f5_competing_tails.json. This is external interval evidence,
not a Lean theorem or a claim of canonical stability along the real path.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FOUNDATION_CERT = ROOT.parent / "MSA_and_1st_Truncation" / "formalization" / "certificates" / "f5_competing_tails.py"
FROZEN_RESULT = FOUNDATION_CERT.parent / "results" / "f5_competing_tails.json"
EXPECTED_SHA256 = "627fa0095a45d59946c4e51b1e82f0473346e9497d23bca4bd50377925a353a1"
DEFAULT_RECEIPT = ROOT / "results" / "certificates" / "codex_f5_isolated_replay.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def intervals_disjoint(left: list[float], right: list[float]) -> bool:
    assert len(left) == len(right) == 2
    assert left[0] <= left[1] and right[0] <= right[1]
    return left[1] < right[0] or right[1] < left[0]


def endpoint_boxes_disjoint(start: list, end: list) -> bool:
    assert len(start) == len(end) > 0
    return any(intervals_disjoint(a[0], b[0]) or intervals_disjoint(a[1], b[1])
               for a, b in zip(start, end))


def inspect(run_dir: Path, full: bool) -> dict:
    copied = run_dir / "f5_competing_tails.py"
    log = run_dir / "run.log"
    result = run_dir / "results" / "f5_competing_tails.json"
    assert sha256(FOUNDATION_CERT) == EXPECTED_SHA256, "frozen F5 source changed"
    assert sha256(copied) == EXPECTED_SHA256, "replayed F5 copy differs"
    assert log.is_file() and result.is_file(), "missing isolated F5 output"
    assert log.read_text().rstrip().endswith("PASS"), "certificate did not print PASS"
    data = json.loads(result.read_text())
    assert data["z"] == ["1.8", "12"] and data["kv"] == ["1", "-6"]
    states = data["states"]
    expected_eta = ["0.2", "0.3", "0.4"] if full else ["0.2"]
    assert [s["model"]["eta"] for s in states] == expected_eta
    for state in states:
        assert state["model"]["z"] == data["z"]
        assert state["model"]["kv"] == data["kv"]
        assert state["tau_max"] == 3.0 and state["circle_radius"] == 2.75
        assert state["real_branch_certified"] is True
        assert state["monodromy_nontrivial"] is True
        assert state["real_pieces"] > 0 and state["circle_pieces"] > 0
        assert state["real_worst_contraction"] < 1.0
        assert state["circle_worst_contraction"] < 1.0
        assert endpoint_boxes_disjoint(state["start_enclosure"], state["end_enclosure"])
    control = data["negative_control"]
    assert control == {"eta": "0.1", "circle_radius": 2.75,
                       "monodromy_nontrivial": False, "expected": False}
    frozen_match = None
    if FROZEN_RESULT.is_file():
        frozen = json.loads(FROZEN_RESULT.read_text())
        if len(frozen.get("states", [])) >= len(states):
            same_states = True
            for state, prior in zip(states, frozen["states"]):
                current_fields = {k: v for k, v in state.items() if k != "seconds"}
                prior_fields = {k: v for k, v in prior.items() if k != "seconds"}
                same_states = same_states and current_fields == prior_fields
            frozen_match = same_states and control == frozen.get("negative_control")
    return {
        "status": "PASS",
        "scope": "External F5 interval certificate: regular real PY-seeded root on [0,3] and nontrivial monodromy at radius 2.75; no Lean instance or canonicality claim.",
        "source_sha256": EXPECTED_SHA256,
        "result_sha256": sha256(result),
        "run_log_sha256": sha256(log),
        "mode": "full" if full else "quick",
        "matches_frozen_result_excluding_elapsed_time": frozen_match,
        "states": [{
            "eta": s["model"]["eta"],
            "real_pieces": s["real_pieces"],
            "circle_pieces": s["circle_pieces"],
            "real_worst_contraction": s["real_worst_contraction"],
            "circle_worst_contraction": s["circle_worst_contraction"],
            "real_branch_certified": s["real_branch_certified"],
            "monodromy_nontrivial": s["monodromy_nontrivial"],
            "endpoint_boxes_disjoint_independently": endpoint_boxes_disjoint(
                s["start_enclosure"], s["end_enclosure"]),
        } for s in states],
        "negative_control": control,
    }


def preserve_artifacts(run_dir: Path, full: bool) -> dict:
    prefix = "codex_f5_full" if full else "codex_f5_quick"
    out_dir = ROOT / "results" / "certificates"
    out_dir.mkdir(parents=True, exist_ok=True)
    result_out = out_dir / f"{prefix}_result.json"
    log_out = out_dir / f"{prefix}_run.log"
    shutil.copyfile(run_dir / "results" / "f5_competing_tails.json", result_out)
    shutil.copyfile(run_dir / "run.log", log_out)
    return {"result_artifact": str(result_out.relative_to(ROOT)),
            "run_log_artifact": str(log_out.relative_to(ROOT))}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="verify eta=0.2, 0.3, 0.4 plus negative control")
    parser.add_argument("--existing-run", type=Path, help="inspect a prior isolated run instead of rerunning")
    parser.add_argument("--receipt", type=Path, default=DEFAULT_RECEIPT)
    args = parser.parse_args()

    if args.existing_run is not None:
        receipt = inspect(args.existing_run, args.full)
        receipt.update(preserve_artifacts(args.existing_run, args.full))
    else:
        with tempfile.TemporaryDirectory(prefix="f5_isolated_") as work:
            run_dir = Path(work)
            assert sha256(FOUNDATION_CERT) == EXPECTED_SHA256, "frozen F5 source changed"
            shutil.copyfile(FOUNDATION_CERT, run_dir / "f5_competing_tails.py")
            command = [sys.executable, str(run_dir / "f5_competing_tails.py")]
            if not args.full:
                command.append("--quick")
            with (run_dir / "run.log").open("w") as log_file:
                completed = subprocess.run(command, stdout=log_file, stderr=subprocess.STDOUT, check=False)
            assert completed.returncode == 0, f"F5 replay exited {completed.returncode}"
            receipt = inspect(run_dir, args.full)
            receipt.update(preserve_artifacts(run_dir, args.full))

    args.receipt.parent.mkdir(parents=True, exist_ok=True)
    args.receipt.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(f"PASS: isolated F5 {receipt['mode']} certificate, {len(receipt['states'])} positive state(s) and negative control")
    print(args.receipt)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
