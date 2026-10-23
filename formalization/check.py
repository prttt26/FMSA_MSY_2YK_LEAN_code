#!/usr/bin/env python3
"""Check the integrated paper collection through the default Lake build."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

HERE = Path(__file__).resolve().parent
CORE = HERE.parent
RESULTS = HERE / "results"
MODULES = sorted((CORE / "FMSAPaper").glob("*.lean"))
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inspect_module(path):
    source = path.read_text()
    names = re.findall(r"^theorem ([A-Za-z0-9_.]+)", source, re.M)
    namespace = re.search(r"^namespace (\S+)", source, re.M).group(1)
    full_names = [namespace + "." + name for name in names]
    guards = re.findall(r"^#print axioms (\S+)", source, re.M)
    assert guards == full_names, f"Incomplete theorem footprint gates: {path}"
    assert source.count("#guard_msgs") == len(names), path
    footprints = re.findall(r"depends on axioms: \[([^\]]*)\]", source)
    assert len(footprints) == len(names), path
    assert all(set(a.strip() for a in fp.split(",")) <= STANDARD_AXIOMS for fp in footprints), path
    assert not re.search(r"\b(sorry|native_decide)\b|^\s*(axiom|unsafe|admit)\b", source, re.M), path
    return {
        "source": str(path.relative_to(CORE)),
        "source_sha256": digest(path),
        "theorems": full_names,
        "guard_count": len(guards),
    }


def main():
    RESULTS.mkdir(exist_ok=True)
    (RESULTS / "validation.json").write_text(json.dumps({
        "status": "RUNNING", "started_at_utc": datetime.now(timezone.utc).isoformat()
    }, indent=2) + "\n")
    modules = [inspect_module(p) for p in MODULES]
    assert modules, "Missing paper modules"
    root = CORE / "FMSAPaper.lean"
    root_imports = re.findall(r"^import (\S+)", root.read_text(), re.M)
    assert set(root_imports) == {"FMSAPaper." + p.stem for p in MODULES}, "Incomplete paper root"
    entry = CORE / "MSA_and_1st_Truncation.lean"
    assert "FMSAPaper" in re.findall(r"^import (\S+)", entry.read_text(), re.M)
    config = tomllib.loads((CORE / "lakefile.toml").read_text())
    assert "MSA_and_1st_Truncation" in config["defaultTargets"]
    assert "FMSAPaper" in {lib["name"] for lib in config["lean_lib"]}
    foundation = subprocess.run(
        [sys.executable, str(HERE / "audit_foundation.py")],
        cwd=CORE, text=True, capture_output=True,
    )
    (RESULTS / "foundation_audit.log").write_text(foundation.stdout + foundation.stderr)
    command = ["lake", "build"]
    build = subprocess.run(command, cwd=CORE, text=True, capture_output=True)
    build_log = RESULTS / "default_build.log"
    build_log.write_text(build.stdout + build.stderr)
    for module in modules:
        artifact = CORE / ".lake/build/lib/lean" / Path(module["source"]).with_suffix(".olean")
        module["status"] = "PASS" if build.returncode == 0 and artifact.is_file() else "FAIL"
        module["artifact"] = str(artifact.relative_to(CORE))
        if artifact.is_file():
            module["artifact_sha256"] = digest(artifact)
    release = json.loads((CORE / "release-manifest.json").read_text())
    dependencies = {}
    for name in ("mathlib", "batteries"):
        dep = (CORE / config["packagesDir"] / name).resolve()
        dependencies[name] = {
            "head": subprocess.check_output(["git", "-C", str(dep), "rev-parse", "HEAD"], text=True).strip(),
            "status": subprocess.check_output(["git", "-C", str(dep), "status", "--short"], text=True).strip(),
        }
    ok = foundation.returncode == 0 and build.returncode == 0 and all(m["status"] == "PASS" for m in modules)
    record = {
        "status": "PASS" if ok else "FAIL",
        "validated_at_utc": datetime.now(timezone.utc).isoformat(),
        "toolchain": (CORE / "lean-toolchain").read_text().strip(),
        "foundation_version": release["version"],
        "foundation_manifest_sha256": digest(CORE / "release-manifest.json"),
        "foundation_audit": foundation.stdout.strip(),
        "foundation_matches_manifest": foundation.returncode == 0,
        "check_script_sha256": digest(Path(__file__)),
        "dependencies": dependencies,
        "theorem_count": sum(m["guard_count"] for m in modules),
        "standard_axioms_only": ok,
        "modules": modules,
        "default_build": {"command": command, "exit_code": build.returncode,
                          "log": str(build_log.relative_to(HERE)), "log_sha256": digest(build_log)},
        "paper_root_sha256": digest(root),
        "package_entry_sha256": digest(entry),
        "integration": "Included in the foundation's default Lake build; no external LEAN_PATH.",
        "scope": "F2 under explicit fold hypotheses, F3, and actual-MSA F4 under all-order component signs proved; physical seed positive Taylor radius proved. F1 full-line reflected weak formula with both linear Dirac terms, actual all-species positive-radial identification, and its transport through every coupling jet (test/jet interchange and explicit convolution-boundary Cauchy sums) proved; single-species single-tail fold radius proved unconditionally (no sign hypothesis); F5/F6 certified separately by interval arithmetic (formalization/certificates, not Lean); no universal converse or physical positivity claim.",
    }
    (RESULTS / "validation.json").write_text(json.dumps(record, indent=2) + "\n")
    print(f"{record['status']}: {record['theorem_count']} theorem guards, {len(modules)} modules, default Lake build")
    print(foundation.stdout.strip())
    if not ok:
        print(foundation.stderr[-2000:])
        print((build.stdout + build.stderr)[-4000:])
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
