"""Validate and record the kernel-checked migration of four legacy matrix interfaces.

Run after the four-target build and both dependency audits stored in
results/multitail_extension. No numerical or symbolic oracle is a proof premise.
"""
from pathlib import Path
import collections
import hashlib
import json
import re
import subprocess

BASE = Path(__file__).resolve().parents[1]
RES = BASE / 'results/multitail_extension'
STD3 = ('propext', 'Classical.choice', 'Quot.sound')
STD2 = ('propext', 'Quot.sound')
RETIRED = [
    'MSAMixture.matExactMSAEqualDiam_hcore',
    'FMSA.ExactMSA.MatEqualDiamCertificate.matExactMSAEqualDiam_kspace_residual',
    'MSAMixture.matExactMSAUnequalDiam_hcore',
    'MSAMixture.matHSexactUnequalDiam_kspace',
]
MODULES = ['MSAMixture' + n for n in [
    'BHRootDefs', 'BHRootUneqDefs', 'BHRootRecenter', 'BaxterLaplace',
    'LegacySingleTail', 'LegacyFourier', 'EqualRootBridge',
    'SingleTailOriginPolynomial', 'EqualCoreOrigin', 'EqualCoreOriginAlgebra',
    'EqualCoreResidues', 'EqualCorePolynomial', 'EqualCoreBridge',
]]
ADDITIONAL = [
    'LeanCode/ExactMSAProject.lean', 'LeanCode/MixtureLegacyRetirementProject.lean',
] + ['LeanCode/YukawaOZMix/' + n + '.lean' for n in MODULES + [
    'MSAMixtureBHRoot', 'MSAMixtureBHRootUneq', 'MSAMixtureBHRootSmooth',
    'MSAMixtureBHRootUneqSmooth', 'MSAMixtureFinOne',
    'MatExactMSAEqualDiamCertificate', 'MixtureBlumHoyeDerivation',
    'MSAMixtureCore', 'MSAMixtureCoreUneq',
]]


def stripped(source):
    out = []
    i = depth = 0
    quoted = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1
                i += 2
                continue
            if source.startswith('-/', i):
                depth -= 1
                i += 2
                continue
            out.append('\n' if source[i] == '\n' else ' ')
            i += 1
            continue
        if quoted:
            if source[i] == '\\':
                out.extend('  ')
                i += 2
                continue
            if source[i] == '"':
                quoted = False
            out.append('\n' if source[i] == '\n' else ' ')
            i += 1
            continue
        if source.startswith('/-', i):
            depth = 1
            i += 2
            continue
        if source.startswith('--', i):
            j = source.find('\n', i)
            j = len(source) if j < 0 else j
            out.extend(' ' * (j - i))
            i = j
            continue
        if source[i] == '"':
            quoted = True
            out.append(' ')
            i += 1
            continue
        out.append(source[i])
        i += 1
    assert depth == 0 and not quoted
    return ''.join(out)


def audit(filename):
    content = (RES / filename).read_text()
    assert 'error:' not in content
    entries = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", content, re.S)
    assert len({n for n, _ in entries}) == len(entries)
    return {n: tuple(a.strip() for a in ax.split(',')) for n, ax in entries}


build = (RES / 'mixture_legacy_retirement_build.log').read_text()
m = re.search(r'Build completed successfully \((\d+) jobs\)', build)
assert m and 'error:' not in build
jobs = int(m[1])
legacy = audit('mixture_legacy_retirement_dependency_audit.log')
joint = audit('mixture_legacy_retirement_joint_audit.log')
assert len(legacy) == 77 and set(legacy.values()) == {STD3}
assert len(joint) == 526
assert collections.Counter(joint.values()) == {STD3: 524, STD2: 2}
assert all(legacy[n] == STD3 for n in RETIRED)
assert legacy.items() <= joint.items()
mt_guards = len(re.findall(r'^#guard_msgs', (BASE / 'LeanCode/MultiTailMSAProject.lean').read_text(), re.M))
ret_guards = len(re.findall(r'^#guard_msgs', (BASE / 'LeanCode/MixtureLegacyRetirementProject.lean').read_text(), re.M))
assert mt_guards == 1074 and ret_guards == 77
scan_path = RES / 'mixture_nonlinear_reconstruction_source_scan.json'
scan = json.loads(scan_path.read_text())
paths = sorted(set(scan['paths'] + ADDITIONAL))
hashes = {}
for path in paths:
    raw = (BASE / path).read_bytes()
    hashes[path] = hashlib.sha256(raw).hexdigest()
    code = stripped(raw.decode())
    hits = re.findall(r'(?m)^\s*axiom\s+\w+|\b(?:sorry|native_decide|ofReduceBool)\b', code)
    assert not hits, (path, hits)
for path in ADDITIONAL:
    assert all(line == line.rstrip() for line in (BASE / path).read_text().splitlines()), path
for name in RETIRED:
    short = name.rsplit('.', 1)[1]
    definitions = sum(len(re.findall(r'^theorem ' + short + r'\b', stripped((BASE / p).read_text()), re.M))
                      for p in ADDITIONAL)
    assert definitions == 1, (name, definitions)
check = subprocess.run(['git', 'diff', '--check'], cwd=BASE, capture_output=True, text=True)
assert check.returncode == 0, check.stdout + check.stderr
scan.update(files=len(paths), paths=paths, sha256=hashes, forbidden=[], forbidden_matches={})
scan_path.write_text(json.dumps(scan, indent=2) + '\n')
checkpoint = {
    'retired_axioms': RETIRED, 'retired_count': 4,
    'replaced_by_kernel_checked_theorems': True,
    'original_DCF_definitions_and_closed_RHS_preserved': True,
    'new_definition_and_bridge_modules': ['LeanCode/YukawaOZMix/' + n + '.lean' for n in MODULES],
    'default_guard_module': 'LeanCode/MixtureLegacyRetirementProject.lean',
    'default_migration_guards': ret_guards,
    'existing_multitail_guards': mt_guards,
    'tracked_combined_guards': mt_guards + ret_guards,
    'guard_scope': 'MultiTailMSAProject plus MixtureLegacyRetirementProject; other existing project guards are additional',
    'audited_migration_theorems': len(legacy),
    'joint_independent_theorem_footprints': len(joint),
    'joint_axiom_counts': {'standard_three': 524, 'propext_Quot_sound': 2},
    'build_jobs': jobs,
    'build_targets': ['LeanCode', 'ExactMSACertificate', 'ExactMSASparseFeasibility', 'MatExactMSAEqualDiamCertificate'],
    'build_log': 'mixture_legacy_retirement_build.log',
    'dependency_log': 'mixture_legacy_retirement_dependency_audit.log',
    'joint_dependency_log': 'mixture_legacy_retirement_joint_audit.log',
    'selected_source_hashes': len(paths), 'git_diff_check': 'PASS',
    'legacy_Fourier_domain': 'supplied actual single-tail BH root; z>0; k!=0; sigma_i>0; rho_i>=0; vacMix>0; symmetric K. Equal-diameter interfaces additionally sigma_i=sig>0. HS anchor has no nonlinear root premise.',
    'weighted_RDF_decay_budget_needed_for_legacy_Fourier': False,
    'arbitrary_finite_tail_scope': 'The previously completed automatic finite-tail Wronskian theorem is unchanged; the four legacy interfaces are its faithful singleton-tail specializations.',
    'retained_physical_limits': ['global root existence and continuation', 'all-state RDF decay', 'g>=0', 'thermodynamic route consistency', 'Maxwell/binodal physical accuracy', 'universal finite-order anomaly thresholds', 'SCOZA'],
}
(RES / 'mixture_legacy_retirement_validation.json').write_text(json.dumps(checkpoint, indent=2) + '\n')
vpath = RES / 'validation_summary.json'
v = json.loads(vpath.read_text())
v.update(axiom_gates=mt_guards + ret_guards, axiom_gate_scope=checkpoint['guard_scope'],
         full_build_jobs=jobs, full_build_targets=checkpoint['build_targets'],
         full_build_log=checkpoint['build_log'], mixture_legacy_matrix_axioms_retired=True,
         mixture_legacy_interface_migration=checkpoint)
v['certified_source_scan']['files'] = len(paths)
v['mixture_actual_pair_HS_reference_Fourier_proof_domain']['old_extra_axioms'] = 'The four legacy matrix SymPy-supported axioms are now replaced by proved theorems; the independent shell-injectivity axiom is outside this retirement and unused by these audited theorems.'
a = v['mixture_nonlinear_joint_audit']
a.update(default_gates=mt_guards + ret_guards, guard_scope=checkpoint['guard_scope'], build_jobs=jobs,
         selected_sources=len(paths), total_independent_theorem_footprints=len(joint),
         legacy_migration_footprints=len(legacy), axioms='524 standard-three footprints plus two generic HS identities using propext/Quot.sound; four legacy physics axioms retired',
         dependency_log=checkpoint['joint_dependency_log'], build_log=checkpoint['build_log'])
vpath.write_text(json.dumps(v, indent=2) + '\n')
hpath = RES / 'mixture_paper_process_handoff.json'
h = json.loads(hpath.read_text())
h['checkpoint'] = {'tracked_axiom_guards': mt_guards + ret_guards, 'multitail_guards': mt_guards,
                   'legacy_migration_guards': ret_guards, 'build_jobs': jobs, 'scanned_sources': len(paths),
                   'independent_nonlinear_footprints': 438, 'additional_thermodynamic_scope_footprints': 11,
                   'additional_legacy_migration_footprints': len(legacy), 'total_independent_footprints': len(joint)}
h['validation'] = f'four-target build PASS ({jobs} jobs); 1074 retained multitail gates plus 77 new migration gates; {len(paths)} selected source hashes; 526-footprint joint audit uses standard axiom subsets only; source scan and git diff --check PASS'
h['legacy_matrix_retirement_checkpoint'] = checkpoint
legacy_paragraph = 'The four legacy matrix closure-recovery and hard-sphere Fourier assumptions have also been replaced by kernel-checked theorems. The migration preserves the original unequal-diameter piecewise DCF, the five-coefficient equal-diameter DCF, and the closed trigonometric residual. For supplied single-tail BH roots with symmetric strengths, positive rates and diameters, nonnegative species densities and positive free volume, the original matrix Fourier identities hold at every nonzero real wave number. This Fourier result does not require the sufficient weighted RDF decay budget used by the reconstructed RDF/OZ capstone. Neither result supplies thermodynamic route consistency, nonnegative RDFs or accurate Maxwell/binodal coexistence.'
if legacy_paragraph not in h['replacement_paragraphs']:
    h['replacement_paragraphs'].append(legacy_paragraph)
if not (RES / 'mixture_paper_notification_1151_receipt.json').exists():
    h['delivery_status'] = 'Legacy matrix interface migration and four-axiom retirement validated; new notification pending.'
hpath.write_text(json.dumps(h, indent=2) + '\n')
print(json.dumps({'build_jobs': jobs, 'tracked_guards': mt_guards + ret_guards,
                  'selected_sources': len(paths), 'independent_footprints': len(joint), 'retired_axioms': RETIRED}))
