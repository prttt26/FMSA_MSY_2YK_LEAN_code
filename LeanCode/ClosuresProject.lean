import LeanCode.Closures.ClosureExpansions
import LeanCode.Closures.DPClosureMap

/-!
# Other-closures track (PYE / HNCB) — scope and axiom gate

**What this file is for.** Companion to `FMSAProject.lean` / `ExactMSAProject.lean`: the same "scope
by import + axiom footprint as a build gate" discipline, for the closures that are **not** the
FMSA-DP first-order construction itself and **not** the exact MSA — namely:

* **PYE** — the `pullback_passes = 0` YK-tail FMSA-DP construction **is** first-order PY; the only
  error versus true first-order PY is the finite-Yukawa-tail re-approximation of the outer closure
  `g_HS·(−βu)`.  Gated: the DCF-error identity `dp_error_entry_norm_le` /
  `dp_sub_py_first_order_eq_conj_residual` (PYE.3), the `k → r` core bridge
  `inner_core_dcf_eq_of_exact_fit` (PYE.5), and tail-fit density `exists_yukawa_tail_fit` (PYE.7).
* **HNCB** — first-order HNCB bridge: `hncb_first_order_outer` and the `γ₁`-collapse
  `pass_zero_eq_py_first_order` (HNCB.1).

Like `FMSAProject.lean`, every `#guard_msgs` block below fails the build if the axiom set of that
declaration changes.  All results guarded here are **axiom-clean** (the standard three only).

⚠ **Overlap with `FMSAProject.lean`.** The *shared* first-order-outer results the FMSA-DP paper
itself consumes — `dpDCFLinear`, `py_first_order_outer`, `msa_first_order_outer` — are gated in
`FMSAProject.lean`, not re-gated here; this file gates only the PYE/HNCB-specific capstones.
-/

/-! ## PYE — the no-pull-back construction is first-order PY -/

/-- info: 'FMSA.FirstOrderClosure.dp_error_entry_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.dp_error_entry_norm_le

/-- info: 'FMSA.FirstOrderClosure.dp_sub_py_first_order_eq_conj_residual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.dp_sub_py_first_order_eq_conj_residual

/-- info: 'FMSA.FirstOrderClosure.inner_core_dcf_eq_of_exact_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.inner_core_dcf_eq_of_exact_fit

/-- info: 'FMSA.FirstOrderClosure.exists_yukawa_tail_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.exists_yukawa_tail_fit

/-! **PYE.4 capstone (conditional).**  `DP-map[g_HS·(−βu)] = (OZ+PY)₁` assembled into one theorem: the
finite-tail DP DCFs converge entrywise to the exact first-order PY DCF, on the single analytic hypothesis
`WHProjectionL1` (the matrix Wiener-`1/f` `L¹` bound — deliberately a hypothesis, not a duplicated MA-class
axiom).  std-3: the assembly itself introduces no axiom. -/
/-- info: 'FMSA.FirstOrderClosure.dp_converges_to_py_first_order_of_whProjectionL1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.dp_converges_to_py_first_order_of_whProjectionL1

/-! ## HNCB — first-order HNCB bridge -/

/-- info: 'FMSA.FirstOrderClosure.hncb_first_order_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.hncb_first_order_outer

/-- info: 'FMSA.FirstOrderClosure.pass_zero_eq_py_first_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.pass_zero_eq_py_first_order

/-! **HNCB.2 — the fixed-rate predictor–corrector pull-back rung is affine** `K̃' = a + L·K̃`
(`a = refit(−βu)`, `L = pullbackLinearPart`): every sub-step (`dpDCFLinear`, `starConjLinear`, bridge
scaling, `refit`, `embed`) is `ℂ`-linear, so the frozen-rate rung splits as constant + bundled linear
map.  std-3. -/
/-- info: 'FMSA.FirstOrderClosure.pullbackRung_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms FMSA.FirstOrderClosure.pullbackRung_affine
