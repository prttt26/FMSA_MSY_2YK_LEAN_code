#!/usr/bin/env python3
"""Check the RATIONAL PART of the independent external M2 Jacobian witness.

Python standard library only. Recomputes I-C*J and its norm using exact
Fraction intervals, checks exact input widening and source hashes. This does
NOT verify that the supplied J intervals enclose the actual analytic Jacobian;
that separate analytic step relies on SymPy transcription/differentiation and
Arb evaluation. It is not Lean verification or a root-existence test.
"""
from argparse import ArgumentParser
from decimal import Decimal
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError('Certificate assertions must remain enabled; do not use python -O.')

RESEARCH = Path(__file__).resolve().parents[2]
DEFAULT = RESEARCH / 'results/certificates/codex_m2_jacobian_arb.json'


def check(report):
    r = json.loads(Path(report).read_text())
    expected_sources = {
        'MSA_Convergence/scripts/certificates/codex_m2_jacobian_arb.py',
        'MSA_Convergence/scripts/certificates/check_m2_jacobian_rational.py',
        'MSA_Convergence/results/two_tail/two_tail_m2_jacobian_interval.json',
        'MSA_Convergence/MSAConvergence/BHResidualPolynomials.lean',
        'MSA_and_1st_Truncation/results/coupling_singularities/codex_m2_zero_mode_firstness.json',
        'MSA_and_1st_Truncation/LeanCode/YukawaOZMix/MSAMultiTailMixtureSystem.lean',
        'MSA_and_1st_Truncation/LeanCode/YukawaOZMix/MSAMixtureConcrete.lean',
        'MSA_and_1st_Truncation/LeanCode/YukawaOZMix/MSAMixtureCancellation.lean',
        'MSA_and_1st_Truncation/LeanCode/HSMixture/MatrixQ0.lean',
    }
    assert set(r['source_sha256']) == expected_sources
    assert r['source_sha256']['MSA_and_1st_Truncation/results/coupling_singularities/codex_m2_zero_mode_firstness.json'] == 'd75a89d83c0c5fb80c3bdcf243e04c9de906384f1a1da4e573a3c518dff0cbb9'
    for rel, expected in r['source_sha256'].items():
        assert hashlib.sha256((RESEARCH.parent/rel).read_bytes()).hexdigest() == expected, rel
    root = json.loads((RESEARCH.parent/'MSA_and_1st_Truncation/results/coupling_singularities/codex_m2_zero_mode_firstness.json').read_text(), parse_float=Decimal)
    pre = json.loads((RESEARCH/'results/two_tail/two_tail_m2_jacobian_interval.json').read_text())
    assert r['coordinate_order'] == ['D1', 'D2', 'G1', 'G2', 'tau', 'weight']
    assert r['physical_data'] == {'eta': '1/10', 'rho': '3/(5*pi)', 'sigma': '1', 'z': ['9/5', '12'], 'K': ['1', 'weight']}
    assert r['C_rational'] == pre['C_rational']
    widen = Q(r['relative_widen_rational'])
    assert widen > 0
    assert len(r['exact_widened_box_rational']) == len(r['arb_input_box_rational_enclosure']) == 6
    for i, ends in enumerate(root['root_box'][:6]):
        lo, hi = map(Q, ends)
        delta = widen*max(Q(1), abs(lo), abs(hi))
        expected = [lo-delta, hi+delta]
        assert list(map(Q, r['exact_widened_box_rational'][i])) == expected
        alo, ahi = map(Q, r['arb_input_box_rational_enclosure'][i])
        assert alo <= expected[0] <= expected[1] <= ahi
    C = [[Q(x) for x in row] for row in r['C_rational']]
    J = [[tuple(map(Q, x)) for x in row] for row in r['J_rational_enclosure']]
    assert len(C) == len(J) == 4 and all(len(row) == 4 for row in C+J)
    assert all(len(x) == 2 and x[0] <= x[1] for row in J for x in row)
    calculated, rows = [], []
    for i in range(4):
        row, norm = [], Q(0)
        for j in range(4):
            lower, upper = Q(i == j), Q(i == j)
            for k in range(4):
                a, b = sorted([-C[i][k]*J[k][j][0], -C[i][k]*J[k][j][1]])
                lower += a
                upper += b
            row.append([str(lower), str(upper)])
            norm += max(abs(lower), abs(upper))
        calculated.append(row)
        rows.append(norm)
    assert calculated == r['I_minus_CJ_rational_enclosure']
    assert rows == list(map(Q, r['row_sum_upper_rational']))
    q = max(rows)
    assert 0 <= q == Q(r['norm_upper_rational']) < 1
    cnorm = max(sum((abs(v) for v in row), Q(0)) for row in C)
    assert cnorm == Q(r['C_infinity_norm_rational'])
    assert cnorm/(1-q) == Q(r['inverse_norm_upper_rational'])
    assert Q(r['norm_upper_decimal_rounded_up']) >= q
    assert Q(r['inverse_norm_upper_decimal_rounded_up']) >= cnorm/(1-q)
    assert len(r['residual_rational_enclosure']) == 4
    assert r['residual_contains_zero'] == [True]*4
    assert all(Q(lo) <= 0 <= Q(hi) for lo, hi in r['residual_rational_enclosure'])
    assert r['status'] == 'PASS_EXTERNAL_UNIFORM_JACOBIAN_REGULARITY'
    return q


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('report', nargs='?', type=Path, default=DEFAULT)
    args = parser.parse_args()
    check(args.report)
    print('PASS exact rational matrix product, row bounds, strict contraction, input boxes and source hashes.')
    print('Analytic Jacobian enclosure remains EXTERNAL (SymPy/Arb); this is NOT a Lean proof.')


if __name__ == '__main__':
    main()
