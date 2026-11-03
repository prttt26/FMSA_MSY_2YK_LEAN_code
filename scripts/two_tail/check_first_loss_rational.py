"""Standard-library re-check of results/two_tail/two_tail_first_loss_{M1,M3}.json.gz (rational part only).

It checks, with exact Fractions:
  * pins: the source, the chain record (sha256) and the generator/model/Lean files on disk;
  * the required slabs are exactly the chain slabs whose A > 0 covers [0, tau_lo] (tau slabs ending at or
    before tau_lo, p slabs ending at or before p_star), and every record's hull U contains the amplitude
    box of each of its member slabs;
  * per record: L2 >= rho_upper [ |qp|/12 + |A|/60 + sum_t (2|W_t|/z_t^3 + |C_t|(1/3 + 1/z_t + 2/z_t^2 + 2/z_t^3)) ]
    and B2 >= 2|qp| + |A| + sum_t z_t (|W_t| + |C_t|) from the stored upper bounds; the k march is strictly
    increasing with m_i > 0 and m_i - d_i h_i - L_i h_i^2/2 > 0, L_i = L2 at k_i = 0 and otherwise
    min(L2, H2(k_i)), H2 recomputed here from the stored bounds (formula in the generator docstring);
    a tail record reaches k >= K with
    rho_upper (|q0|/K + B2/K^2 + 2|A|/K^3) < 1/2;
  * coverage: for every required slab, the k ranges of the records containing it start at 0, are
    contiguous, and end in a tail record.
It does NOT check the Arb claims (m_i <= min |F|, d_i >= max |dF/dk|, the upper bounds |qp|, |A|, |W|, |C|,
|q0| over U, the rho enclosure), nor the chain itself (check_py_chain_rational.py).

Usage: python3 check_first_loss_rational.py JSON.gz
"""
import sys, json, hashlib, gzip
from fractions import Fraction as Q
from pathlib import Path

TAU = 4


def P_(s):
    if 'p' in s:
        m, e = s.split('p'); return Q(int(m))*Q(2)**int(e)
    return Q(s)
def I(s): return (P_(s[0]), P_(s[1]))


def H2(k, up, rho_u, zq):
    qp, A, W1, W2, C1, C2 = up
    s = qp*(1/k**2 + 6/k**3 + 12/k**4) + A*(2/k**3 + 12/k**4 + 24/k**5)
    for Wt, Ct, zt in ((W1, C1, zq[0]), (W2, C2, zq[1])):
        s += 2*Wt/k**3 + Ct*(zt/k**2 + (6 + 4*zt)/k**3 + 2*zt**2/k**4)
    return rho_u*s


def main():
    with gzip.open(sys.argv[1], 'rt') as fh:
        d = json.load(fh)
    ok = True
    here = Path(__file__).resolve().parent
    raw = Path(d['source']).read_bytes(); ok &= hashlib.sha256(raw).hexdigest() == d['source_sha256']
    craw = Path(d['chain']).read_bytes(); ok &= hashlib.sha256(craw).hexdigest() == d['chain_sha256']
    pins = all(hashlib.sha256((here/n).read_bytes()).hexdigest() == h for n, h in d['script_sha256'].items()) and \
        all(hashlib.sha256((here.parents[2]/n).read_bytes()).hexdigest() == h for n, h in d['lean_sha256'].items())
    ok &= pins
    print(f'source, chain, generator/model and Lean hashes match: {ok}')
    ch = json.loads(gzip.decompress(craw))
    c = next(c for c in json.loads(raw)['controls'] if c['name'] == ch['control'])
    ok &= d['control'] == ch['control'] and (d['data']['z'], d['data']['w'], d['data']['eta']) == (c['z'], c['w'], c['eta'])
    zq = [Q(x) for x in c['z']]; tl = Q(c['rigorous_bracket']['lo']['tau'])
    p_star = P_(ch['p_star']) if ch['p_star'] is not None else None
    rho_u = I(d['rho_enclosure'])[1]
    ok &= Q(3, 1)/Q(10, 1) < rho_u < 1                                      # 6*0.49/pi = 0.9358...
    # required slabs and their amplitude boxes
    boxes, req = {}, []
    for j, s in enumerate(ch['slabs']):
        w = s['w']; k = w['k']; P = I(w['P']); Y = [I(v) for v in w['Y']]
        B = [None]*5
        for a, jj in enumerate([i for i in range(5) if i != k]):
            B[jj] = Y[a]
        B[k] = P
        need = P[1] <= (tl if k == TAU else p_star)
        if need:
            req.append(j); boxes[j] = B[:4]
    ok &= req == d['required_slabs']
    print(f'{len(req)} required slabs = the chain slabs with A > 0 required on [0, tau_lo]: {req == d["required_slabs"]}')
    cover = {j: [] for j in req}
    good = True
    for r in d['records']:
        a, b = r['slabs']; U = [I(v) for v in r['U']]
        mem = [j for j in req if a <= j <= b]
        g = bool(mem) and all(all(U[i][0] <= boxes[j][i][0] and boxes[j][i][1] <= U[i][1] for i in range(4)) for j in mem)
        up = [P_(v) for v in r['up']]; qp, A, W1, W2, C1, C2 = up
        L2 = P_(r['L2']); B2 = P_(r['B2']); K = P_(r['K']); q0 = P_(r['q0'])
        s2 = qp/12 + A/60
        for Wt, Ct, zt in ((W1, C1, zq[0]), (W2, C2, zq[1])):
            s2 += 2*Wt/zt**3 + Ct*(Q(1, 3) + 1/zt + 2/zt**2 + 2/zt**3)
        g &= all(v >= 0 for v in up) and L2 >= rho_u*s2 and B2 >= 2*qp + A + zq[0]*(W1 + C1) + zq[1]*(W2 + C2)
        ks = [P_(v) for v in r['k']]; ms = [P_(v) for v in r['m']]; ds = [P_(v) for v in r['d']]
        g &= len(ks) == len(ms) + 1 == len(ds) + 1 and ks[0] >= 0
        for i in range(len(ms)):
            h = ks[i + 1] - ks[i]
            Li = L2 if ks[i] == 0 else min(L2, H2(ks[i], up, rho_u, zq))
            g &= h > 0 and ms[i] > 0 and ds[i] >= 0 and ms[i] - ds[i]*h - Li*h*h/2 > 0
        if r['tail']:
            g &= ks[-1] >= K > 0 and rho_u*(q0/K + B2/K**2 + 2*A/K**3) < Q(1, 2)
        good &= g
        for j in mem:
            cover[j].append((ks[0], ks[-1], r['tail']))
    ok &= good
    print(f'{len(d["records"])} records: hulls contain member boxes, L2/B2 bounds, every march step '
          f'm - d h - L2 h^2/2 > 0, tail bounds < 1/2: {good}')
    cov = True
    for j, iv in cover.items():
        iv.sort()
        if not iv or iv[0][0] != 0:
            cov = False; continue
        end, done = iv[0][1], iv[0][2]
        for a, b, t in iv[1:]:
            if not done and a > end:
                cov = False
            end = max(end, b); done = done or t
        cov &= done
    ok &= cov
    print(f'every required slab has k ranges from 0, contiguous, ending in a tail record: {cov}')
    print(f'k steps: {sum(len(r["m"]) for r in d["records"])}')
    print('ALL RATIONAL CHECKS PASS' if ok else 'A CHECK FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    assert __debug__, 'run without -O'
    sys.exit(main())
