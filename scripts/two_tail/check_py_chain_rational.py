"""Standard-library re-check of results/two_tail/two_tail_py_chain_{M1,M3}.json.gz (rational part only).

Coordinates x = (Dt1, Dt2, G1, G2, tau); a witness with parameter index k has unknowns y = the other four.
From the stored (outward-rounded) Arb enclosures f, J_y, R_p it recomputes, in exact Fraction intervals,
every slab, link, switch and endpoint Krawczyk test in mean-value form,
    E = I - C J_y,  K = y~ - C f - (C R_p)(P - p~) + E (Y - y~),  q = max_i sum_j |E_ij| r_j / r_i,
and checks K strictly inside Y and q <= stored bound < 1.  For p slabs (k = 0) it recomputes the lower
bound of dtau/dp from d = -C R_p + E d and checks it is > 0.  Against the hash-checked endpoint
certificate it checks the exact data and bracket.  It also checks:
  * the tau slabs tile [0, tau_end] and the p slabs tile [p_0, p_end] exactly, every witness center
    parameter lies in its P;
  * every unknown center lies in its box; the source, generator/model and Lean hashes match;
  * without a switch, a tau slab ends exactly at tau_lo (with one, tau_s < tau_lo);
  * the seed enclosure (Dt = 0 exactly, tau = 0) lies inside the first box;
  * every link box (point parameter = the break) lies inside both neighbouring slab boxes; the
    switch box (fixed tau_s) lies inside the last tau slab and the first p slab;
  * A > 0 from exact endpoints on every tau slab ending at or before tau_lo and every p slab ending
    at or before p_star, with p_star >= the p range of the S_lo box and a p slab ending exactly at
    p_star;
  * the endpoint boxes (fixed tau_lo / tau_hi) lie inside their slab boxes, with A signs + and -.
"Inside" = slab parameter coordinate in the closed P, every other coordinate strictly inside Y.
It does NOT check the Arb enclosures (f, J_y, R_p, A, seed G) themselves.

Usage: python3 check_py_chain_rational.py JSON.gz
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
def add(a, b): return (a[0] + b[0], a[1] + b[1])
def sub(a, b): return (a[0] - b[1], a[1] - b[0])
def mul(a, b):
    p = (a[0]*b[0], a[0]*b[1], a[1]*b[0], a[1]*b[1]); return (min(p), max(p))
def pt(x): return (x, x)
def strict_in(i, o): return o[0] < i[0] and i[1] < o[1]
def mag(iv): return max(abs(iv[0]), abs(iv[1]))


def check(w):
    """Returns (ok, q, box5, k, dtau_lower or None)."""
    k = w['k']; U = [i for i in range(5) if i != k]
    xc = [P_(v) for v in w['c']]; C = [[P_(v) for v in r] for r in w['C']]
    Y = [I(v) for v in w['Y']]; P = I(w['P']); f = [I(v) for v in w['f']]
    Jy = [[I(v) for v in r] for r in w['Jy']]; Rp = [I(v) for v in w['Rp']]
    yc = [xc[j] for j in U]; pc = xc[k]
    ok = len(xc) == 5 and len(Y) == len(f) == len(Rp) == 4 and P[0] <= pc <= P[1] and all(y[0] < y[1] for y in Y)
    ok &= all(y[0] <= v <= y[1] for y, v in zip(Y, yc)) and len(C) == len(Jy) == 4 and all(len(r) == 4 for r in C + Jy)
    E = [[None]*4 for _ in range(4)]
    for i in range(4):
        for j in range(4):
            acc = pt(Q(int(i == j)))
            for m in range(4):
                acc = sub(acc, mul(pt(C[i][m]), Jy[m][j]))
            E[i][j] = acc
    dP = sub(P, pt(pc)); CRp = []
    for i in range(4):
        crp = pt(Q(0))
        for m in range(4):
            crp = add(crp, mul(pt(C[i][m]), Rp[m]))
        CRp.append(crp)
        acc = pt(yc[i])
        for m in range(4):
            acc = sub(acc, mul(pt(C[i][m]), f[m]))
        acc = sub(acc, mul(crp, dP))
        for j in range(4):
            acc = add(acc, mul(E[i][j], sub(Y[j], pt(yc[j]))))
        ok &= strict_in(acc, Y[i])
    r = [(y[1] - y[0])/2 for y in Y]
    q = max(sum((mag(E[i][j])*r[j] for j in range(4)), Q(0))/r[i] for i in range(4))
    ok &= q <= P_(w['q']) < 1
    dl = None
    if k == 0:
        d0 = max(mag(CRp[i])/r[i] for i in range(4))/(1 - q)
        dl = -CRp[3][1] - sum((mag(E[3][j])*r[j] for j in range(4)), Q(0))*d0
    B = [None]*5
    for a, j in enumerate(U):
        B[j] = Y[a]
    B[k] = P
    return ok, q, B, k, dl


def inside(Bz, Bs, k):
    return all((Bs[j][0] <= Bz[j][0] and Bz[j][1] <= Bs[j][1]) if j == k else strict_in(Bz[j], Bs[j]) for j in range(5))


def main():
    with gzip.open(sys.argv[1], 'rt') as fh:
        d = json.load(fh)
    ok = True
    raw = Path(d['source']).read_bytes(); ok &= hashlib.sha256(raw).hexdigest() == d['source_sha256']
    here = Path(__file__).resolve().parent
    pins = all(hashlib.sha256((here/n).read_bytes()).hexdigest() == h for n, h in d['script_sha256'].items()) and \
        all(hashlib.sha256((here.parents[2]/n).read_bytes()).hexdigest() == h for n, h in d['lean_sha256'].items())
    ok &= pins
    print(f'source, generator/model and Lean hashes match the files on disk: {pins and ok}')
    c = next(c for c in json.loads(raw)['controls'] if c['name'] == d['control'])
    tl, th = Q(c['rigorous_bracket']['lo']['tau']), Q(c['rigorous_bracket']['hi']['tau'])
    ok &= [Q(x) for x in d['bracket']] == [tl, th]
    ok &= (d['data']['z'], d['data']['w'], d['data']['eta']) == (c['z'], c['w'], c['eta'])
    sl = d['slabs']; res = [check(s['w']) for s in sl]
    ks = [r[3] for r in res]; Bs = [r[2] for r in res]
    ph = [s['phase'] for s in sl]
    ok &= all((p == 'tau') == (k == TAU) for p, k in zip(ph, ks)) and ph == sorted(ph, key=lambda p: p != 'tau')
    nt = ph.count('tau')
    ts = Q(d['tau_switch']) if d['tau_switch'] is not None else None
    tau_end = ts if ts is not None else th
    tile_t = Bs[0][TAU][0] == 0 and Bs[nt - 1][TAU][1] == tau_end and \
        all(Bs[j][TAU][1] == Bs[j + 1][TAU][0] for j in range(nt - 1))
    tile_p = all(Bs[j][0][1] == Bs[j + 1][0][0] for j in range(nt, len(sl) - 1))
    ok &= tile_t and tile_p and (ts is None) == (nt == len(sl)) and (ts is None or ts < tl)
    if ts is None:              # a tau slab must END exactly at tau_lo, so 'ends <= tau_lo' covers [0, tau_lo] (Codex 158)
        lo_break = any(Bs[j][TAU][1] == tl for j in range(nt))
        ok &= lo_break
        print(f'a tau slab ends exactly at tau_lo: {lo_break}')
    p_star = P_(d['p_star']) if d['p_star'] is not None else None
    if p_star is not None:      # a p slab must END exactly at p_star, so 'ends <= p_star' covers [p_0, p_star]
        star_break = any(Bs[j][0][1] == p_star for j in range(nt, len(sl)))
        ok &= star_break
        print(f'a p slab ends exactly at p_star: {star_break}')
    good, qmax, dmin = True, Q(0), None
    for s, (g, q, B, k, dl) in zip(sl, res):
        lim = tl if k == TAU else p_star
        need = B[k][1] <= lim
        g &= bool(s['A_required']) == need
        if need:
            g &= I(s['A'])[0] > 0
        if k == 0:
            g &= dl > 0; dmin = dl if dmin is None else min(dmin, dl)
        good &= g; qmax = max(qmax, q)
    ok &= good
    print(f'{len(sl)} slabs ({nt} tau, {len(sl) - nt} p): tau slabs tile [0, {float(tau_end)!r}] {tile_t}, p slabs '
          f'contiguous {tile_p}; every Krawczyk recomputed, K strictly in Y, q < 1, A > 0 where required'
          f'{", dtau/dp > 0 on every p slab" if dmin is not None else ""}: {good} (max q {float(qmax):.6f}'
          f'{f", min dtau/dp lower bound {float(dmin):.4e}" if dmin is not None else ""})')
    seed = [I(v) for v in d['seed']['enclosure']]
    sg = seed[0] == seed[1] == seed[4] == (0, 0) and inside(seed, Bs[0], TAU)
    ok &= sg; print(f'seed (Dt = 0, tau = 0) inside the first box: {sg}')
    pairs = [(j, j + 1) for j in range(len(sl) - 1) if j + 1 != nt]
    lk = len(d['links']) == len(pairs)
    for ln, (a, b) in zip(d['links'], pairs):
        g, _, Bz, kz, _ = check(ln['w'])
        g &= kz == ks[a] == ks[b] and Bz[kz] == (Bs[a][kz][1], Bs[a][kz][1]) and inside(Bz, Bs[a], kz) and inside(Bz, Bs[b], kz)
        lk &= g
    ok &= lk; print(f'{len(d["links"])} link boxes at the breaks: Krawczyk recomputed, inside both neighbouring boxes: {lk}')
    if ts is not None:
        g, _, Bz, kz, _ = check(d['switch']['w'])
        g &= kz == TAU and Bz[TAU] == (ts, ts) and Q(d['switch']['tau']) == ts and inside(Bz, Bs[nt - 1], TAU) and inside(Bz, Bs[nt], 0)
        ok &= g; print(f'switch box at tau_s = {float(ts)!r}: inside the last tau slab and the first p slab: {g}')
    for e, tau, want in (('lo', tl, '+'), ('hi', th, '-')):
        r = d['endpoints'][e]; j = r['slab']
        g, _, Bz, kz, _ = check(r['w'])
        g &= kz == TAU and Bz[TAU] == (tau, tau) and Q(r['tau']) == tau and inside(Bz, Bs[j], ks[j])
        A = I(r['A']); sign = '+' if A[0] > 0 else '-' if A[1] < 0 else '0?'
        g &= sign == want == r['detF0_sign']
        if e == 'lo' and p_star is not None:
            g &= Bz[0][1] <= p_star
        ok &= g; print(f'endpoint {e}: tiny box Krawczyk recomputed, inside slab {j}, A sign {sign}'
                       f'{", p range <= p_star" if e == "lo" and p_star is not None else ""}: {g}')
    print('ALL RATIONAL CHECKS PASS' if ok else 'A CHECK FAILED')
    return 0 if ok else 1


if __name__ == '__main__':
    assert __debug__, 'run without -O'
    sys.exit(main())
