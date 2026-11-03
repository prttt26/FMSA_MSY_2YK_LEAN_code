"""Exact Python mirror of the Lean executable checks.

It mirrors `ComplexTaylorCells.cellOK`, `M3MonodromyPath.slabOK` / `chainFrom` and
`M3TaylorRadius.seedOK` / `boxDisjoint`. Every operation is the same exact integer computation
in the same order as the Lean definitions, so that data can be validated before the kernel
spends time on it. The Lean kernel is the authority; this mirror only screens candidates.

Intervals are (lo, hi) integer pairs at scale S = 2**128. A complex box is (re, im). A cell is
dict(Y=[cbox]*4, C=[[cbox]*4]*4, X=[cbox]*4, T=cbox).
"""
S = 2 ** 128
G = 2 ** 40
W = [(0, 0), (-1332, 5185), (-1316, 5185), (-1316, 5201), (-1332, 5201), (-1332, 5185)]


# --- ScaledIntegerIntervals ---------------------------------------------------------------
def iadd(a, b): return (a[0] + b[0], a[1] + b[1])
def ineg(a): return (-a[1], -a[0])
def imul(a, b):
    p = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return (min(min(p[0], p[1]), min(p[2], p[3])) // S, -((-max(max(p[0], p[1]), max(p[2], p[3]))) // S))
def absUpper(a): return max(abs(a[0]), abs(a[1]))
def rational(n, d):  # Interval.rational s n d
    if d == 0: return (0, 0)
    return ((n * S) // d, -((-(n * S)) // d))


# --- ComplexTaylorModels -------------------------------------------------------------------
ZERO = ((0, 0), (0, 0))
ONE = ((S, S), (0, 0))
def cadd(A, B): return (iadd(A[0], B[0]), iadd(A[1], B[1]))
def cneg(A): return (ineg(A[0]), ineg(A[1]))
def cmul(A, B):
    return (iadd(imul(A[0], B[0]), ineg(imul(A[1], B[1]))), iadd(imul(A[0], B[1]), imul(A[1], B[0])))
def cofReal(I): return (I, (0, 0))
def cpow(A, n):
    r = ONE
    for _ in range(n): r = cmul(r, A)
    return r

def eadd(e, f):
    if not e: return list(f)
    if not f: return list(e)
    return [e[0] + f[0]] + eadd(e[1:], f[1:])
def unit(i): return [0] * i + [1]

def ins(e, A, t):
    out = []
    for k, (e2, B) in enumerate(t):
        if e == e2:
            return out + [(e2, cadd(B, A))] + t[k + 1:]
        out.append((e2, B))
    return out + [(e, A)]
def tnorm(t):
    acc = []
    for e, A in t: acc = ins(e, A, acc)
    return acc
def tadd(t, u): return tnorm(t + u)
def tneg(t): return [(e, cneg(A)) for e, A in t]
def tscale(A, t): return [(e, cmul(A, B)) for e, B in t]
def tmul(u, t): return tnorm([(eadd(p[0], q[0]), cmul(p[1], q[1])) for p in u for q in t])
def tconst(A): return [([], A)]
def tpow(t, n):
    r = tconst(ONE)
    for _ in range(n): r = tmul(r, t)
    return r
def shiftVar(Y, i): return [([], Y), (unit(i), ONE)]
def monoTM(Yf, o, e):
    if not e: return tconst(ONE)
    return tmul(tpow(shiftVar(Yf(o), o), e[0]), monoTM(Yf, o + 1, e[1:]))
def monoBox(e, B):
    if not e: return ONE
    return cmul(cpow(B(0), e[0]), monoBox(e[1:], lambda i: B(i + 1)))
def trange(B, t):
    acc = ZERO
    for e, A in t: acc = cadd(acc, cmul(A, monoBox(e, B)))
    return acc


# --- ComplexTaylorSpecs --------------------------------------------------------------------
def residTM(T, Yf, l):
    acc = []
    for e, b, I in l:
        acc = tadd(acc, tscale(cmul(cofReal(I), cpow(T, b)), monoTM(Yf, 0, e)))
    return acc
def getD(l, j): return l[j] if j < len(l) else 0
def decr(j, e):
    if not e: return []
    if j == 0: return [e[0] - 1] + e[1:]
    return [e[0]] + decr(j - 1, e[1:])
def natScale(k, I): return (k * I[0], k * I[1])
def derivI(j, l):
    return [(decr(j, e), b, natScale(getD(e, j), I)) for e, b, I in l if getD(e, j) != 0]


# --- ComplexTaylorCells --------------------------------------------------------------------
def getB(l, i): return l[i] if i < len(l) else ZERO
def cB(d, i, k): return getB(d['C'][i] if i < len(d['C']) else [], k)
def Yb(d, n, k): return getB(d['Y'], k) if k < n else ZERO
def hb(d, n, k): return cadd(getB(d['X'], k), cneg(getB(d['Y'], k))) if k < n else ZERO

def newtonTM(n, lI, d, i):
    acc = shiftVar(Yb(d, n, i), i)
    for k in range(n):
        acc = tadd(acc, tneg(tscale(cB(d, i, k), residTM(d['T'], lambda m: Yb(d, n, m), lI(k)))))
    return acc
def jacTM(n, lI, d, i, j):
    acc = tconst(ONE) if i == j else []
    for k in range(n):
        acc = tadd(acc, tneg(tscale(cB(d, i, k), residTM(d['T'], lambda m: Yb(d, n, m), derivI(j, lI(k))))))
    return acc
def ordered(A): return A[0] <= A[1]
def proper(A): return A[0] < A[1]
def inside(A, B): return B[0] <= A[0] and A[1] <= B[1]
def comp(b, A): return A[1] if b else A[0]
def width(d, b, j): c = comp(b, getB(d['X'], j)); return c[1] - c[0]
def entryU(E, b, b2): return absUpper(E[0] if b == b2 else E[1])
def rowSum(d, n, Es, b):
    return sum(sum(entryU(getB(Es, j), b, b2) * width(d, b2, j) for j in range(n)) for b2 in (False, True))
def rowOK(n, lI, d, i):
    Es = [trange(lambda k: hb(d, n, k), jacTM(n, lI, d, i, j)) for j in range(n)]
    return all(4 * rowSum(d, n, Es, b) <= 3 * width(d, b, i) * S for b in (False, True))
def mapOK(n, lI, d, i):
    r = trange(lambda k: hb(d, n, k), newtonTM(n, lI, d, i))
    X = getB(d['X'], i)
    return inside(r[0], X[0]) and inside(r[1], X[1])
def boxesOK(n, d, i):
    X, Y = getB(d['X'], i), getB(d['Y'], i)
    return (proper(X[0]) and proper(X[1]) and ordered(Y[0]) and ordered(Y[1]) and
            all(ordered(cB(d, i, k)[0]) and ordered(cB(d, i, k)[1]) for k in range(n)))
def cellOK(n, lI, d):
    return all(boxesOK(n, d, i) and mapOK(n, lI, d, i) and rowOK(n, lI, d, i) for i in range(n))


# --- M3MonodromyPath / M3TaylorRadius ------------------------------------------------------
def encQ(A, num, den): return A[0] * den <= num * S and num * S <= A[1] * den
def Wk(k): return W[k] if k < 5 else W[5]
def pin(T, k, s):
    a, b = Wk(k), Wk(k + 1)
    return encQ(T[0], a[0] * G + s * (b[0] - a[0]), 64 * G) and encQ(T[1], a[1] * G + s * (b[1] - a[1]), 64 * G)
def boxSub(n, A, B):
    return all(inside(getB(A['X'], i)[0], getB(B['X'], i)[0]) and inside(getB(A['X'], i)[1], getB(B['X'], i)[1])
               for i in range(n))
def slabOK(lI, x):
    return (x['seg'] < 5 and x['s0'] <= x['s1'] and x['s1'] <= G and cellOK(4, lI, x['cell']) and
            cellOK(4, lI, x['ends']) and pin(x['cell']['T'], x['seg'], x['s0']) and
            pin(x['cell']['T'], x['seg'], x['s1']) and pin(x['ends']['T'], x['seg'], x['s1']) and
            boxSub(4, x['ends'], x['cell']))
def posEq(p, q): return (p[0] == q[0] and p[1] == q[1]) or (p[0] + 1 == q[0] and p[1] == G and q[1] == 0)
def disjI(A, B): return A[1] < B[0] or B[1] < A[0]
def boxDisjoint(n, A, B):
    return any(disjI(getB(A['X'], i)[0], getB(B['X'], i)[0]) or disjI(getB(A['X'], i)[1], getB(B['X'], i)[1])
               for i in range(n))
def seedOK(d):
    X = lambda i: getB(d['X'], i)
    return (encQ(X(0)[0], 0, 1) and encQ(X(0)[1], 0, 1) and encQ(X(1)[0], 0, 1) and encQ(X(1)[1], 0, 1) and
            encQ(X(2)[0], 2064, 5000) and encQ(X(2)[0], 2065, 5000) and encQ(X(2)[1], 0, 1) and
            encQ(X(3)[0], 1286, 5000) and encQ(X(3)[0], 1287, 5000) and encQ(X(3)[1], 0, 1))


# --- M3TaylorSpec coefficient intervals ----------------------------------------------------
PHYS = [(1069028584064966747858780876442842309226, 1069028584064966747862183700112051693862),
        (108315241484954818046648587420924854560, 108315241484954818046993365542815312259),
        (310297353591408453456666808794198138, 310297353591408453463829122653711733),
        (282954560699298259517370576822755, 282954560699298259530432946503019),
        (258021160973090761041186135444, 258021160973090761059053144453),
        (235284843422800231064605145, 235284843422800231086328617)]

def expr_enclose(e):
    """Expr.enclose S physBounds for the tuple encoding produced by `parse_expr`."""
    k = e[0]
    if k == 'input': return PHYS[e[1]]
    if k == 'rational': return rational(e[1], e[2])
    if k == 'add': return iadd(expr_enclose(e[1]), expr_enclose(e[2]))
    if k == 'neg': return ineg(expr_enclose(e[1]))
    if k == 'mul': return imul(expr_enclose(e[1]), expr_enclose(e[2]))
    raise ValueError(e)

def parse_expr(s, i=0):
    """Parse the generated Lean `Expr 6` syntax: (.rational (p) q), (.input k), (.add a b), (.mul a b)."""
    def skip(i):
        while s[i] == ' ': i += 1
        return i
    i = skip(i)
    assert s[i] == '(', s[i:i + 20]
    i += 1
    if s.startswith('.rational', i):
        i = skip(i + len('.rational'))
        assert s[i] == '('; j = s.index(')', i); p = int(s[i + 1:j]); i = skip(j + 1)
        j = i
        while s[j].isdigit(): j += 1
        q = int(s[i:j]); i = skip(j); assert s[i] == ')'
        return ('rational', p, q), i + 1
    if s.startswith('.input', i):
        i = skip(i + len('.input')); j = i
        while s[j].isdigit(): j += 1
        k = int(s[i:j]); i = skip(j); assert s[i] == ')'
        return ('input', k), i + 1
    for op in ('add', 'mul'):
        if s.startswith('.' + op, i):
            a, i = parse_expr(s, i + len(op) + 1)
            b, i = parse_expr(s, i)
            i = skip(i); assert s[i] == ')'
            return (op, a, b), i + 1
    raise ValueError(s[i:i + 30])

def load_spec(path):
    """lI from the generated M3TaylorSpec.lean (the exact file the kernel uses)."""
    import re
    text = open(path).read()
    body = text.split('def specE : List (List (List ℕ × ℕ × Expr 6)) := [', 1)[1].split('\n\ndef lR', 1)[0]
    rows = []
    for row in body.strip()[1:-1].split('],\n    ['):
        entries = []
        for m in re.finditer(r'\(\[(\d), (\d), (\d), (\d)\], (\d), ', row):
            e, _ = parse_expr(row, m.end())
            entries.append(([int(m.group(k)) for k in range(1, 5)], int(m.group(5)), expr_enclose(e)))
        rows.append(entries)
    assert [len(r) for r in rows] == [6, 6, 9, 9], [len(r) for r in rows]
    return lambda k: rows[k] if k < len(rows) else []
