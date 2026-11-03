"""Generate the Lean M3 slab-chain data modules from the published Codex monodromy witness.

Input: results/certificates/codex_m3_polygon_arb_witness.json.gz (hash-pinned in the output).
For every slab, the slab cell is the witness record rounded outward to the 2^128 grid. The
endpoint cell is the witness endpoint record, with its box widened by powers of two about its
centre until all three of these hold:
* the mirror of `cellOK` passes;
* the endpoint box lies in the slab box;
* the endpoint box lies in the next slab box.
Every check is screened with the exact mirror `m3_cell_mirror.py`. The Lean kernel re-checks
everything; nothing here is trusted.

Output (in --out, deliberately OUTSIDE the research package; user decision 2026-10-31):
* `ChunkNNN.lean`, CHUNK slabs each, each with one `decide +kernel`
  theorem;
* `Index.lean`, which assembles the chunks and proves the final M3
  radius theorem;
* `m3_chain_manifest.json`.

Usage: python3 scripts/m3_kernel/gen_m3_chain.py --out DIR [--chunk 20] [--limit-chunks K]
"""
import argparse, gzip, hashlib, json, sys, time
from fractions import Fraction as Q
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import m3_cell_mirror as M

ROOT = Path(__file__).resolve().parents[2]
WITNESS = ROOT / 'results/certificates/codex_m3_polygon_arb_witness.json.gz'
SPEC = ROOT / 'MSAConvergence/M3TaylorSpec.lean'
OUTDIR = None  # set from --out; the data is deliberately kept outside the research package
S, G = M.S, M.G


def fl(x): return (Q(x) * S).__floor__()
def ce(x): return (Q(x) * S).__ceil__()


def cell(rec, T, factor=1):
    X = []
    for B in rec['X']:
        comps = []
        for lo, hi in B:
            lo, hi = Q(lo), Q(hi)
            c, r = (lo + hi) / 2, (hi - lo) / 2 * factor
            comps.append((fl(c - r), ce(c + r)))
        X.append(tuple(comps))
    return dict(Y=[((fl(a), fl(a)), (fl(b), fl(b))) for a, b in rec['center']],
                C=[[((fl(a), fl(a)), (fl(b), fl(b))) for a, b in row] for row in rec['preconditioner']],
                X=X, T=T)


def rect(T): return ((fl(T[0][0]), ce(T[0][1])), (fl(T[1][0]), ce(T[1][1])))


def gam_point(seg, s):
    a, b = M.Wk(seg), M.Wk(seg + 1)
    den = Q(64 * G)
    return Q(a[0] * G + s * (b[0] - a[0])) / den, Q(a[1] * G + s * (b[1] - a[1])) / den


def lit_iv(I): return f'⟨{I[0]}, {I[1]}⟩'
def lit_cb(A):
    if A[0][0] == A[0][1] and A[1][0] == A[1][1]:
        return f'pt ({A[0][0]}) ({A[1][0]})'
    return f'bx ({A[0][0]}) ({A[0][1]}) ({A[1][0]}) ({A[1][1]})'
def lit_cell(d):
    Y = ', '.join(lit_cb(y) for y in d['Y'])
    C = ', '.join('[' + ', '.join(lit_cb(c) for c in row) + ']' for row in d['C'])
    X = ', '.join(lit_cb(x) for x in d['X'])
    return f'⟨[{Y}],\n      [{C}],\n      [{X}],\n      {lit_cb(d["T"])}⟩'
def lit_slab(x):
    return f'  ⟨{x["seg"]}, {x["s0"]}, {x["s1"]},\n    {lit_cell(x["cell"])},\n    {lit_cell(x["ends"])}⟩'


def chunk_file(i, base, slab_lits):
    """One chunk module: a def and a kernel theorem per slab, then the chunk theorem."""
    names = [f'slab{base + j:04d}' for j in range(len(slab_lits))]
    parts = []
    for n, lit in zip(names, slab_lits):
        parts.append(f'''def {n} : Slab :=
{lit}

set_option maxHeartbeats 0 in
-- Kernel evaluation of this slab's exact integer cell, path and box checks.
theorem {n}_ok : slabOK {n} = true := by decide +kernel
''')
    rest = ', '.join(names[1:])
    alls = ', '.join(f'{n}_ok' for n in names[1:])
    return f'''import MSAConvergence.M3MonodromyPath

/-! Generated M3 slab data, chunk {i} ({len(names)} slabs, {names[0]}–{names[-1]}). Do not edit:
produced by `scripts/m3_kernel/gen_m3_chain.py` from the published witness. Each slab theorem is
the kernel's exact integer check of that slab. The chunk theorem adds the junctions inside the
chunk. -/
noncomputable section
namespace FMSA.Convergence.M3ChainData
open ComplexTaylorCells M3MonodromyPath

{chr(10).join(parts)}
def chunk{i:03d} : List Slab := [{', '.join(names)}]

theorem chunk{i:03d}_ok : chainRest chunk{i:03d} = true :=
  chainRest_of_slabs {names[0]} [{rest}] {names[0]}_ok (by decide +kernel)
    (by simp only [List.all_cons, List.all_nil{', ' + alls if alls else ''}, Bool.and_true])

{guards([*names, f'chunk{i:03d}'])}end FMSA.Convergence.M3ChainData
'''


def guards(thms):
    """Axiom guards for the generated theorems. The footprint [propext, Quot.sound] was read from
    the compiler on a generated chunk; check_project.py re-checks every guard exactly."""
    ns = 'FMSA.Convergence.M3ChainData'
    return ''.join(f"/-- info: '{ns}.{n}_ok' depends on axioms: [propext, Quot.sound] -/\n"
                   f"#guard_msgs in\n#print axioms {ns}.{n}_ok\n" for n in thms)


def forall_chunks(names):
    """`∀ c ∈ [names], chainRest c = true` from the chunk theorems, as a nested term."""
    term = 'fun _ h => absurd h List.not_mem_nil'
    for n in reversed(names):
        term = f'List.forall_mem_cons.mpr ⟨{n}_ok,\n    {term}⟩'
    return term


def write_index(n0, total):
    names = [f'chunk{i:03d}' for i in range(total)]
    seg0, loop = names[1:n0], names[n0:]
    imports = ''.join(f'import MSAConvergence.M3ChainData.Chunk{i:03d}\n' for i in range(total))
    (OUTDIR / 'Index.lean').write_text(f'''import MSAConvergence.M3TaylorRadius
{imports}
/-! The M3 Taylor-radius bound, with every numerical step checked by the kernel.

Edge 0 is `chunk000` followed by `seg0Rest`; the loop is `loopChunks`. Each chunk's exact integer
checks are its own `chunkNNN_ok` theorem, by `decide +kernel`. Here only the junctions between
chunks and a few position, seed and disjointness facts are evaluated. Generated by
`scripts/m3_kernel/gen_m3_chain.py`. -/
noncomputable section
namespace FMSA.Convergence.M3ChainData
open Filter Topology
open FMSA.Paper FMSA.MatrixQ0 FMSA.ExactMSA.MultiTailMixture
open FMSA.Convergence.BHResidualPolynomials FMSA.Convergence.CanonicalNeighborhood
open ComplexTaylorCells M3MonodromyPath M3TaylorRadius M3ResidualModel

def seg0Rest : List (List Slab) := [{', '.join(seg0)}]
def loopChunks : List (List Slab) := [{', '.join(loop)}]
def chain0 : List Slab := chunk000 ++ seg0Rest.flatten
def loopChain : List Slab := loopChunks.flatten

theorem chain0_ok : chainRest chain0 = true :=
  chainRest_flatten chunk000 seg0Rest (by unfold chunk000; exact List.cons_ne_nil _ _) chunk000_ok
    (by decide +kernel)
    ({forall_chunks(seg0)})

theorem loop_ok : chainFrom (lastPosL chain0) (lastCellL chain0) loopChain = true :=
  chainFrom_flatten loopChunks _ _ (by decide +kernel)
    ({forall_chunks(loop)})

/-- **M3: the original HS germ has real coupling Taylor radius at most 84.** The series does not
converge, not even conditionally, at any real coupling with `|τ| > 84`. Every numerical step is
a kernel computation. -/
theorem m3_taylor_radius_le_84 :
    ∃ (p : ℝ → TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)
      (a : FormalMultilinearSeries ℝ ℝ (TailMatrix (Fin 2) 1 × TailMatrix (Fin 2) 1)),
      p 0 = (0, baseSeed z rho sigma) ∧ HasFPowerSeriesAt p a 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), IsRoot z rho sigma (t • strengths) (p t).1 (p t).2) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), p t ∈ canonicalAmplitudes z rho sigma) ∧
      a.radius ≤ ENNReal.ofReal 84 ∧ ∀ tau : ℝ, 84 < |tau| → ¬Summable (fun n => tau ^ n • a.coeff n) :=
  radius_of_chainL chain0 loopChain chain0_ok loop_ok (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end FMSA.Convergence.M3ChainData
''')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--chunk', type=int, default=20)
    ap.add_argument('--limit-chunks', type=int, default=0)
    ap.add_argument('--out', required=True, help='output directory, outside MSAConvergence/')
    args = ap.parse_args()
    global OUTDIR
    OUTDIR = Path(args.out).resolve()
    assert ROOT / 'MSAConvergence' not in [OUTDIR, *OUTDIR.parents], 'keep the data out of the package'
    t0 = time.time()
    lI = M.load_spec(SPEC)
    w = json.loads(gzip.decompress(WITNESS.read_bytes()))
    recs = [(k, r) for k, seg in enumerate(w['segments']) for r in seg['slabs']]
    slabs = [None] * len(recs)
    for idx, (k, r) in enumerate(recs):
        s0, s1 = (Q(v) * G for v in r['s'])
        assert s0.denominator == 1 and s1.denominator == 1
        slabs[idx] = dict(seg=k, s0=int(s0), s1=int(s1), cell=cell(r, rect(r['T'])))
    factors = []
    for idx, (k, r) in enumerate(recs):
        x = slabs[idx]
        p = gam_point(k, x['s1'])
        T = ((p[0] * S).__floor__(), (p[0] * S).__ceil__()), ((p[1] * S).__floor__(), (p[1] * S).__ceil__())
        nxt = slabs[idx + 1]['cell'] if idx + 1 < len(slabs) else None
        f = 1
        while True:
            e = cell(r['endpoint'], T, f)
            if M.cellOK(4, lI, e) and M.boxSub(4, e, x['cell']) and (nxt is None or M.boxSub(4, e, nxt)):
                break
            f *= 2
            assert f <= 2 ** 24, ('endpoint widening failed', idx)
        x['ends'] = e
        factors.append(f)
        assert M.slabOK(lI, x), ('slab check failed', idx)
        if idx % 500 == 0:
            print(f'slab {idx}/{len(recs)} factor {f} {time.time() - t0:.0f}s', flush=True)
    # chain junctions, seed, loop
    p, E = (0, 0), slabs[0]['cell']
    for x in slabs:
        assert M.posEq(p, (x['seg'], x['s0'])) and M.boxSub(4, E, x['cell'])
        p, E = (x['seg'], x['s1']), x['ends']
    seg0 = [x for x in slabs if x['seg'] == 0]
    assert slabs[:len(seg0)] == seg0 and (seg0[-1]['seg'], seg0[-1]['s1']) == (0, G) and p == (4, G)
    assert M.seedOK(slabs[0]['cell']) and slabs[0]['s0'] == 0
    assert M.boxDisjoint(4, seg0[-1]['ends'], slabs[-1]['ends'])
    # chunks: segment 0 and the loop are chunked separately so the split is at a chunk boundary
    def chunked(l): return [l[i:i + args.chunk] for i in range(0, len(l), args.chunk)]
    chunks0, chunks1 = chunked(seg0), chunked(slabs[len(seg0):])
    chunks = chunks0 + chunks1
    if args.limit_chunks:
        chunks = chunks[:args.limit_chunks]
    OUTDIR.mkdir(exist_ok=True)
    for old in OUTDIR.glob('Chunk*.lean'):
        old.unlink()
    base = 0
    for i, c in enumerate(chunks):
        (OUTDIR / f'Chunk{i:03d}.lean').write_text(chunk_file(i, base, [lit_slab(x) for x in c]))
        base += len(c)
    write_index(len(chunks0), len(chunks)) if not args.limit_chunks else None
    manifest = dict(
        command=' '.join(sys.argv), witness=str(WITNESS.relative_to(ROOT)),
        witness_sha256=hashlib.sha256(WITNESS.read_bytes()).hexdigest(),
        spec_sha256=hashlib.sha256(SPEC.read_bytes()).hexdigest(),
        slabs=len(slabs), chunk_size=args.chunk, chunks=len(chunks), seg0_chunks=len(chunks0),
        endpoint_widening_max=max(factors),
        endpoint_widening_histogram={str(f): factors.count(f) for f in sorted(set(factors))},
        mirror_seconds=round(time.time() - t0, 1),
        label='Lean data; every check is re-done by the kernel (decide +kernel).')
    (OUTDIR / 'm3_chain_manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(manifest, indent=2))


if __name__ == '__main__':
    assert __debug__
    main()
