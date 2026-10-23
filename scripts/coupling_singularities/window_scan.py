"""Fine scan of w in [-2.640, -2.630] (z = (1.8, 12), eta = 0.3): the window where a real
fold exists but the nearest complex physical-sheet fold is closer."""
import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

sys.path.insert(0, str(Path(__file__).resolve().parent))
from family_crossing import OUT, real_fold, series_radius, state  # noqa: E402
from nearest import continue_path, on_sheet, refine_fold  # noqa: E402

rows = []
st = state(-2.630); t = complex(-2.79657, 6.48256)
u = continue_path(st, [0.0, 0.97*t]); u, t, _ = refine_fold(st, u, t)
for w in np.arange(-2.6300, -2.64001, -0.0005):
    st = state(w)
    u, t, res = refine_fold(st, u, t)
    tf = real_fold(w, lam_max=80.0)
    pred = min(abs(t), tf) if tf else abs(t)
    Rs = series_radius(st, 0.9*pred)
    rows.append(dict(w=float(w), tau_f=tf, abs_tau_c=abs(t), tau_c=[t.real, t.imag], R_pred=pred,
                     binding=('fold' if tf and tf < abs(t) else 'complex'), R_series=Rs))
    print(f"w={w:+.4f}: tau_f={'none' if tf is None else '%.5f' % tf:>8}  |tau*_c|={abs(t):.5f}  "
          f"binding={rows[-1]['binding']:7s}  R_pred={pred:.5f}  R_series(60,70,80)={np.round(Rs, 4)}", flush=True)
(OUT/'window_scan.json').write_text(json.dumps(rows, indent=1))
