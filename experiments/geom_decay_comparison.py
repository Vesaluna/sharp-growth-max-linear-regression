"""
Geometric Step-Decay Subgradient Method (f(beta*)-free) vs. Oracle-f(beta*) PolyakSGM
on the exact Experiment D benchmark (d = 20, r = 3, m = 500, +-100 oblivious outliers).

IMPORTANT HONESTY NOTE:
- Both methods start from the SAME local initialization beta^(0) = beta* + D_0 with
  ||D_0||_F = 0.25 (so initialization itself uses beta*, matching Experiment D).
- PolyakSGM uses the oracle objective value f(beta*) in its step size
  (f(beta^(k)) - f(beta*)) / ||g^(k)||_F^2. (Note: for alpha > 0, f(beta*) > 0 is
  the empirical risk at beta*, NOT necessarily the global minimum f*.)
- GeomDecaySGM uses NO knowledge of f(beta*) or f*: it takes normalized subgradient
  steps beta^(k+1) = beta^(k) - lambda_0 * q^k * g^(k) / ||g^(k)||_F with a single
  fixed schedule (lambda_0, q) shared across all alpha values and all seeds.
- This script is purely an empirical illustration of local sharpness geometry and
  does NOT constitute a proved convergence theorem.
"""

import json
import os
import time
import numpy as np

RESULTS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "results",
    "geom_decay_comparison.json",
)


def make_regular_simplex_beta(r: int, d: int, sep: float = 1.0) -> np.ndarray:
    """Embed r regular-simplex vertices with pairwise Euclidean distance `sep` in R^d."""
    assert r - 1 <= d
    M = np.eye(r) - np.ones((r, r)) / r
    U, s, _ = np.linalg.svd(M)
    coords = U[:, : r - 1] * s[: r - 1]
    cur_dist = np.linalg.norm(coords[0] - coords[1])
    coords = coords * (sep / cur_dist)
    beta = np.zeros((r, d))
    beta[:, : r - 1] = coords
    return beta


def max_linear_pred(A: np.ndarray, beta: np.ndarray) -> np.ndarray:
    return np.max(A @ beta.T, axis=1)


def l1_loss(A: np.ndarray, y: np.ndarray, beta: np.ndarray) -> float:
    return float(np.mean(np.abs(y - max_linear_pred(A, beta))))


def subgrad_and_loss(A: np.ndarray, y: np.ndarray, beta: np.ndarray):
    m = A.shape[0]
    r = beta.shape[0]
    scores = A @ beta.T
    idx = np.argmax(scores, axis=1)
    yhat = scores[np.arange(m), idx]
    resid = yhat - y
    f_val = float(np.mean(np.abs(resid)))
    g = np.zeros_like(beta)
    sgn = np.sign(resid)
    for j in range(r):
        mask = idx == j
        if np.any(mask):
            g[j] = (sgn[mask, None] * A[mask]).sum(axis=0) / m
    return f_val, g


def run_polyak(A, y, beta_star, beta_init, n_iters=250):
    f_beta_star = l1_loss(A, y, beta_star)
    beta = beta_init.copy()
    dists = [float(np.linalg.norm(beta - beta_star))]
    for _ in range(n_iters):
        f_val, g = subgrad_and_loss(A, y, beta)
        if f_val - f_beta_star <= 1e-14:
            dists.append(float(np.linalg.norm(beta - beta_star)))
            break
        gnorm2 = float(np.sum(g * g))
        if gnorm2 < 1e-24:
            dists.append(float(np.linalg.norm(beta - beta_star)))
            break
        step = (f_val - f_beta_star) / gnorm2
        beta = beta - step * g
        dists.append(float(np.linalg.norm(beta - beta_star)))
    return dists, f_beta_star


def run_geom_decay(A, y, beta_star, beta_init, lam0=0.04, q=0.95, n_iters=250):
    """Normalized geometric step-decay subgradient method (uses NO f(beta*) or f*)."""
    beta = beta_init.copy()
    dists = [float(np.linalg.norm(beta - beta_star))]
    step = lam0
    for _ in range(n_iters):
        _, g = subgrad_and_loss(A, y, beta)
        gnorm = float(np.linalg.norm(g))
        if gnorm < 1e-15:
            dists.append(float(np.linalg.norm(beta - beta_star)))
            break
        beta = beta - step * (g / gnorm)
        step *= q
        dists.append(float(np.linalg.norm(beta - beta_star)))
    return dists


def sample_curve(dists):
    sampled = [[i, dists[i]] for i in range(0, len(dists), 10)]
    if sampled[-1][0] != len(dists) - 1:
        sampled.append([len(dists) - 1, dists[-1]])
    return sampled


def main():
    t0 = time.time()
    d, r, m = 20, 3, 500
    n_iters = 250
    alphas = [0.0, 0.20, 0.30, 0.40]
    seeds = [20261123, 20261124, 20261125, 20261126, 20261127]
    # Single fixed schedule shared across all alpha and all seeds (no per-alpha tuning)
    lam0 = 0.04
    q = 0.95

    beta_star = make_regular_simplex_beta(r, d, sep=1.0)
    per_seed = {}
    exp_d_exact = {}

    for seed in seeds:
        rng = np.random.default_rng(seed)
        A = rng.normal(size=(m, d))
        y_clean = max_linear_pred(A, beta_star)
        D0 = rng.normal(size=(r, d))
        D0 = 0.25 * D0 / np.linalg.norm(D0)
        beta_init = beta_star + D0

        seed_res = {}
        for alpha in alphas:
            k_bad = int(round(alpha * m))
            y = y_clean.copy()
            signs = rng.choice([-1.0, 1.0], size=k_bad)
            y[:k_bad] += signs * 100.0

            p_dists, f_bstar = run_polyak(A, y, beta_star, beta_init, n_iters=n_iters)
            g_dists = run_geom_decay(A, y, beta_star, beta_init, lam0=lam0, q=q, n_iters=n_iters)

            key = f"alpha_{int(round(alpha * 100))}"
            entry = {
                "alpha": alpha,
                "f_beta_star": f_bstar,
                "polyak_n_iters": len(p_dists) - 1,
                "polyak_final_dist": p_dists[-1],
                "geom_n_iters": len(g_dists) - 1,
                "geom_final_dist": g_dists[-1],
            }
            seed_res[key] = entry
            if seed == 20261123:
                exp_d_exact[key] = {
                    **entry,
                    "polyak_curve": sample_curve(p_dists),
                    "geom_curve": sample_curve(g_dists),
                }
        per_seed[str(seed)] = seed_res

    summary = {}
    for alpha in alphas:
        key = f"alpha_{int(round(alpha * 100))}"
        p_vals = [per_seed[str(s)][key]["polyak_final_dist"] for s in seeds]
        g_vals = [per_seed[str(s)][key]["geom_final_dist"] for s in seeds]
        summary[key] = {
            "alpha": alpha,
            "polyak_median": float(np.median(p_vals)),
            "polyak_min": float(np.min(p_vals)),
            "polyak_max": float(np.max(p_vals)),
            "geom_median": float(np.median(g_vals)),
            "geom_min": float(np.min(g_vals)),
            "geom_max": float(np.max(g_vals)),
        }

    out = {
        "config": {
            "d": d,
            "r": r,
            "m": m,
            "init_dist": 0.25,
            "outlier_magnitude": 100.0,
            "n_iters": n_iters,
            "seeds": seeds,
            "geom_schedule": {"lam0": lam0, "q": q},
        },
        "exp_d_seed_20261123": exp_d_exact,
        "multi_seed_summary": summary,
        "per_seed": per_seed,
        "elapsed_sec": round(time.time() - t0, 2),
    }
    os.makedirs(os.path.dirname(RESULTS_PATH), exist_ok=True)
    with open(RESULTS_PATH, "w") as f:
        json.dump(out, f, indent=2)

    print(f"Saved geometric decay comparison to {RESULTS_PATH} in {out['elapsed_sec']}s")
    print(f"\nSchedule: lam0={lam0}, q={q}, n_iters={n_iters}, seeds={seeds}")
    print("\n--- Seed 20261123 (exact Experiment D draw) ---")
    for k, v in exp_d_exact.items():
        print(
            f"  {k}: Polyak(oracle f(beta*))={v['polyak_final_dist']:.3e} ({v['polyak_n_iters']} iters) | "
            f"GeomDecay(no f(beta*))={v['geom_final_dist']:.3e}"
        )
    print("\n--- 5-Seed Summary (final ||beta^(250) - beta*||_F) ---")
    for k, v in summary.items():
        print(
            f"  {k}: Polyak med={v['polyak_median']:.3e} [{v['polyak_min']:.2e}, {v['polyak_max']:.2e}] | "
            f"GeomDecay med={v['geom_median']:.3e} [{v['geom_min']:.2e}, {v['geom_max']:.2e}]"
        )


if __name__ == "__main__":
    main()
