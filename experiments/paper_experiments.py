#!/usr/bin/env python3
"""
Phase IV reproducible numerical experiments for the manuscript:
"Sharp Growth and Outlier-Robust Local Recovery in L1 Max-Linear Regression"

All random seeds are fixed for exact determinism. Saves output to
experiments/results/paper_experiments.json.

Experiments:
  A. Dimension & oversampling sweep (d in {5, 10, 20, 40}, m/d in {8, 16, 32, 64})
     measuring empirical local sharpness modulus at fixed macroscopic radius.
  B. Oblivious vs. omniscient outlier breakdown sweep (alpha in [0, 0.55])
     comparing Theorem 4's (1 - 2*alpha) scaling, Prop. 4.1' uniform-translation
     converse, and omniscient-location adversarial breakdown at alpha = 0.25.
  C. Separation scale Delta_min and condition number kappa = Delta_max / Delta_min
     invariance sweep (confirming Theorem 2's scale-free r=2 global sharpness and
     Theorem 4's zero-kappa dependence for r=3).
  D. Cone conditioning comparison: L1 alpha(C_p) = (1 - cos(pi*p))/sqrt(2*pi) vs
     L2 lambda_min(C_p) = p - sin(2*pi*p)/(2*pi) and PolyakSGM trajectories under
     0%, 20%, 30%, 40% gross outliers.
"""

import json
import os
import time
import numpy as np

RESULTS_PATH = os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "results", "paper_experiments.json"
)


def max_linear_pred(A, beta):
    return np.max(A @ beta.T, axis=1)


def l1_loss(A, y, beta):
    return float(np.mean(np.abs(y - max_linear_pred(A, beta))))


def empirical_local_sharpness(A, y, beta_star, radius, rng, n_dirs=600, n_radii=3):
    """
    Estimate min_{0 < ||Delta||_F <= radius} (f(beta* + Delta) - f(beta*)) / ||Delta||_F
    using random isotropic perturbations, single-block perturbations, and uniform translations.
    """
    r, d = beta_star.shape
    f0 = l1_loss(A, y, beta_star)
    radii = np.linspace(radius / n_radii, radius, n_radii)
    min_ratio = np.inf
    # 1. Isotropic random directions
    for _ in range(n_dirs):
        D = rng.normal(size=(r, d))
        D /= np.linalg.norm(D)
        for rad in radii:
            ratio = (l1_loss(A, y, beta_star + rad * D) - f0) / rad
            if ratio < min_ratio:
                min_ratio = ratio
    # 2. Single-block perturbations (often worst-case for cone conditioning)
    for j in range(r):
        for _ in range(60):
            u = rng.normal(size=d)
            u /= np.linalg.norm(u)
            D = np.zeros((r, d))
            D[j] = u
            for rad in radii:
                ratio = (l1_loss(A, y, beta_star + rad * D) - f0) / rad
                if ratio < min_ratio:
                    min_ratio = ratio
    # 3. Uniform translations (worst-case for Prop. 4.1' breakdown)
    for _ in range(80):
        h = rng.normal(size=d)
        h /= np.linalg.norm(h)
        D = np.tile(h, (r, 1)) / np.sqrt(r)
        for rad in radii:
            ratio = (l1_loss(A, y, beta_star + rad * D) - f0) / rad
            if ratio < min_ratio:
                min_ratio = ratio
    return float(min_ratio)


def make_regular_simplex_beta(r, d, sep=1.0):
    """Create r rows in R^d with all pairwise distances equal to `sep` (requires d >= r - 1)."""
    assert d >= r - 1
    # Standard simplex vertices in R^r projected to R^{r-1}
    V = np.eye(r) - np.ones((r, r)) / r
    Q, _ = np.linalg.qr(V[:, : r - 1])
    # Better: use SVD of centered identity
    U, S, _ = np.linalg.svd(V, full_matrices=False)
    coords = U[:, : r - 1] * S[: r - 1]
    # Current pairwise distance is sqrt(2); scale to `sep`
    coords = coords * (sep / np.sqrt(2.0))
    beta = np.zeros((r, d))
    beta[:, : r - 1] = coords
    return beta


def experiment_a_dimension_oversampling():
    """Dimension invariance of empirical sharpness modulus at fixed macroscopic radius."""
    rng = np.random.default_rng(20261120)
    r = 3
    sep = 1.0
    radius = 0.2 * sep
    dims = [5, 10, 20, 40]
    ratios = [8, 16, 32, 64]
    n_trials = 10
    results = []
    for d in dims:
        beta_star = make_regular_simplex_beta(r, d, sep=sep)
        for md in ratios:
            m = md * d
            vals = []
            for _ in range(n_trials):
                A = rng.normal(size=(m, d))
                y = max_linear_pred(A, beta_star)
                vals.append(empirical_local_sharpness(A, y, beta_star, radius, rng, n_dirs=250, n_radii=2))
            results.append({
                "d": d,
                "m": m,
                "m_over_d": md,
                "mean_mu": float(np.mean(vals)),
                "std_mu": float(np.std(vals)),
                "min_mu": float(np.min(vals)),
            })
    return {"r": r, "sep": sep, "radius": radius, "n_trials": n_trials, "grid": results}


def experiment_b_outlier_breakdown():
    """Oblivious (+1000 and Prop 4.1' translation) vs omniscient outlier breakdown sweep."""
    rng = np.random.default_rng(20261121)
    d = 10
    r = 3
    m = 500
    sep = 1.0
    radius = 0.15 * sep
    beta_star = make_regular_simplex_beta(r, d, sep=sep)
    alphas = [0.0, 0.10, 0.20, 0.30, 0.40, 0.45, 0.48, 0.50, 0.52, 0.55]
    n_trials = 12

    h_hat = np.zeros(d)
    h_hat[0] = 1.0

    oblivious_const_rows = []
    oblivious_trans_rows = []
    omniscient_rows = []

    for alpha in alphas:
        k_bad = int(round(alpha * m))
        mu_const = []
        mu_trans = []
        mu_omni = []
        for _ in range(n_trials):
            A = rng.normal(size=(m, d))
            y_clean = max_linear_pred(A, beta_star)

            # 1. Oblivious support (first k_bad indices), huge +1000 corruptions
            y1 = y_clean.copy()
            y1[:k_bad] += 1000.0
            mu_const.append(empirical_local_sharpness(A, y1, beta_star, radius, rng, n_dirs=200, n_radii=2))

            # 2. Oblivious support, Prop. 4.1' single fixed translation corruption xi_i = <a_i, h_hat>
            y2 = y_clean.copy()
            y2[:k_bad] += A[:k_bad] @ h_hat
            # Evaluate specifically along uniform translation t = 0.1 (exact Prop 4.1' direction)
            D_trans = np.tile(h_hat, (r, 1)) / np.sqrt(r)
            slope_trans = (l1_loss(A, y2, beta_star + 0.1 * D_trans) - l1_loss(A, y2, beta_star)) / 0.1
            mu_trans.append(float(slope_trans))

            # 3. Omniscient-location adversary: picks the k_bad samples with largest |<a_i, h_hat>|
            idx_omni = np.argsort(np.abs(A @ h_hat))[::-1][:k_bad]
            y3 = y_clean.copy()
            y3[idx_omni] += A[idx_omni] @ h_hat
            slope_omni = (l1_loss(A, y3, beta_star + 0.1 * D_trans) - l1_loss(A, y3, beta_star)) / 0.1
            mu_omni.append(float(slope_omni))

        oblivious_const_rows.append({
            "alpha": alpha,
            "mean_mu": float(np.mean(mu_const)),
            "min_mu": float(np.min(mu_const)),
        })
        oblivious_trans_rows.append({
            "alpha": alpha,
            "mean_slope": float(np.mean(mu_trans)),
            "theory_slope": float((1.0 - 2.0 * alpha) * np.sqrt(2.0 / np.pi) / np.sqrt(r)),
        })
        omniscient_rows.append({
            "alpha": alpha,
            "mean_slope": float(np.mean(mu_omni)),
            "max_slope": float(np.max(mu_omni)),
        })

    return {
        "d": d,
        "r": r,
        "m": m,
        "radius": radius,
        "n_trials": n_trials,
        "oblivious_plus1000": oblivious_const_rows,
        "oblivious_prop41_translation": oblivious_trans_rows,
        "omniscient_largest_leverage": omniscient_rows,
    }


def experiment_c_separation_and_kappa():
    """
    Verify:
    (1) Theorem 2 scale-free r=2 global sharpness across Delta_min in {0.01, 0.05, 0.2, 1.0, 5.0}.
    (2) Theorem 4 kappa-invariance for r=3 with kappa = Delta_max / Delta_min in {1, 5, 20, 100}
        while keeping cone probabilities balanced (beta_1 = -e_1, beta_2 = (1 + eps) e_1?
        Even cleaner: place beta_1, beta_2 at distance Delta_min and beta_3 orthogonal at distance
        kappa * Delta_min, wait: cone probabilities change unless beta_3 is on a symmetric ray —
        actually in R^3, if beta_1 = (0, 0, 0), beta_2 = (1, 0, 0), beta_3 = (0, L, 0):
        as L grows, pi_3 -> 1/2, pi_1 and pi_2 shrink slightly or stay bounded!
        Let's check exact cone probabilities pi_1, pi_2, pi_3 explicitly and report them!).
    """
    rng = np.random.default_rng(20261122)

    # Part 1: r = 2 scale-free global sharpness vs Delta_min
    d2 = 10
    m2 = 2000
    A2 = rng.normal(size=(m2, d2))
    r2_rows = []
    for sep in [0.01, 0.05, 0.2, 1.0, 5.0]:
        beta_star = np.zeros((2, d2))
        beta_star[0, 0] = sep / 2.0
        beta_star[1, 0] = -sep / 2.0
        y2 = max_linear_pred(A2, beta_star)
        # Global perturbations of size R = 1.0 (much larger than sep when sep = 0.01!)
        min_ratio = np.inf
        for _ in range(1000):
            D = rng.normal(size=(2, d2))
            D /= np.linalg.norm(D)
            for rad in [0.05, 0.5, 2.0]:
                beta = beta_star + rad * D
                dist = min(
                    np.linalg.norm(beta - beta_star),
                    np.linalg.norm(beta - beta_star[[1, 0]]),
                )
                ratio = l1_loss(A2, y2, beta) / dist
                if ratio < min_ratio:
                    min_ratio = ratio
        r2_rows.append({
            "Delta_min": sep,
            "empirical_global_mu": float(min_ratio),
            "theory_global_lb": float((np.sqrt(2.0) - 1.0) / np.sqrt(np.pi)),
        })

    # Part 2: r = 3 separation scale Delta_min invariance (at R = 0.15 * Delta_min)
    d3 = 10
    m3 = 600
    A3 = rng.normal(size=(m3, d3))
    r3_scale_rows = []
    for sep in [0.05, 0.2, 0.5, 1.0, 5.0]:
        beta_star = make_regular_simplex_beta(3, d3, sep=sep)
        y3 = max_linear_pred(A3, beta_star)
        mu_hat = empirical_local_sharpness(A3, y3, beta_star, 0.15 * sep, rng, n_dirs=400, n_radii=2)
        r3_scale_rows.append({
            "Delta_min": sep,
            "radius": 0.15 * sep,
            "empirical_mu": mu_hat,
        })

    # Part 3: r = 3 high condition number kappa = Delta_max / Delta_min
    # Use beta_1 = (0, 0, 0, ...), beta_2 = (1, 0, 0, ...), beta_3 = (0.5, -h, 0, ...) with h varying?
    # Better: in R^d, put beta_1 = (0, 1), beta_2 = (0, -1), beta_3 = (kappa, 0) shifted so origin is centroid?
    # No, active cones depend ONLY on differences beta_j - beta_k!
    # Check beta_1 = (0, 0), beta_2 = (eps, 0), beta_3 = (eps/2, 1):
    # Wait: a in C_1 <=> a_1 < 0 and (eps/2) a_1 + a_2 < 0 (prob ~ 1/4)
    #       a in C_2 <=> a_1 > 0 and -(eps/2) a_1 + a_2 < 0 (prob ~ 1/4)
    #       a in C_3 <=> a_2 > (eps/2)|a_1| (prob ~ 1/2)!
    # GENIUS!! As eps -> 0 (so kappa = ||beta_3 - beta_1|| / ||beta_2 - beta_1|| ~ 1/eps -> infinity!),
    # the three cone probabilities converge to (1/4, 1/4, 1/2) — ALL BOUNDED AWAY FROM ZERO!
    # So alpha_min stays O(1) even as kappa -> 100!
    r3_kappa_rows = []
    A_pop = rng.normal(size=(200000, d3))
    for kappa_target in [1.0, 5.0, 20.0, 100.0]:
        eps = 1.0 / kappa_target
        beta_star = np.zeros((3, d3))
        beta_star[0, 0] = -eps / 2.0
        beta_star[1, 0] = eps / 2.0
        beta_star[2, 1] = 1.0
        dists = [
            np.linalg.norm(beta_star[0] - beta_star[1]),
            np.linalg.norm(beta_star[0] - beta_star[2]),
            np.linalg.norm(beta_star[1] - beta_star[2]),
        ]
        dmin = float(min(dists))
        dmax = float(max(dists))
        kappa_exact = dmax / dmin
        # Estimate cone probabilities
        preds = A_pop @ beta_star.T
        winners = np.argmax(preds, axis=1)
        pis = [float(np.mean(winners == j)) for j in range(3)]
        y3 = max_linear_pred(A3, beta_star)
        mu_hat = empirical_local_sharpness(A3, y3, beta_star, 0.15 * dmin, rng, n_dirs=400, n_radii=2)
        r3_kappa_rows.append({
            "kappa": float(kappa_exact),
            "Delta_min": dmin,
            "Delta_max": dmax,
            "pi_min": float(min(pis)),
            "pis": pis,
            "radius": float(0.15 * dmin),
            "empirical_mu": mu_hat,
        })

    return {
        "r2_scale_free": r2_rows,
        "r3_scale_invariance": r3_scale_rows,
        "r3_kappa_invariance": r3_kappa_rows,
    }


def experiment_d_cone_conditioning_and_polyaksgm():
    """Exact L1 vs L2 cone curves (Prop 3.4) + PolyakSGM convergence trajectories under outliers."""
    ps = [0.02, 0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.40, 0.50]
    cone_curves = []
    for p in ps:
        alpha_l1 = float((1.0 - np.cos(np.pi * p)) / np.sqrt(2.0 * np.pi))
        lam_l2 = float(p - np.sin(2.0 * np.pi * p) / (2.0 * np.pi))
        bathtub_lb = float(np.sqrt(2.0 * np.pi) / 6.0 * (p ** 2))
        cone_curves.append({
            "p": p,
            "alpha_l1": alpha_l1,
            "lambda_l2": lam_l2,
            "bathtub_lb": bathtub_lb,
            "ratio_l1_over_p2": alpha_l1 / (p ** 2),
            "ratio_l2_over_p3": lam_l2 / (p ** 3),
        })

    # PolyakSGM trajectories for d = 20, r = 3, m = 500 under alpha in {0.0, 0.20, 0.30, 0.40}
    # Note: for alpha > 0, f(beta*) > 0 is known in the oracle-f* PolyakSGM test (evaluating
    # how the sharpness geometry drives linear convergence when f* = f(beta*)).
    rng = np.random.default_rng(20261123)
    d = 20
    r = 3
    m = 500
    beta_star = make_regular_simplex_beta(r, d, sep=1.0)
    A = rng.normal(size=(m, d))
    y_clean = max_linear_pred(A, beta_star)
    D0 = rng.normal(size=(r, d))
    D0 = 0.25 * D0 / np.linalg.norm(D0)
    beta_init = beta_star + D0

    trajectories = {}
    for alpha in [0.0, 0.20, 0.30, 0.40]:
        k_bad = int(round(alpha * m))
        y = y_clean.copy()
        signs = rng.choice([-1.0, 1.0], size=k_bad)
        y[:k_bad] += signs * 100.0
        f_star = l1_loss(A, y, beta_star)

        beta = beta_init.copy()
        dists = [float(np.linalg.norm(beta - beta_star))]
        for it in range(250):
            scores = A @ beta.T
            idx = np.argmax(scores, axis=1)
            yhat = scores[np.arange(m), idx]
            resid = yhat - y
            f_val = float(np.mean(np.abs(resid)))
            if f_val - f_star <= 1e-14:
                dists.append(float(np.linalg.norm(beta - beta_star)))
                break
            g = np.zeros_like(beta)
            sgn = np.sign(resid)
            for j in range(r):
                mask = idx == j
                if np.any(mask):
                    g[j] = (sgn[mask, None] * A[mask]).sum(axis=0) / m
            gnorm2 = float(np.sum(g * g))
            if gnorm2 < 1e-24:
                dists.append(float(np.linalg.norm(beta - beta_star)))
                break
            step = (f_val - f_star) / gnorm2
            beta = beta - step * g
            dists.append(float(np.linalg.norm(beta - beta_star)))
        # Sample every 10 iterations + final point for compact JSON / pgfplots
        sampled = [[i, dists[i]] for i in range(0, len(dists), 10)]
        if sampled[-1][0] != len(dists) - 1:
            sampled.append([len(dists) - 1, dists[-1]])
        trajectories[f"alpha_{int(round(alpha*100))}"] = {
            "alpha": alpha,
            "f_star": f_star,
            "n_iters": len(dists) - 1,
            "final_dist": dists[-1],
            "sampled_curve": sampled,
        }

    return {"cone_curves": cone_curves, "polyaksgm": trajectories}


def main():
    t0 = time.time()
    out = {
        "experiment_a_dim_oversampling": experiment_a_dimension_oversampling(),
        "experiment_b_outlier_breakdown": experiment_b_outlier_breakdown(),
        "experiment_c_sep_and_kappa": experiment_c_separation_and_kappa(),
        "experiment_d_cones_and_polyaksgm": experiment_d_cone_conditioning_and_polyaksgm(),
    }
    out["elapsed_sec"] = round(time.time() - t0, 2)
    with open(RESULTS_PATH, "w") as f:
        json.dump(out, f, indent=2)
    print(f"Saved paper experiments to {RESULTS_PATH} in {out['elapsed_sec']}s")
    print("\n--- Summary A (d vs m/d, r=3) ---")
    for row in out["experiment_a_dim_oversampling"]["grid"]:
        if row["m_over_d"] in (16, 32):
            print(f"  d={row['d']:2d}, m/d={row['m_over_d']:2d}: mean_mu={row['mean_mu']:.4f} (min={row['min_mu']:.4f})")
    print("\n--- Summary B (outlier alpha sweep) ---")
    for r1, r2, r3 in zip(
        out["experiment_b_outlier_breakdown"]["oblivious_plus1000"],
        out["experiment_b_outlier_breakdown"]["oblivious_prop41_translation"],
        out["experiment_b_outlier_breakdown"]["omniscient_largest_leverage"],
    ):
        print(
            f"  alpha={r1['alpha']:.2f} | obliv+1000 mu={r1['mean_mu']:+.4f} "
            f"| obliv_P41={r2['mean_slope']:+.4f} (th={r2['theory_slope']:+.4f}) "
            f"| omni={r3['mean_slope']:+.4f}"
        )
    print("\n--- Summary C3 (kappa invariance, r=3) ---")
    for row in out["experiment_c_sep_and_kappa"]["r3_kappa_invariance"]:
        print(f"  kappa={row['kappa']:6.2f}, pi_min={row['pi_min']:.4f}, emp_mu={row['empirical_mu']:.4f}")
    print("\n--- Summary D (PolyakSGM) ---")
    for k, v in out["experiment_d_cones_and_polyaksgm"]["polyaksgm"].items():
        print(f"  {k}: iters={v['n_iters']}, final_dist={v['final_dist']:.3e}")


if __name__ == "__main__":
    main()
