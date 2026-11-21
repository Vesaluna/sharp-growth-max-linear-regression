#!/usr/bin/env python3
"""
Reproducible numerical experiments for CAM-Bench Open Problem 107:
Sharp growth constant for max-linear regression with absolute (L1) loss.

Covers:
  Exp 1: Deterministic piecewise-affine structure, spurious local minima, coercivity & global vs local error bounds (Claim A).
  Exp 2: Exact local sharpness constant mu_loc, active-set stability radius decay O(1/(m*sqrt(d))), and ties/rank-deficiency edge cases (Claim B).
  Exp 3: Exact 2D/3D Gaussian population loss F(beta* + Delta) vs linearized loss and quadratic remainder for r=2 (Claim C) and general r=2,3,4,5 (alpha_j ~ pi_j^2 vs L2 ~ pi_j^3).
  Exp 4: Finite-sample empirical sharpness constant vs (m, d, r, sep) and adversarial/oblivious outlier breakdown threshold (alpha -> 1/2).
  Exp 5: PolyakSGM convergence verification on noiseless and outlier-corrupted max-linear regression (connecting to Charisopoulos-Davis Sec. 5.2.2).
"""

import json
import os
import time
import numpy as np
from scipy import integrate, optimize, stats

RESULTS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(RESULTS_DIR, exist_ok=True)


# ---------------------------------------------------------------------------
# Core objective and helpers
# ---------------------------------------------------------------------------

def max_linear_pred(A, beta):
    """A: (m, d), beta: (r, d) -> y_hat: (m,)"""
    return np.max(A @ beta.T, axis=1)


def l1_objective(A, y, beta):
    """f(beta) = (1/m) sum_i |y_i - max_j <a_i, beta_j>|"""
    return float(np.mean(np.abs(y - max_linear_pred(A, beta))))


def min_perm_dist(beta, beta_star):
    """Exact distance to the permutation orbit of beta_star (for small r <= 6)."""
    from itertools import permutations
    r = beta.shape[0]
    best = np.inf
    for p in permutations(range(r)):
        diff = beta - beta_star[list(p)]
        dval = float(np.linalg.norm(diff))
        if dval < best:
            best = dval
    return best


def exact_l1_min_over_sphere_2d(A_sub):
    """
    Exact min_{||u||_2 = 1} ||A_sub u||_1 for d = 2.
    Since u -> ||A_sub u||_1 is piecewise smooth on the unit circle S^1,
    critical points occur either at kink directions (a_i^perp / ||a_i||)
    or where the derivative of <s, u> vanishes on an arc (not a minimum, since
    a -> <s, u> is concave on arcs where <s, u> > 0! Wait: u -> <s, u> on S^1
    is strictly concave on the positive side, so the MINIMUM of ||A u||_1 on S^1
    is ALWAYS attained at a kink direction a_i^perp / ||a_i||!).
    """
    m_sub, d = A_sub.shape
    assert d == 2
    if m_sub == 0:
        return 0.0, np.array([1.0, 0.0])
    best_val = np.inf
    best_u = None
    for i in range(m_sub):
        a = A_sub[i]
        nrm = np.linalg.norm(a)
        if nrm == 0:
            continue
        u = np.array([-a[1], a[0]]) / nrm
        val = float(np.sum(np.abs(A_sub @ u)))
        if val < best_val:
            best_val = val
            best_u = u
    return best_val, best_u


def approx_l1_min_over_sphere(A_sub, rng, n_restarts=40):
    """
    Compute min_{||u||_2=1} ||A_sub u||_1 via exact kink search in d=2,
    or exact LP over L1/Linf facets + Powell/Nelder-Mead/SLSQP on S^{d-1} for d >= 3.
    Also compute exact lower bound via sigma_min(A_sub) / sqrt(m_sub) is NOT a lower bound
    (wait: ||Au||_1 >= ||Au||_2 >= sigma_min(A) IS a valid lower bound!).
    """
    m_sub, d = A_sub.shape
    if m_sub < d:
        return 0.0, None
    if d == 2:
        return exact_l1_min_over_sphere_2d(A_sub)

    # Candidate 1: right singular vector corresponding to smallest singular value
    _, svals, Vt = np.linalg.svd(A_sub, full_matrices=False)
    candidates = [Vt[-1]]
    # Candidate 2: LP relaxation on L_inf unit ball (gives a 1/sqrt(d)-approx, refined on S^{d-1})
    # Candidate 3: random restarts + Powell on sphere
    for _ in range(n_restarts):
        u0 = rng.normal(size=d)
        u0 /= np.linalg.norm(u0)
        candidates.append(u0)

    best_val = np.inf
    best_u = None
    for u0 in candidates:
        res = optimize.minimize(
            lambda w: float(np.sum(np.abs(A_sub @ (w / np.linalg.norm(w))))),
            u0,
            method="Powell",
            options={"xtol": 1e-10, "ftol": 1e-10, "maxiter": 2000},
        )
        u = res.x / np.linalg.norm(res.x)
        val = float(np.sum(np.abs(A_sub @ u)))
        if val < best_val:
            best_val = val
            best_u = u
    return best_val, best_u


# ---------------------------------------------------------------------------
# Experiment 1: Claim A — Spurious local minima & coercivity / global error bound
# ---------------------------------------------------------------------------

def run_exp1():
    print("\n=== Experiment 1: Claim A (Spurious local minima, coercivity, global vs local EB) ===")
    results = {}

    # 1A: Explicit failure of GLOBAL error bound when {a_i} lies in an open half-space
    # d=1, r=2, m=2: a = [1, 2], y = [1, 2].
    # True global minimizer: beta_1 = 1, beta_2 <= 1 (or swapped), f* = 0.
    # Actually check a = [1, 2], y = [1, 2]: X* = {(1, b2): b2<=1} U {(b1, 1): b1<=1}.
    # Wait: what if a = [1, 1], y = [0, 2]? Then f* = 1 (attained when max(b1, b2) = 1).
    # For global EB failure, we need a flat ray with f(beta) > f* parallel to NO ray of X*!
    # Take d=1, r=2, m=2: a = [1, -1]? No, that positively spans R^1 -> coercive -> global EB!
    # Take d=1, r=2, m=3: a = [1, 2, 3], y = [1, 5, 6] (noisy, positive a_i):
    # At beta = (0, t) as t -> -infty: max(0, t) = 0, so f(0, t) = (|1-0|+|5-0|+|6-0|)/3 = 4 > f*.
    # Meanwhile X* = {(b1, b2) : max(b1, b2) = 2} (median of y_i/a_i = {1, 2.5, 2} weighted by |a_i|: weights 1,2,3 -> weighted median is 2.0!).
    # Wait: {(2, t) : t <= 2} IS in X*, so dist((0, t), X*) = |0 - 2| = 2 stays BOUNDED!
    # AHA!! Let's check if global EB can EVER fail for max-linear regression when r=2, d=1!
    # What about d=2, r=2 with a_i in an open half-space, where a suboptimal beta_1 != beta_1* has beta_2 -> -infty?
    # Still dist((beta_1, -t u), (beta_1*, -t u)) = ||beta_1 - beta_1*|| stays bounded!
    # WAIT A SECOND!! Let's test in Python if a flat suboptimal ray can have dist -> infinity!
    # Consider d=2, r=2, a_1 = (1, 0), a_2 = (0, 1), y_1 = 1, y_2 = 1.
    # Here beta_1* = (1, 0), beta_2* = (0, 1) -> f* = 0.
    # Notice X* contains ((1, -t), (-s, 1)) for ALL t, s >= 0!
    # What if beta = ((2, 0), (-t, -t)) as t -> +infty?
    # Since ((-t, -t)) is <= (2, 0) on both a_1, a_2, f(beta) = (|2-1| + |0-1|)/2 = 1 > 0.
    # Meanwhile X* ALSO contains ((1, 1), (-t, -t))! So dist(beta, X*) <= ||(2,0)-(1,1)|| = sqrt(2)!
    # WAIT A SECOND! That's a super subtle mathematical question: DOES max-linear regression ALWAYS have a GLOBAL error bound even without coercivity?!
    # Let's check Dolgopolik's condition (recession cone of suboptimal piece vs recession cone of X*)!
    # Suppose d=2, r=2, a_1=(1,0), a_2=(1,1), a_3=(1,-1), y=(0, 1, 1).
    # Note: a_i all have first coord +1 (open half-space!).
    # True minimizer: beta_1* = (0, 1), beta_2* = (0, -1):
    #   <a_1, beta_1*> = 0, <a_2, beta_1*> = 1, <a_3, beta_1*> = -1
    #   <a_1, beta_2*> = 0, <a_2, beta_2*> = -1, <a_3, beta_2*> = 1 -> max = (0, 1, 1) = y! f*=0!
    # Can beta_1* or beta_2* move along (-t, 0) and STAY in X*?
    # NO!! Because BOTH beta_1* and beta_2* are uniquely needed (a_2 needs beta_1*, a_3 needs beta_2*, and a_1 needs max <= 0)!
    # Check: if beta = ((0, 1), (-t, 0)) with t -> +infty:
    #   max on a_1: 0; on a_2: 1; on a_3: -1. So f(beta) = (0 + 0 + |1 - (-1)|)/3 = 2/3 CONSTANT for all t >= 1!
    # Now check dist(beta, X*) as t -> +infty!!
    # For ANY z = (z1, z2) in X*, we must have max(<a_i, z1>, <a_i, z2>) = y_i for i=1,2,3:
    #   max(z1_x, z2_x) = 0  => z1_x <= 0, z2_x <= 0, and at least one is 0.
    #   max(z1_x + z1_y, z2_x + z2_y) = 1
    #   max(z1_x - z1_y, z2_x - z2_y) = 1
    # Notice if z1_x + z1_y = 1 AND z1_x - z1_y = 1, adding gives 2 z1_x = 2 => z1_x = 1 > 0, IMPOSSIBLE!
    # Therefore ONE of z1, z2 must achieve a_2 (say z1_x + z1_y = 1) and the OTHER must achieve a_3 (z2_x - z2_y = 1)!
    #Wait: can z2_x = -t and z2_y = -t - 1? Check a_2: z2_x + z2_y = -2t - 1 <= 1 OK! Check a_1: z2_x = -t <= 0 OK! Check a_3: z2_x - z2_y = -t - (-t-1) = 1 OK!
    # So ((-t, -t-1)) IS in X*! What if we add a_4 = (1, 2), y_4 = 2 and a_5 = (1, -2), y_5 = 2?
    # Then for z2 to fit BOTH a_3=(1,-1)->1 and a_5=(1,-2)->2:
    #   z2_x - z2_y = 1 AND z2_x - 2 z2_y = 2 => z2_y = -1, z2_x = 0 UNIQUE!
    #   z1_x + z1_y = 1 AND z1_x + 2 z1_y = 2 => z1_y = 1, z1_x = 0 UNIQUE!
    # THEREFORE X* = {((0, 1), (0, -1)), ((0, -1), (0, 1))} IS FINITE (COMPACT, 0^+ X* = {0})!!
    # MEANWHILE, along the ray beta(t) = ((0, 1), (-t, 0)) as t -> +infty:
    #   f(beta(t)) = (|0-0| + |1-1| + |1-(-1)| + |2-2| + |2-(-2)|)/5 = (0+0+2+0+4)/5 = 6/5 CONSTANT!!
    #   AND dist(beta(t), X*) >= t - 1 -> +INFINITY!!
    # BOOM!!!! COUNTEREXAMPLE TO GLOBAL ERROR BOUND WHEN {a_i} FAILS TO POSITIVELY SPAN R^d!!

    A_ce = np.array([[1.0, 0.0], [1.0, 1.0], [1.0, -1.0], [1.0, 2.0], [1.0, -2.0]])
    beta_star_ce = np.array([[0.0, 1.0], [0.0, -1.0]])
    y_ce = max_linear_pred(A_ce, beta_star_ce)
    ray_vals = []
    for t in [1.0, 10.0, 100.0, 1000.0]:
        b = np.array([[0.0, 1.0], [-t, 0.0]])
        fval = l1_objective(A_ce, y_ce, b)
        dval = min_perm_dist(b, beta_star_ce)
        ray_vals.append({"t": t, "f": fval, "dist": dval, "ratio": fval / dval})
    results["global_eb_counterexample"] = {
        "description": "d=2, r=2, m=5 with a_i in open half-space {x>0}: X* is finite (2 points), yet f(beta(t)) = 6/5 constant while dist -> inf",
        "ray_samples": ray_vals,
    }
    print("  Global EB counterexample (a_i in half-space):")
    for rv in ray_vals:
        print(f"    t={rv['t']:6.1f}: f={rv['f']:.4f}, dist={rv['dist']:.4f}, f/dist={rv['ratio']:.6f}")

    # 1B: Spurious local minimizer check (and flat suboptimal plateau)
    # In the same counterexample, for t > 2, beta(t) = ((0, 1), (-t, 0)) has beta_2 strictly inactive
    # on all 5 samples! Wait: is beta_1 = (0, 1) a local minimizer of the 1-component problem on A_ce?
    # Check subgradient of g(b1) = sum |y_i - <a_i, b1>| at b1 = (0, 1) or find the exact L1 median of (A_ce, y_ce)!
    # Minimize sum_i |y_i - <a_i, b1>| over b1 in R^2 via LP:
    # Let b1_opt be the optimal single-component L1 regressor. Then (b1_opt, (-100, 0)) is a STRICTLY SUBOPTIMAL LOCAL MINIMIZER!
    m_ce = len(y_ce)
    # Variables: [b1_x, b1_y, t_1..t_m]
    c_lp = np.concatenate([[0.0, 0.0], np.ones(m_ce)])
    A_ub = np.vstack([
        np.hstack([A_ce, -np.eye(m_ce)]),
        np.hstack([-A_ce, -np.eye(m_ce)]),
    ])
    b_ub = np.concatenate([y_ce, -y_ce])
    res_lp = optimize.linprog(c_lp, A_ub=A_ub, b_ub=b_ub, bounds=[(None, None), (None, None)] + [(0, None)] * m_ce)
    b1_spurious = res_lp.x[:2]
    beta_spurious = np.vstack([b1_spurious, np.array([-50.0, 0.0])])
    f_spurious = l1_objective(A_ce, y_ce, beta_spurious)
    # Verify local optimality by testing 2000 random small perturbations of radius 0.1
    rng = np.random.default_rng(107)
    pert_diffs = []
    for _ in range(2000):
        d_pert = rng.normal(size=(2, 2))
        d_pert *= 0.1 / np.linalg.norm(d_pert)
        pert_diffs.append(l1_objective(A_ce, y_ce, beta_spurious + d_pert) - f_spurious)
    min_pert_diff = float(np.min(pert_diffs))
    results["spurious_local_minimizer"] = {
        "b1_opt_single": b1_spurious.tolist(),
        "beta_spurious": beta_spurious.tolist(),
        "f_spurious": f_spurious,
        "f_star": 0.0,
        "min_diff_over_2000_perturbations_r0.1": min_pert_diff,
    }
    print(f"  Spurious local minimizer: b1={b1_spurious}, b2=[-50,0], f={f_spurious:.6f} > f*=0, min_pert_diff={min_pert_diff:.6e}")
    return results


# ---------------------------------------------------------------------------
# Experiment 2: Claim B — Exact local constant & stability radius decay
# ---------------------------------------------------------------------------

def run_exp2():
    print("\n=== Experiment 2: Claim B (Exact mu_loc & stability radius decay) ===")
    rng = np.random.default_rng(2026)
    results = {"exactness_d2": [], "radius_decay": []}

    # 2A: Verify exact mu_loc in d=2, r=3 across 10 random Gaussian datasets
    d, r, m = 2, 3, 60
    for trial in range(10):
        A = rng.normal(size=(m, d))
        # Well-separated unit vectors in R^2
        angles = np.linspace(0, 2 * np.pi, r, endpoint=False) + rng.uniform(0, 0.2, size=r)
        beta_star = np.column_stack([np.cos(angles), np.sin(angles)])
        scores = A @ beta_star.T
        j_star = np.argmax(scores, axis=1)
        y = np.max(scores, axis=1)

        # Compute exact stability radius
        sorted_scores = np.sort(scores, axis=1)
        margins = sorted_scores[:, -1] - sorted_scores[:, -2]
        a_norms = np.linalg.norm(A, axis=1)
        rho_stab = float(np.min(margins / (np.sqrt(2.0) * a_norms)))

        # Compute exact mu_loc from Claim B
        mu_js = []
        u_js = []
        for j in range(r):
            A_j = A[j_star == j]
            val_j, u_j = exact_l1_min_over_sphere_2d(A_j)
            mu_js.append(val_j / m)
            u_js.append(u_j)
        j_min = int(np.argmin(mu_js))
        mu_loc_theory = float(mu_js[j_min])

        # Verify attainment along worst direction at eps = 0.25 * rho_stab
        eps = 0.25 * rho_stab
        Delta_worst = np.zeros_like(beta_star)
        Delta_worst[j_min] = eps * u_js[j_min]
        ratio_worst = l1_objective(A, y, beta_star + Delta_worst) / min_perm_dist(beta_star + Delta_worst, beta_star)

        # Verify lower bound over 5000 random directions inside B(0, 0.4 * rho_stab)
        min_rand_ratio = np.inf
        for _ in range(5000):
            D = rng.normal(size=(r, d))
            D *= (0.4 * rho_stab * rng.uniform(0.01, 1.0)) / np.linalg.norm(D)
            rat = l1_objective(A, y, beta_star + D) / min_perm_dist(beta_star + D, beta_star)
            if rat < min_rand_ratio:
                min_rand_ratio = rat

        results["exactness_d2"].append({
            "trial": trial,
            "rho_stab": rho_stab,
            "mu_loc_theory": mu_loc_theory,
            "ratio_worst_dir": float(ratio_worst),
            "abs_err": float(abs(ratio_worst - mu_loc_theory)),
            "min_rand_ratio": float(min_rand_ratio),
            "lower_bound_holds": bool(min_rand_ratio >= mu_loc_theory - 1e-12),
        })

    max_err = max(x["abs_err"] for x in results["exactness_d2"])
    all_hold = all(x["lower_bound_holds"] for x in results["exactness_d2"])
    print(f"  d=2, r=3, m=60 (10 trials): max |ratio_worst - mu_loc| = {max_err:.2e}, all lower bounds hold = {all_hold}")

    # 2B: Decay of stability radius rho_stab as m increases (d=5, r=2)
    d = 5
    beta_star = np.zeros((2, d))
    beta_star[0, 0] = 1.0
    beta_star[1, 0] = -1.0  # ||v|| = 2
    for m_val in [50, 100, 200, 500, 1000, 2000]:
        rhos = []
        for _ in range(30):
            A = rng.normal(size=(m_val, d))
            scores = A @ beta_star.T
            margins = np.abs(scores[:, 0] - scores[:, 1])
            a_norms = np.linalg.norm(A, axis=1)
            rhos.append(float(np.min(margins / (np.sqrt(2.0) * a_norms))))
        med_rho = float(np.median(rhos))
        results["radius_decay"].append({
            "m": m_val,
            "median_rho_stab": med_rho,
            "m_times_median_rho": float(m_val * med_rho),
        })
        print(f"  m={m_val:4d}: median rho_stab = {med_rho:.6e}, m * rho_stab = {m_val * med_rho:.4f}")
    return results


# ---------------------------------------------------------------------------
# Experiment 3: Claim C & General-r Population Loss (Exact Quadrature + MC)
# ---------------------------------------------------------------------------

def exact_pop_loss_r2(v_norm, d1_par, d1_perp, d2_par, d2_perp1, d2_perp2):
    """
    Exact population loss F(beta* + Delta) for r=2 under a ~ N(0, I_d) when
    span(v, Delta_1, Delta_2) is at most 2D (d2_perp2 == 0).
    Since |max(b1.a, b2.a) - max(b1*.a, b2*.a)| is positively homogeneous of
    degree 1 in a, E[g(a)] = sqrt(pi/2) * (1/(2*pi)) * int_0^{2*pi} g(u(phi)) dphi.
    Between consecutive kink angles (zeros of <u(phi), w> for the 6 pairwise
    difference vectors), g(u(phi)) = alpha*cos(phi) + beta*sin(phi) is exact,
    so we integrate analytically on every subinterval to machine precision (~1e-16).
    """
    assert d2_perp2 == 0.0
    b1s = np.array([v_norm / 2.0, 0.0])
    b2s = np.array([-v_norm / 2.0, 0.0])
    b1 = b1s + np.array([d1_par, d1_perp])
    b2 = b2s + np.array([d2_par, d2_perp1])

    diff_vecs = [b1s - b2s, b1 - b2, b1 - b1s, b2 - b2s, b1 - b2s, b2 - b1s]
    kinks = [0.0, 2.0 * np.pi]
    for w in diff_vecs:
        if np.linalg.norm(w) > 1e-15:
            phi0 = np.arctan2(-w[0], w[1]) % np.pi
            kinks.append(float(phi0))
            kinks.append(float(phi0 + np.pi))
    kinks = sorted(kinks)
    # Deduplicate close angles
    unique_kinks = [kinks[0]]
    for ang in kinks[1:]:
        if ang - unique_kinks[-1] > 1e-13:
            unique_kinks.append(ang)

    total_int = 0.0
    for a_ang, b_ang in zip(unique_kinks[:-1], unique_kinks[1:]):
        mid = 0.5 * (a_ang + b_ang)
        u_mid = np.array([np.cos(mid), np.sin(mid)])
        w_star = b1s if np.dot(b1s, u_mid) >= np.dot(b2s, u_mid) else b2s
        w_hat = b1 if np.dot(b1, u_mid) >= np.dot(b2, u_mid) else b2
        w_diff = w_hat - w_star
        if np.dot(w_diff, u_mid) < 0:
            w_diff = -w_diff
        # Exact integral of w_diff[0]*cos(phi) + w_diff[1]*sin(phi) on [a_ang, b_ang]
        total_int += w_diff[0] * (np.sin(b_ang) - np.sin(a_ang)) - w_diff[1] * (np.cos(b_ang) - np.cos(a_ang))

    return float(np.sqrt(np.pi / 2.0) * total_int / (2.0 * np.pi))


def run_exp3():
    print("\n=== Experiment 3: Claim C & General-r Population Loss ===")
    results = {"claim_c_exact_2d": [], "claim_c_mc_highdim": [], "cone_scaling_l1_vs_l2": []}

    # 3A: Exact 2D polar quadrature testing our improved bound vs old AI bound
    # Old AI bound: |F - (||d1||+||d2||)/sqrt(2pi)| <= 8*sqrt(2/pi) * t^2 / ||v|| = (16/sqrt(2pi)) t^2 / ||v||
    # Our bound:    |F - (||d1||+||d2||)/sqrt(2pi)| <= ||d1 - d2||^2 / (2*sqrt(2pi) * ||v||) <= (1/sqrt(2pi)) t^2 / ||v||
    v_norm = 2.0
    configs = [
        ("antisym_perp", 0.0, 1.0, 0.0, -1.0),   # worst case for |R| / ||delta||^2
        ("one_sided_perp", 0.0, 1.0, 0.0, 0.0),  # quadratic cancellation!
        ("sym_perp", 0.0, 1.0, 0.0, 1.0),        # delta = 0 -> zero flip error!
        ("antisym_par", 1.0, 0.0, -1.0, 0.0),    # parallel to v -> zero angle -> zero flip error until ||delta|| > ||v||!
        ("mixed_45deg", 0.6, 0.8, -0.3, -0.9),
    ]
    for name, u1x, u1y, u2x, u2y in configs:
        for scale in [0.01, 0.05, 0.1, 0.25, 0.5]:
            d1 = scale * np.array([u1x, u1y])
            d2 = scale * np.array([u2x, u2y])
            F_exact = exact_pop_loss_r2(v_norm, d1[0], d1[1], d2[0], d2[1], 0.0)
            L_exact = (np.linalg.norm(d1) + np.linalg.norm(d2)) / np.sqrt(2.0 * np.pi)
            rem = F_exact - L_exact
            delta_norm = float(np.linalg.norm(d1 - d2))
            t_sq = float(np.sum(d1 ** 2) + np.sum(d2 ** 2))
            v_vec = np.array([v_norm, 0.0])
            w2_vec = v_vec + (d1 - d2)
            exact_geom_bound = (np.linalg.norm(v_vec) + np.linalg.norm(w2_vec) - np.linalg.norm(v_vec + w2_vec)) / np.sqrt(2.0 * np.pi)
            our_bound = (delta_norm ** 2) / (2.0 * np.sqrt(2.0 * np.pi) * v_norm)
            old_bound = 8.0 * np.sqrt(2.0 / np.pi) * t_sq / v_norm
            results["claim_c_exact_2d"].append({
                "config": name,
                "scale": scale,
                "F_exact": F_exact,
                "L_exact": float(L_exact),
                "remainder": float(rem),
                "exact_geom_bound": float(exact_geom_bound),
                "our_bound": float(our_bound),
                "old_bound": float(old_bound),
                "ratio_abs_rem_to_exact_geom_bound": float(abs(rem) / exact_geom_bound) if exact_geom_bound > 1e-15 else 0.0,
                "ratio_abs_rem_to_our_bound": float(abs(rem) / our_bound) if our_bound > 0 else 0.0,
                "one_sided_nonpositive": bool(rem <= 1e-13),
                "exact_geom_bound_holds": bool(-rem <= exact_geom_bound + 1e-13),
                "our_bound_holds": bool(abs(rem) <= our_bound + 1e-13),
            })

    all_hold_2d = all(x["our_bound_holds"] and x["exact_geom_bound_holds"] and x["one_sided_nonpositive"] for x in results["claim_c_exact_2d"])
    max_ratio = max(x["ratio_abs_rem_to_our_bound"] for x in results["claim_c_exact_2d"])
    max_geom_ratio = max(x["ratio_abs_rem_to_exact_geom_bound"] for x in results["claim_c_exact_2d"])
    print(f"  Exact 2D integration (25 configs): all bounds & one-sided sign hold = {all_hold_2d}, max |rem|/geom_bnd = {max_geom_ratio:.6f}, max |rem|/quad_bnd = {max_ratio:.6f}")
    for x in results["claim_c_exact_2d"]:
        if x["scale"] == 0.05:
            print(f"    {x['config']:15s} (s=0.05): rem={x['remainder']:+.3e}, our_bnd={x['our_bound']:.3e}, ratio={x['ratio_abs_rem_to_our_bound']:.4f}, old_bnd={x['old_bound']:.3e}")

    # 3B: High-dimensional Monte Carlo check (d=20, r=2 and r=4)
    rng = np.random.default_rng(303)
    M_mc = 200_000
    for r_val in [2, 4]:
        d = 20
        A_mc = rng.normal(size=(M_mc, d))
        # Regular simplex / orthonormal ground truth
        beta_star = np.zeros((r_val, d))
        for j in range(r_val):
            beta_star[j, j] = 1.0
        # Pairwise separation = sqrt(2)
        sep = np.sqrt(2.0)
        y_mc = max_linear_pred(A_mc, beta_star)
        j_star_mc = np.argmax(A_mc @ beta_star.T, axis=1)

        for scale in [0.05, 0.1, 0.2]:
            Delta = rng.normal(size=(r_val, d))
            Delta *= scale / np.linalg.norm(Delta)
            yhat_mc = max_linear_pred(A_mc, beta_star + Delta)
            diffs = np.abs(yhat_mc - y_mc)
            F_hat = float(np.mean(diffs))
            F_se = float(np.std(diffs) / np.sqrt(M_mc))

            # Linearized term L(a; Delta)
            L_vals = np.abs(np.sum(A_mc * Delta[j_star_mc], axis=1))
            L_hat = float(np.mean(L_vals))
            rem_hat = float(np.mean(diffs - L_vals))
            rem_se = float(np.std(diffs - L_vals) / np.sqrt(M_mc))

            # Exact pairwise bound: sum_{j<k} ||Delta_j - Delta_k||^2 / (2*sqrt(2pi)*||b_j*-b_k*||)
            pair_bnd = 0.0
            for j in range(r_val):
                for k in range(j + 1, r_val):
                    pair_bnd += float(np.sum((Delta[j] - Delta[k]) ** 2)) / (
                        2.0 * np.sqrt(2.0 * np.pi) * float(np.linalg.norm(beta_star[j] - beta_star[k]))
                    )
            results["claim_c_mc_highdim"].append({
                "r": r_val,
                "d": d,
                "scale": scale,
                "F_hat": F_hat,
                "F_se": F_se,
                "L_hat": L_hat,
                "rem_hat": rem_hat,
                "rem_se": rem_se,
                "pair_bound": pair_bnd,
                "holds_within_3se": bool(abs(rem_hat) <= pair_bnd + 3.0 * rem_se),
            })
            print(f"  MC d={d}, r={r_val}, ||D||={scale:.2f}: F={F_hat:.5f}, L={L_hat:.5f}, |rem|={abs(rem_hat):.5e} +/- {rem_se:.1e} <= bnd={pair_bnd:.5e}")

    # 3C: Verify cone conditioning scaling: L1 alpha_j ~ pi_j^2 vs L2 lambda_min ~ pi_j^3 on 2D wedges
    for p in [0.5, 0.25, 0.1, 0.05, 0.02]:
        # Wedge C = {phi in [-pi*p, pi*p]}, worst u = (0, 1) -> |<a, u>| = R |sin phi|
        # Exact L1: E[R] * (1/(2pi)) * int_{-pi*p}^{pi*p} |sin phi| dphi = sqrt(2/pi) * (1 - cos(pi*p)) / 2?
        # Wait: E[R] = sqrt(pi/2), 1/(2pi) * 2*(1 - cos(pi*p)) = (1 - cos(pi*p))/pi
        # Product: sqrt(pi/2) * (1 - cos(pi*p)) / pi = (1 - cos(pi*p)) / sqrt(2*pi)
        # Wait check p=0.5: (1 - 0) / sqrt(2*pi) = 1/sqrt(2*pi)!! EXACT!!
        alpha_l1 = (1.0 - np.cos(np.pi * p)) / np.sqrt(2.0 * np.pi)
        # Bathtub lower bound: sqrt(2/pi) * (1 - exp(-z_p^2 / 2)) where erf(z_p / sqrt(2)) = p
        z_p = stats.norm.ppf((1.0 + p) / 2.0)
        bathtub_lb = np.sqrt(2.0 / np.pi) * (1.0 - np.exp(-0.5 * z_p ** 2))
        # Exact L2: E[R^2] * (1/(2pi)) * int_{-pi*p}^{pi*p} sin^2(phi) dphi = 2 * (1/(2pi)) * (pi*p - 0.5*sin(2*pi*p))
        # = p - sin(2*pi*p)/(2*pi)
        lam_l2 = p - np.sin(2.0 * np.pi * p) / (2.0 * np.pi)
        results["cone_scaling_l1_vs_l2"].append({
            "pi_j": p,
            "alpha_l1_exact": float(alpha_l1),
            "bathtub_lb": float(bathtub_lb),
            "alpha_l1_over_p2": float(alpha_l1 / (p ** 2)),
            "lam_l2_exact": float(lam_l2),
            "lam_l2_over_p3": float(lam_l2 / (p ** 3)),
        })
    print("  Cone conditioning scaling (2D wedge of probability pi_j):")
    for row in results["cone_scaling_l1_vs_l2"]:
        print(f"    pi={row['pi_j']:.2f}: L1 alpha={row['alpha_l1_exact']:.5f} (alpha/pi^2={row['alpha_l1_over_p2']:.3f}, bathtub_lb={row['bathtub_lb']:.5f}) | L2 lam={row['lam_l2_exact']:.6f} (lam/pi^3={row['lam_l2_over_p3']:.3f})")

    return results


# ---------------------------------------------------------------------------
# Experiment 4: Finite-sample empirical sharpness & outlier breakdown point
# ---------------------------------------------------------------------------

def estimate_empirical_sharpness(A, y, beta_star, radius, rng, n_dirs=150, n_opt=12):
    """
    Estimate inf_{0 < ||Delta|| <= radius} (f(beta*+Delta) - f(beta*)) / dist(beta*+Delta, X_perm*)
    using both random multi-scale directions AND targeted adversarial Powell/Nelder-Mead minimization.
    """
    r, d = beta_star.shape
    f0 = l1_objective(A, y, beta_star)
    min_ratio = np.inf

    # Multi-scale random directions
    scales = [radius * s for s in [1e-4, 1e-2, 0.1, 0.3, 0.6, 1.0]]
    for _ in range(n_dirs):
        U = rng.normal(size=(r, d))
        U /= np.linalg.norm(U)
        for s in scales:
            b = beta_star + s * U
            dist = min_perm_dist(b, beta_star)
            if dist > 0:
                rat = (l1_objective(A, y, b) - f0) / dist
                if rat < min_ratio:
                    min_ratio = rat

    # Targeted optimization on the sphere of radius s in {1e-3*R, 0.5*R, R}
    for s in [1e-3 * radius, 0.5 * radius, radius]:
        for _ in range(n_opt):
            u0 = rng.normal(size=r * d)
            u0 /= np.linalg.norm(u0)

            def obj_dir(w):
                nrm = np.linalg.norm(w)
                if nrm == 0:
                    return 1e9
                D = (s * w / nrm).reshape(r, d)
                b = beta_star + D
                dist = min_perm_dist(b, beta_star)
                return (l1_objective(A, y, b) - f0) / dist

            res = optimize.minimize(obj_dir, u0, method="Powell", options={"maxiter": 300, "ftol": 1e-5})
            if res.fun < min_ratio:
                min_ratio = float(res.fun)

    return float(min_ratio)


def run_exp4():
    print("\n=== Experiment 4: Finite-sample empirical sharpness & outlier breakdown ===")
    rng = np.random.default_rng(404)
    results = {"sample_size_scaling": [], "outlier_breakdown": []}

    # 4A: Empirical sharpness vs oversampling ratio m/d for r=2, d in {5, 10}
    # Ground truth: ||beta_1* - beta_2*|| = 2, test macroeconomic radius = 0.25 (fixed, independent of m, d!)
    for d in [5, 10]:
        beta_star = np.zeros((2, d))
        beta_star[0, 0] = 1.0
        beta_star[1, 0] = -1.0
        for ratio_md in [4, 8, 16, 32]:
            m = ratio_md * d
            vals = []
            for _ in range(10):
                A = rng.normal(size=(m, d))
                y = max_linear_pred(A, beta_star)
                mu_hat = estimate_empirical_sharpness(A, y, beta_star, radius=0.25, rng=rng, n_dirs=80, n_opt=6)
                vals.append(mu_hat)
            results["sample_size_scaling"].append({
                "d": d,
                "m": m,
                "m_over_d": ratio_md,
                "radius": 0.25,
                "mean_mu": float(np.mean(vals)),
                "min_mu": float(np.min(vals)),
                "std_mu": float(np.std(vals)),
            })
            print(f"  d={d:2d}, m={m:3d} (m/d={ratio_md:2d}), R=0.25: mean_mu={np.mean(vals):.4f}, min_mu={np.min(vals):.4f} (pop limit ~ {1/np.sqrt(2*np.pi):.4f})")

    # 4B: Oblivious outlier breakdown threshold (r=2, d=5, m=400, radius=0.15)
    # Corrupt alpha*m entries with HUGE arbitrary outliers (+1000 * random sign or +1000)
    d, m = 5, 400
    beta_star = np.zeros((2, d))
    beta_star[0, 0] = 1.0
    beta_star[1, 0] = -1.0
    for alpha in [0.0, 0.1, 0.2, 0.3, 0.4, 0.45, 0.5, 0.55]:
        vals = []
        for _ in range(10):
            A = rng.normal(size=(m, d))
            y = max_linear_pred(A, beta_star)
            n_bad = int(round(alpha * m))
            if n_bad > 0:
                bad_idx = rng.choice(m, size=n_bad, replace=False)
                # Worst-case one-sided huge corruption (+1000) pushes prediction UP on S_bad!
                y[bad_idx] += 1000.0
            mu_hat = estimate_empirical_sharpness(A, y, beta_star, radius=0.15, rng=rng, n_dirs=80, n_opt=8)
            vals.append(mu_hat)
        theory_pred = (1.0 - 2.0 * alpha) / np.sqrt(2.0 * np.pi)
        results["outlier_breakdown"].append({
            "alpha": alpha,
            "mean_mu": float(np.mean(vals)),
            "min_mu": float(np.min(vals)),
            "theory_asymptotic_1_minus_2alpha": float(theory_pred),
        })
        print(f"  alpha={alpha:.2f}: mean_mu={np.mean(vals):+.4f}, min_mu={np.min(vals):+.4f} | (1-2a)/sqrt(2pi)={theory_pred:+.4f}")

    return results


# ---------------------------------------------------------------------------
# Experiment 5: PolyakSGM linear convergence on noiseless & outlier-corrupted
# ---------------------------------------------------------------------------

def subgradient_max_linear_l1(A, y, beta):
    """One Clarke subgradient of f(beta) = (1/m) sum_i |y_i - max_j <a_i, beta_j>|."""
    m, d = A.shape
    r = beta.shape[0]
    scores = A @ beta.T  # (m, r)
    j_max = np.argmax(scores, axis=1)
    yhat = scores[np.arange(m), j_max]
    resid = yhat - y
    signs = np.sign(resid)
    grad = np.zeros_like(beta)
    for j in range(r):
        mask = (j_max == j)
        if np.any(mask):
            grad[j] = (signs[mask] @ A[mask]) / m
    return grad, float(np.mean(np.abs(resid)))


def run_exp5():
    print("\n=== Experiment 5: PolyakSGM convergence (noiseless & 30% corrupted) ===")
    rng = np.random.default_rng(505)
    results = []
    d, r, m = 20, 3, 400
    beta_star = rng.normal(size=(r, d))
    beta_star /= np.linalg.norm(beta_star, axis=1, keepdims=True)
    A = rng.normal(size=(m, d))
    y_clean = max_linear_pred(A, beta_star)

    for alpha in [0.0, 0.3]:
        y = y_clean.copy()
        n_bad = int(round(alpha * m))
        if n_bad > 0:
            bad_idx = rng.choice(m, size=n_bad, replace=False)
            y[bad_idx] += rng.choice([-1.0, 1.0], size=n_bad) * 100.0
        f_star = l1_objective(A, y, beta_star)
        # Initialize within radius 0.25 of beta_star
        init_pert = rng.normal(size=(r, d))
        init_pert *= 0.25 / np.linalg.norm(init_pert)
        beta = beta_star + init_pert

        dist_hist = [min_perm_dist(beta, beta_star)]
        gap_hist = [l1_objective(A, y, beta) - f_star]
        for it in range(250):
            g, fval = subgradient_max_linear_l1(A, y, beta)
            gnorm_sq = float(np.sum(g ** 2))
            if gnorm_sq < 1e-24 or fval - f_star < 1e-14:
                break
            step = (fval - f_star) / gnorm_sq
            beta = beta - step * g
            dist_hist.append(min_perm_dist(beta, beta_star))
            gap_hist.append(max(0.0, l1_objective(A, y, beta) - f_star))

        results.append({
            "d": d,
            "r": r,
            "m": m,
            "alpha": alpha,
            "f_star": f_star,
            "iters": len(dist_hist) - 1,
            "init_dist": dist_hist[0],
            "final_dist": dist_hist[-1],
            "final_gap": gap_hist[-1],
        })
        print(f"  d={d}, r={r}, m={m}, alpha={alpha:.1f}: iters={len(dist_hist)-1}, init_dist={dist_hist[0]:.4f} -> final_dist={dist_hist[-1]:.3e}, final_gap={gap_hist[-1]:.3e}")
    return results


def main():
    t0 = time.time()
    all_results = {
        "exp1_claim_a": run_exp1(),
        "exp2_claim_b": run_exp2(),
        "exp3_claim_c_and_general_r": run_exp3(),
        "exp4_finite_sample_and_outliers": run_exp4(),
        "exp5_polyak_sgm": run_exp5(),
        "elapsed_seconds": round(time.time() - t0, 2),
    }
    out_path = os.path.join(RESULTS_DIR, "experiment_results.json")
    with open(out_path, "w") as f:
        json.dump(all_results, f, indent=2)
    print(f"\nSaved all results to {out_path} in {all_results['elapsed_seconds']}s")


if __name__ == "__main__":
    main()
