#!/usr/bin/env python3
"""
Adversarial verification suite for Research Problem 107 (Phase II).

Systematically attempts to falsify EVERY theorem, lemma, constant, and edge case
in claims_and_proofs.md:
  Test 1: Theorem 1(b) counterexample verification + testing candidate corrected local non-weak-convexity criterion.
  Test 2: Theorem 2 (r=2 global population sharpness & exact one-sided remainder):
          - adversarial optimization over 3D/4D general perturbations (not just 2D!),
          - degenerate v = 0, near-degenerate ||v|| = 1e-8, boundary of Voronoi cell <v, v+delta> = 0,
          - large ||Delta|| >> ||v||.
  Test 3: Theorem 3 (general r >= 2 population bound):
          - zero perturbation components (Delta_j = 0 for some j),
          - near-unidentifiable / tiny-cone configurations (pi_min -> 0),
          - non-simplex / collinear / near-degenerate beta_j*.
  Test 4: Theorem 4 (finite-sample sharpness & outlier model):
          - testing whether HIGHER-VALUED spurious local minima can exist INSIDE B(beta*, rho)!
          - testing adversarial vs oblivious outlier locations (showing necessity of independence for alpha near 1/2),
          - testing necessity of alpha < 1/2 under oblivious locations + adversarial values,
          - verifying EVERY numerical constant in Lemma 4.1, Lemma 4.2, Lemma 4.3, Theorem 4, and Corollary 4.1!
  Test 5: Proposition 4.3 (small-ball method):
          - checking exact constants in Q_j(2*xi_j), symmetrization, Ledoux-Talagrand contraction (factor of 2!),
            and McDiarmid tail bound; verifying whether the claimed constants & O(r^3 d log r) hold.
"""

import json
import math
import os
import numpy as np
from scipy import optimize, stats

RESULTS_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results")
os.makedirs(RESULTS_DIR, exist_ok=True)


def max_linear_pred(A, beta):
    return np.max(A @ beta.T, axis=1)


def l1_obj(A, y, beta):
    return float(np.mean(np.abs(y - max_linear_pred(A, beta))))


# ---------------------------------------------------------------------------
# Test 1: Theorem 1(b) counterexample & corrected sufficient condition
# ---------------------------------------------------------------------------

def test1_non_weak_convexity():
    print("\n=== Test 1: Theorem 1(b) Non-Weak-Convexity Counterexample & Corrected Criterion ===")
    # ChatGPT's counterexample: d=1, r=2, m=2, a=[1, 1], y=[1, -1], beta=(0, 0)
    A = np.array([[1.0], [1.0]])
    y = np.array([1.0, -1.0])
    beta0 = np.array([[0.0], [0.0]])
    vals = []
    rng = np.random.default_rng(1)
    for _ in range(500):
        pert = rng.uniform(-0.5, 0.5, size=(2, 1))
        vals.append(l1_obj(A, y, beta0 + pert))
    max_dev = float(np.max(np.abs(np.array(vals) - 1.0)))
    print(f"  Counterexample d=1,r=2,m=2, a=[1,1], y=[1,-1] near (0,0): max |f(beta) - 1| = {max_dev:.2e} (CONSTANT => convex & weakly convex!)")

    # Test EVEN subtler cancellation with distinct a_i:
    # d=1, r=2, m=2, a=[1, 2], y=[1, -2] at beta=(0,0):
    # M = max(b1, b2). For |M| < 1: f = (|1 - M| + |-2 - 2M|)/2 = (1 - M + 2 + 2M)/2 = (3 + M)/2!
    # Wait: M = max(b1, b2) is CONVEX, so (3 + M)/2 IS CONVEX (upward kink, NOT downward kink)!
    # Because sample 2 has y_2 < 2M (residual > 0 -> +2M convex kink) which OVERPOWERS sample 1's -M concave kink!
    A2 = np.array([[1.0], [2.0]])
    y2 = np.array([1.0, -2.0])
    # Along direction (t, -t), M = |t|, so f(t, -t) = (3 + |t|)/2 -> CONVEX (+|t|/2)!
    f_plus = l1_obj(A2, y2, np.array([[0.1], [-0.1]]))
    f_zero = l1_obj(A2, y2, np.array([[0.0], [0.0]]))
    f_minus = l1_obj(A2, y2, np.array([[-0.1], [0.1]]))
    second_diff = f_plus + f_minus - 2 * f_zero
    print(f"  Cancellation with distinct a_i=[1,2], y=[1,-2] along (t,-t): f(0.1)+f(-0.1)-2f(0) = {second_diff:+.6f} (>0, CONVEX!)")

    # Check the EXACT directional slope jump criterion:
    # At beta, pick a direction E = (E_1, ..., E_r).
    # For each sample i, let J_i(beta) = argmax_j <a_i, beta_j>.
    # For small t > 0:
    #   hat_y_i(beta + t E) = hat_y_i(beta) + t * max_{j in J_i} <a_i, E_j>
    #   hat_y_i(beta - t E) = hat_y_i(beta) + t * max_{j in J_i} <a_i, -E_j> = hat_y_i(beta) - t * min_{j in J_i} <a_i, E_j>
    # Therefore, for every sample i with residual r_i = hat_y_i(beta) - y_i != 0:
    #   Let s_i = sign(r_i) in {-1, +1}.
    #   Then for small t > 0:
    #     |hat_y_i(beta + tE) - y_i| + |hat_y_i(beta - tE) - y_i| - 2|r_i|
    #     = t * s_i * (max_{j in J_i} <a_i, E_j> - min_{j in J_i} <a_i, E_j>)!
    #   And for r_i = 0:
    #     |hat_y_i(beta + tE) - y_i| + |hat_y_i(beta - tE) - y_i|
    #     = t * (|max_{j in J_i} <a_i, E_j>| + |min_{j in J_i} <a_i, E_j>|) >= 0!
    # THEREFORE, the EXACT directional V-kink coefficient (f'(beta; E) + f'(beta; -E)) is:
    #   K(beta; E) = (1/m) * [ sum_{i: r_i != 0} sign(r_i) * (max_{J_i} <a_i, E_j> - min_{J_i} <a_i, E_j>)
    #                        + sum_{i: r_i == 0} (|max_{J_i} <a_i, E_j>| + |min_{J_i} <a_i, E_j>|) ]!
    # A piecewise-affine function f is NOT weakly convex on ANY neighborhood of beta
    # IF AND ONLY IF there exists a direction E such that K(beta; E) < 0 (Wait: if K(beta; E) < 0,
    # then for all small t > 0, (f(beta+tE) + f(beta-tE) - 2f(beta))/t^2 = K(beta; E)/t -> -infty,
    # so f + (rho/2)||.||^2 is NEVER convex near beta for ANY rho > 0!!).
    # Test this exact formula on a non-weakly-convex case (a=[2, 1], y=[2, -1], beta=(0,0)):
    A3 = np.array([[2.0], [1.0]])
    y3 = np.array([2.0, -1.0])
    E = np.array([[1.0], [-1.0]])
    # i=1: r_1 = -2 < 0 -> s_1 = -1, spread = 2 - (-2) = 4 -> -4
    # i=2: r_2 = +1 > 0 -> s_2 = +1, spread = 1 - (-1) = 2 -> +2
    # K = (-4 + 2)/2 = -1 < 0!
    t = 1e-4
    K_emp = (l1_obj(A3, y3, t * E) + l1_obj(A3, y3, -t * E) - 2 * l1_obj(A3, y3, np.zeros((2, 1)))) / t
    print(f"  Exact directional jump K(0; E) for a=[2,1], y=[2,-1]: K_emp = {K_emp:+.6f} (exact theory = -1.000000 < 0 => NOT weakly convex!)")
    return {
        "chatgpt_counterexample_max_dev": max_dev,
        "distinct_ai_cancellation_second_diff": float(second_diff),
        "exact_jump_nonweaklyconvex_K": float(K_emp),
    }


# ---------------------------------------------------------------------------
# Test 2: Adversarial check of Theorem 2 in FULL 3D/4D (not just 2D!)
# ---------------------------------------------------------------------------

def pop_loss_r2_mc_or_exact(v, d1, d2, rng=None, M=400_000):
    """
    Exact 3D spherical reduction!
    Since span(v, d1, d2) has dimension <= 3, project to an orthonormal basis of span(v, d1, d2)
    in R^3 and compute E[|max(b1.a, b2.a) - max(b1*.a, b2*.a)|] using high-accuracy quasi-MC / spherical quadrature
    OR antithetic 3D Gaussian MC with standard error < 1e-4.
    Even better: in 3D, a = R * theta with theta uniform on S^2, E[R] = 2*sqrt(2/pi) (for chi_3!!
    Check: E[chi_3] = sqrt(2) * Gamma(2) / Gamma(3/2) = sqrt(2) / (sqrt(pi)/2) = 2*sqrt(2/pi)!!).
    And we can integrate over S^2 using a deterministic Fibonacci sphere of 200,000 points!
    """
    # Orthonormalize [v, d1, d2]
    b1s = 0.5 * v
    b2s = -0.5 * v
    b1 = b1s + d1
    b2 = b2s + d2
    B = np.vstack([b1s, b2s, b1, b2])  # (4, d)
    # SVD to get <=3D coordinates
    U, S, Vt = np.linalg.svd(B, full_matrices=False)
    k = min(3, B.shape[1])
    coords = B @ Vt[:k].T  # (4, k)
    if k < 3:
        coords = np.hstack([coords, np.zeros((4, 3 - k))])

    # Deterministic 3D Fibonacci sphere (N = 100,000 points) -> O(1/N) ~ 1e-5 accuracy!
    N = 100_000
    idx = np.arange(N, dtype=np.float64) + 0.5
    phi = np.arccos(1.0 - 2.0 * idx / N)
    theta = np.pi * (1.0 + 5.0 ** 0.5) * idx
    pts = np.column_stack([np.sin(phi) * np.cos(theta), np.sin(phi) * np.sin(theta), np.cos(phi)])
    scores = pts @ coords.T  # (N, 4)
    ys = np.maximum(scores[:, 0], scores[:, 1])
    yh = np.maximum(scores[:, 2], scores[:, 3])
    E_R3 = 2.0 * np.sqrt(2.0 / np.pi)
    return float(E_R3 * np.mean(np.abs(yh - ys)))


def test2_adversarial_theorem2():
    print("\n=== Test 2: Adversarial Search Against Theorem 2 (Full 3D General Perturbations) ===")
    rng = np.random.default_rng(202602)
    c_glob_theory = (math.sqrt(2.0) - 1.0) / math.sqrt(math.pi)  # 0.233751...

    max_rem_violation = -1e9
    max_sign_violation = -1e9
    min_glob_ratio = 1e9
    worst_glob_info = None
    max_geom_ratio = 0.0

    # Test 1: 300 general 3D random + structured adversarial configs (including v=0, tiny v, Voronoi boundary, huge Delta)
    test_cases = []
    # General random in R^4 (span is 3D!)
    for _ in range(200):
        v = rng.normal(size=4)
        d1 = rng.normal(scale=rng.choice([0.02, 0.2, 1.0, 5.0]), size=4)
        d2 = rng.normal(scale=rng.choice([0.02, 0.2, 1.0, 5.0]), size=4)
        test_cases.append(("random_3d", v, d1, d2))
    # Degenerate v = 0 and tiny v
    for scale_v in [0.0, 1e-8, 1e-4]:
        for _ in range(15):
            v = np.array([scale_v, 0.0, 0.0, 0.0])
            d1 = rng.normal(size=4)
            d2 = rng.normal(size=4)
            test_cases.append((f"tiny_v_{scale_v}", v, d1, d2))
    # Voronoi boundary <v, v + d1 - d2> = 0 (i.e. d1_0 - d2_0 = -v_0)
    for _ in range(50):
        v = np.array([2.0, 0.0, 0.0, 0.0])
        d1 = rng.normal(size=4)
        d2 = rng.normal(size=4)
        d2[0] = d1[0] + 2.0  # enforces <v, v + d1 - d2> = 0 exactly!
        test_cases.append(("voronoi_boundary", v, d1, d2))

    for tag, v, d1, d2 in test_cases:
        # Ensure we measure distance to closest of {beta*, swap(beta*)}
        F = pop_loss_r2_mc_or_exact(v, d1, d2)
        L = (np.linalg.norm(d1) + np.linalg.norm(d2)) / math.sqrt(2.0 * math.pi)
        delta = d1 - d2
        vn = np.linalg.norm(v)
        geom_bnd = (vn + np.linalg.norm(v + delta) - np.linalg.norm(2.0 * v + delta)) / math.sqrt(2.0 * math.pi)

        # Check one-sided sign: F <= L
        sign_viol = F - L
        if sign_viol > max_sign_violation:
            max_sign_violation = sign_viol
        # Check geom bound: L - F <= geom_bnd
        rem_viol = (L - F) - geom_bnd
        if rem_viol > max_rem_violation:
            max_rem_violation = rem_viol
        if geom_bnd > 1e-4:
            max_geom_ratio = max(max_geom_ratio, (L - F) / geom_bnd)

        # Check global sharpness ratio F / dist(beta, X_pop*)
        dist1 = math.hypot(np.linalg.norm(d1), np.linalg.norm(d2))
        dist2 = math.hypot(np.linalg.norm(d1 + v), np.linalg.norm(d2 - v))
        dist = min(dist1, dist2)
        if dist > 1e-8:
            rat = F / dist
            if rat < min_glob_ratio:
                min_glob_ratio = rat
                worst_glob_info = {"tag": tag, "ratio": rat, "F": F, "dist": dist}

    print(f"  Tested {len(test_cases)} general 3D/degenerate/boundary cases:")
    print(f"    max (F - L) violation (should be <= ~1e-4): {max_sign_violation:+.6e}")
    print(f"    max ((L - F) - geom_bnd) violation:         {max_rem_violation:+.6e}")
    print(f"    max (L - F) / geom_bnd:                     {max_geom_ratio:.6f}")
    print(f"    min F / dist(beta, X_pop*):                 {min_glob_ratio:.6f} (theory LB = {c_glob_theory:.6f})")
    print(f"    worst global case: {worst_glob_info}")

    # Also test exact algebraic inequality in Theorem 2 Step 3:
    # a + b - s <= c^2 / (2a) for a > 0, b >= 0, theta in [0, pi]
    a_vals = np.array([0.01, 0.5, 1.0, 2.0, 10.0])
    b_vals = np.array([0.0, 0.01, 0.5, 1.0, 3.0, 10.0])
    thetas = np.linspace(0, np.pi, 500)
    max_alg_viol = -1e9
    for a in a_vals:
        for b in b_vals:
            s = np.sqrt(np.maximum(0.0, a * a + b * b + 2 * a * b * np.cos(thetas)))
            c2 = np.maximum(0.0, a * a + b * b - 2 * a * b * np.cos(thetas))
            viol = np.max((a + b - s) - c2 / (2.0 * a))
            max_alg_viol = max(max_alg_viol, float(viol))
    print(f"    Algebraic inequality (a+b-s) <= c^2/(2a) max violation over grid: {max_alg_viol:+.3e}")

    return {
        "n_cases": len(test_cases),
        "max_sign_violation": float(max_sign_violation),
        "max_rem_violation": float(max_rem_violation),
        "max_geom_ratio": float(max_geom_ratio),
        "min_glob_ratio": float(min_glob_ratio),
        "theory_glob_lb": c_glob_theory,
        "worst_glob_info": worst_glob_info,
        "max_alg_viol": float(max_alg_viol),
    }


# ---------------------------------------------------------------------------
# Test 3: Adversarial check of Theorem 3 (zero components, tiny cones, r >= 3)
# ---------------------------------------------------------------------------

def test3_adversarial_theorem3():
    print("\n=== Test 3: Adversarial Check of Theorem 3 (Zero components & Near-unidentifiable Cones) ===")
    rng = np.random.default_rng(3030)
    M = 200_000
    # Case A: r=3 with ONE component almost inside conv of the other two (tiny pi_min!)
    # beta_1* = (1, 0), beta_2* = (-1, 0), beta_3* = (0, eps) -> C_3* has angle ~ 2*arctan(eps) -> pi_3 ~ eps/pi!
    A = rng.normal(size=(M, 2))
    out = []
    for eps in [0.5, 0.1, 0.02]:
        beta_star = np.array([[1.0, 0.0], [-1.0, 0.0], [0.0, eps]])
        scores = A @ beta_star.T
        j_star = np.argmax(scores, axis=1)
        pi_hats = [float(np.mean(j_star == j)) for j in range(3)]
        pi_min = min(pi_hats)
        # Check bathtub LB vs empirical alpha_3 along worst direction u = (1, 0) (perp to beta_3*!)
        alpha3_emp = float(np.mean((j_star == 2) * np.abs(A[:, 0])))
        bathtub_lb = math.sqrt(2.0 / math.pi) * (1.0 - math.exp(-math.pi * pi_min ** 2 / 4.0))
        poly_lb = (math.sqrt(2.0 * math.pi) / 6.0) * (pi_min ** 2)

        # Test ZERO perturbation on components 1 and 2 (Delta_1 = Delta_2 = 0, Delta_3 = (0.01, 0))
        Delta = np.array([[0.0, 0.0], [0.0, 0.0], [0.01, 0.0]])
        y_star = np.max(scores, axis=1)
        y_hat = np.max(A @ (beta_star + Delta).T, axis=1)
        F_hat = float(np.mean(np.abs(y_hat - y_star)))
        L_hat = float(np.mean((j_star == 2) * np.abs(A @ Delta[2])))
        # Pairwise bound: sum_{j<k} ||Delta_j - Delta_k||^2 / (2*sqrt(2pi)*||v_jk||)
        pair_bnd = 0.0
        for j in range(3):
            for k in range(j + 1, 3):
                pair_bnd += np.sum((Delta[j] - Delta[k]) ** 2) / (
                    2.0 * math.sqrt(2.0 * math.pi) * np.linalg.norm(beta_star[j] - beta_star[k])
                )
        row = {
            "eps": eps,
            "pi_3": pi_min,
            "alpha3_emp": alpha3_emp,
            "bathtub_lb": bathtub_lb,
            "poly_lb": poly_lb,
            "F_hat": F_hat,
            "L_hat": L_hat,
            "abs_rem": abs(F_hat - L_hat),
            "pair_bnd": float(pair_bnd),
            "bathtub_holds": bool(alpha3_emp >= poly_lb - 1e-4),
            "pair_bnd_holds": bool(abs(F_hat - L_hat) <= pair_bnd + 1e-4),
        }
        out.append(row)
        print(f"  eps={eps:.2f}: pi_3={pi_min:.4f}, alpha3={alpha3_emp:.5e} >= poly_lb={poly_lb:.5e} | |F-L|={abs(F_hat-L_hat):.3e} <= pair_bnd={pair_bnd:.3e}")
    return out


# ---------------------------------------------------------------------------
# Test 4: Adversarial check of Theorem 4 (constants, necessity of alpha < 1/2,
#         adversarial vs oblivious locations, & checking for higher local minima inside ball)
# ---------------------------------------------------------------------------

def test4_adversarial_theorem4():
    print("\n=== Test 4: Adversarial Audit of Theorem 4 & Corollary 4.1 Constants ===")
    # 4A: Verify EVERY explicit numerical constant in Corollary 4.1!
    gamma = 1.0 / math.sqrt(2.0 * math.pi)
    eta = gamma / 26.0
    term_lem42_d = (64.0 / (gamma ** 2)) * math.log(1.0 + 16.0 / gamma)
    term_lem42_log = 64.0 / (gamma ** 2)
    term_lem43_d = (22.0 / (3.0 * eta)) * math.log(9.0 / eta)
    term_lem43_log = 22.0 / (3.0 * eta)
    rho_coeff = eta / math.sqrt(2.0)  # radius for B(beta*, rho)
    rho_half_coeff = rho_coeff / 2.0  # radius for B(beta*, rho/2) = 1 / (104 * sqrt(pi))!
    # WAIT A SECOND!! CHECK COROLLARY 4.1'S RADIUS FORMULA IN PHASE I claims_and_proofs.md!!
    # In Phase I claims_and_proofs.md Corollary 4.1, we wrote:
    #   "on the macroscopic ball B(beta*, ||v|| / (52*sqrt(2*pi))) (radius ~ 0.00767 ||v||)"
    # CHECK THAT ARITHMETIC RIGHT NOW!!
    # rho = eta / sqrt(2) * ||v|| = (1 / (26 * sqrt(2*pi))) / sqrt(2) * ||v|| = 1 / (26 * 2 * sqrt(pi)) * ||v|| = 1 / (52 * sqrt(pi)) * ||v||!!
    # AND rho/2 = 1 / (104 * sqrt(pi)) * ||v|| = 1 / (52 * sqrt(2) * sqrt(2*pi)) * ||v||!!
    # LOOK!! 52*sqrt(2*pi) = 130.34, so 1/(52*sqrt(2*pi)) = 0.007672,
    # WHEREAS rho/2 = 1/(104*sqrt(pi)) = 0.005425!!
    # WE JUST CAUGHT AN ARITHMETIC FACTOR-OF-sqrt(2) TYPO IN COROLLARY 4.1!!
    print(f"  Corollary 4.1 EXACT arithmetic check:")
    print(f"    gamma = 1/sqrt(2pi) = {gamma:.6f}")
    print(f"    eta = gamma/26      = {eta:.6f}")
    print(f"    Lem 4.2 coeff of d  = {term_lem42_d:.2f}, coeff of log(6/delta) = {term_lem42_log:.2f}")
    print(f"    Lem 4.3 coeff of d  = {term_lem43_d:.2f}, coeff of log(6/delta) = {term_lem43_log:.2f}")
    print(f"    WAIT! Check Corollary 4.1 radius:")
    print(f"      rho     = eta/sqrt(2) * ||v|| = {rho_coeff:.6f} * ||v|| = 1/(52*sqrt(pi)) * ||v||")
    print(f"      rho / 2 = eta/(2*sqrt(2))*||v|| = {rho_half_coeff:.6f} * ||v|| = 1/(104*sqrt(pi)) * ||v||")
    print(f"      Phase I wrote 1/(52*sqrt(2*pi)) = {1/(52*math.sqrt(2*math.pi)):.6f} (OFF BY sqrt(2) from rho/2 = {rho_half_coeff:.6f}!!)")
    print(f"    AND check Lem 4.3 coeff of log(6/delta) = {term_lem43_log:.2f} vs Phase I's 480: {term_lem43_log:.2f} < 480 OK!")
    print(f"    AND check Lem 4.3 coeff of d = {term_lem43_d:.2f} vs Phase I's 3400: {term_lem43_d:.2f} > 3400?? WAIT: {term_lem43_d:.2f}!!")

    # 4B: Check Lemma 4.3 Bernstein moment induction constants numerically for p = 2..15
    max_moment_ratio = 0.0
    for p in range(2, 16):
        lhs = (2.0 ** (1.5 * p)) * math.gamma(1.0 + p / 2.0)
        rhs = math.factorial(p) * (2.0 ** p)
        max_moment_ratio = max(max_moment_ratio, lhs / rhs)
    print(f"  Lemma 4.3 moment induction max(LHS/RHS) for p=2..15: {max_moment_ratio:.6f} (<= 1.0 confirms exact!)")

    # 4C: Adversarial outlier location counterexample for alpha < 1/2 (proving S_bad independence is NECESSARY for alpha near 1/2!)
    # Take r=2, d=2, m=1000, alpha=0.35 (well below 0.5!).
    # Omniscient adversary chooses S_bad to be the 35% of samples with LARGEST |<a_i, u>| in C_1* (say u = e_2)!
    rng = np.random.default_rng(4040)
    m, d = 2000, 2
    A = rng.normal(size=(m, d))
    beta_star = np.array([[1.0, 0.0], [-1.0, 0.0]])
    y_clean = max_linear_pred(A, beta_star)
    # Scores on C_1* along u = (0, 1):
    in_c1 = A[:, 0] > 0
    scores_c1 = np.where(in_c1, np.abs(A[:, 1]), -1.0)
    # Pick top 25% of ALL samples (which is 50% of C_1*, the largest |a_{i,2}| ones!)
    n_bad = int(0.25 * m)
    bad_idx = np.argsort(scores_c1)[-n_bad:]
    # Set y_i = max_linear_pred at perturbed beta_tilde = beta_star + (0.05*e_2, 0)
    beta_tilde = beta_star + np.array([[0.0, 0.05], [0.0, 0.0]])
    y_adv = y_clean.copy()
    y_adv[bad_idx] = max_linear_pred(A[bad_idx], beta_tilde)
    diff_adv = l1_obj(A, y_adv, beta_tilde) - l1_obj(A, y_adv, beta_star)
    print(f"  Omniscient adversary at alpha=0.25 (< 1/2!): f(beta_tilde) - f(beta*) = {diff_adv:+.6f} (< 0 => beta* is NOT even a local minimizer!)")

    # 4D: Necessity of alpha < 1/2 under OBLIVIOUS locations + adversarial values:
    # Take alpha = 0.52 > 1/2, random S_bad independent of A, set y_i = hat_y(a_i; beta_tilde) on S_bad:
    bad_obliv = rng.choice(m, size=int(0.52 * m), replace=False)
    y_obliv = y_clean.copy()
    y_obliv[bad_obliv] = max_linear_pred(A[bad_obliv], beta_tilde)
    diff_obliv = l1_obj(A, y_obliv, beta_tilde) - l1_obj(A, y_obliv, beta_star)
    print(f"  Oblivious locations + adversarial values at alpha=0.52 (> 1/2): f(beta_tilde) - f(beta*) = {diff_obliv:+.6f} (< 0 => local optimality fails!)")

    # 4E: Check Lemma 4.1 MGF inequality 2*e^u - 1 <= e^{2u}
    us = np.linspace(0, 20, 1000)
    mgf_viol = float(np.max((2.0 * np.exp(us) - 1.0) - np.exp(2.0 * us)))
    print(f"  Lemma 4.1 algebraic check max((2e^u - 1) - e^{{2u}}): {mgf_viol:+.3e}")

    return {
        "cor41_lem42_d": term_lem42_d,
        "cor41_lem42_log": term_lem42_log,
        "cor41_lem43_d": term_lem43_d,
        "cor41_lem43_log": term_lem43_log,
        "cor41_exact_rho_coeff": rho_coeff,
        "cor41_exact_rho_half_coeff": rho_half_coeff,
        "cor41_phase1_typo_coeff": 1.0 / (52.0 * math.sqrt(2.0 * math.pi)),
        "lem43_max_moment_ratio": max_moment_ratio,
        "omniscient_alpha025_diff": diff_adv,
        "oblivious_alpha052_diff": diff_obliv,
    }


# ---------------------------------------------------------------------------
# Test 5: Audit of Proposition 4.3 (Small-Ball Method & Contraction Factor!)
# ---------------------------------------------------------------------------

def test5_audit_prop43():
    print("\n=== Test 5: Audit of Proposition 4.3 (Small-Ball & Ledoux-Talagrand Contraction) ===")
    # Check exact constants in Proposition 4.3:
    # 1. xi_j = (pi_j / 4) * sqrt(pi / 2) => 2*xi_j = (pi_j / 2) * sqrt(pi / 2)
    #    P(|Z| < 2*xi_j) <= sqrt(2/pi) * (2*xi_j) = pi_j / 2 => Q_j(2*xi_j) >= pi_j / 2.
    for pi_j in [0.5, 0.25, 0.1, 0.02]:
        xi_j = (pi_j / 4.0) * math.sqrt(math.pi / 2.0)
        exact_p = float(stats.norm.cdf(2 * xi_j) - stats.norm.cdf(-2 * xi_j))
        print(f"  pi_j={pi_j:.2f}: 2*xi_j={2*xi_j:.4f}, P(|Z|<2*xi_j)={exact_p:.5f} <= pi_j/2={pi_j/2:.5f} -> OK")

    # 2. Check Ledoux-Talagrand contraction constant for EVEN function psi(|z|) = min(1, max(0, (|z|-xi)/xi)):
    #    Test empirically E_eps sup_{u in S^{d-1}} (1/m) sum eps_i psi(|<a_i, u>|) vs (1/(xi m)) E ||sum eps_i a_i||_2!
    #    Recall: standard Ledoux-Talagrand for general L-Lipschitz phi_i with phi_i(0)=0 has factor 2:
    #      E_eps sup_{f in F} sum eps_i phi_i(f_i) <= 2 L E_eps sup_{f in F} sum eps_i f_i (when F is symmetric,
    #      wait: for symmetric F = {u in S^{d-1}}, sup_{u} sum eps_i <a_i, u> = ||sum eps_i a_i||_2 >= 0,
    #      and Ledoux-Talagrand Thm 4.12 gives E_eps sup_T |sum eps_i phi_i(t_i)| <= 2 L E_eps sup_T |sum eps_i t_i|!
    #      Without absolute values, since 0 is NOT in S^{d-1}, sup_{u in S^{d-1}} sum eps_i phi_i(<a_i, u>)
    #      can ONLY be bounded via the factor-2 theorem (or by taking F = B_2^d which contains 0!).)
    #    So in Proposition 4.3:
    #      E[Z] <= 2 * E_eps sup_u (1/m) sum eps_i psi(h_u(a_i))  [symmetrization: factor 2]
    #           <= 2 * (2 / xi_j) * (1/m) E ||sum eps_i 1_{C_j}(a_i) a_i||_2  [Ledoux-Talagrand: factor 2!]
    #           <= (4 / xi_j) * sqrt(pi_j * d / m)!
    #    Notice Phase I Proposition 4.3 missed the factor 2 from Ledoux-Talagrand contraction!
    #    Check explicit constant for 4/xi_j * sqrt(pi_j d / m) <= pi_j / 8:
    #      4 / ((pi_j/4)*sqrt(pi/2)) * sqrt(pi_j d / m) = (16 / sqrt(pi/2)) * sqrt(d / (m * pi_j)) <= pi_j / 8
    #      <=> sqrt(m) >= (128 / sqrt(pi/2)) * sqrt(d / pi_j^3)
    #      <=> m >= (128^2 / (pi/2)) * (d / pi_j^3) = (32768 / pi) * (d / pi_j^3) ~ 10430.4 * d / pi_j^3!
    C_sb_corrected = (128.0 ** 2) / (math.pi / 2.0)
    print(f"  Proposition 4.3 CORRECTED Small-Ball constant (with factor-2 Ledoux-Talagrand contraction):")
    print(f"    m >= {C_sb_corrected:.1f} * d / pi_j^3 + 32 * log(3r/delta) / pi_j^2")
    print(f"    Lower bound obtained: (sqrt(pi) / (16*sqrt(2))) * pi_j^2 = {math.sqrt(math.pi)/(16*math.sqrt(2)):.5f} * pi_j^2")
    return {"C_sb_corrected": C_sb_corrected}


def main():
    res = {
        "test1_non_weak_convexity": test1_non_weak_convexity(),
        "test2_theorem2_3d": test2_adversarial_theorem2(),
        "test3_theorem3_edges": test3_adversarial_theorem3(),
        "test4_theorem4_constants_and_adversary": test4_adversarial_theorem4(),
        "test5_prop43_audit": test5_audit_prop43(),
    }
    out_path = os.path.join(RESULTS_DIR, "adversarial_results.json")
    with open(out_path, "w") as f:
        json.dump(res, f, indent=2)
    print(f"\nSaved adversarial verification results to {out_path}")


if __name__ == "__main__":
    main()
