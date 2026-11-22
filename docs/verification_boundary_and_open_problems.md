# Verification Boundary and Open Mathematical Problems

**Date:** 2026-11-22  
**Manuscript:** *Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression* (`paper/main.pdf`, 20 pages; `paper/supplement.pdf`, 4 pages)  
**Lean 4 Companion:** `lean/Research107/` (`leanprover/lean4:v4.35.0`, 12 `.lean` files, 5,851 lines, 0 `sorry`)

---

## 1. Executive Boundary Statement

This project has **not** yet undergone formal peer review or independent line-by-line review by a human mathematician. Its verification status is intentionally split into three clearly demarcated zones:

1. **Machine-checked in Lean 4 (kernel-verified):** The core statistical theorems (**Theorem 3.1**, **Theorem 5.1**, **Proposition 5.5**), their concentration lemmas (**Lemmas 4.1, 4.3, 5.6, 5.7, 5.8**), and all three Appendix A lemmas (**Lemmas A.1–A.3**) are compiled in Lean 4 (`v4.35.0`) with zero `sorry`, zero `admit`, zero custom axioms, and exclusively standard axioms (`[propext, Classical.choice, Quot.sound]`).
2. **Pen-and-paper proofs only (NOT formalized in Lean 4, NOT independently human-audited):** **Propositions 2.1, 2.2(b), 2.3, 4.4**, **Remark 3.2**, **Lemma 4.2**, **Theorem 4.5** (assembly), **Corollary 5.3** (numerical domination check), and **Corollary 5.4** (citation of `(A2)` and SuperPolyak convergence) rely on pen-and-paper arguments and/or external citations. They have been cross-checked numerically/symbolically in Python, which is **not** a substitute for formal verification or independent human refereeing.
3. **Human semantic audit still required even for Lean-verified theorems:** A Lean 4 kernel guarantees that the formalized Lean statement follows logically from `mathlib4` axioms, but confirming that each Lean definition (`iidStdGaussian`, `maxLinearPred`, `frobNorm`, `blockL1L2Norm`, `S_bad`, quantifier order) faithfully matches the English/LaTeX prose in `paper/main.pdf` still requires independent human inspection.

---

## 2. Exact Verification Boundary Table

| Result in `paper/main.pdf` | Lean 4 Status | Type-Signature / Proof Scope Verified | What Remains Unformalized / Unaudited by Human Referee |
| :--- | :---: | :--- | :--- |
| **Prop. 2.1** (Robinson–Dolgopolik deterministic EB) | None | — | Pen-and-paper application of Robinson (1981, Prop. 1) & Dolgopolik (2023, `arXiv:2210.02606` Thm. 4, Prop. 1, Cor. 2) plus 4-point non-coercivity counterexample. |
| **Prop. 2.2** (Non-weak-convexity & directional V-kink criterion) | Partial | Part (a) class witness & naive-tie cancellation counterexample (`Deterministic.lean`) | Part (b) general $K(\beta; E) < 0$ criterion (pen-and-paper only). |
| **Prop. 2.3** (Active-set stability radius) | None | — | Pen-and-paper exact $d=1$ invariance & uniform $d \ge 2$ Beta tail bounds. |
| **Thm. 3.1** (Global $r=2$ Gaussian population sharpness) | **Full** | `theorem2_gaussian_remainder_bounds`, `theorem2_unconditional_global_sharpness` (`Theorem2Probabilistic.lean`); all $d \ge 1$, collinear & $\beta_1^*=\beta_2^*$ cases included. | Independent human inspection of Lean-to-LaTeX correspondence. |
| **Rem. 3.2** (Non-optimality of $\frac{\sqrt{2}-1}{\sqrt{\pi}}$) | None | — | Pen-and-paper 2D polar calculation at $\beta^*=(e_1,-e_1), \beta=(e_2,-e_2)$ giving $\frac{2-\sqrt{2}}{\sqrt{\pi}} \approx 0.330495$. |
| **Lem. 4.1** (Pointwise flip decomposition) | **Full** | `lemma31_pointwise_flip_decomp` (`Deterministic.lean`); all $r \ge 1$. | Independent human inspection of statement alignment. |
| **Lem. 4.2** (2D Gaussian polar flip integral) | None | — | Pen-and-paper polar integral (all 4 degenerate/collinear cases); used only in Thm. 4.5, **not** in Thm. 5.1. |
| **Lem. 4.3** (Gaussian bathtub $\frac{\sqrt{2\pi}}{6}p^2$) | **Full** | `lemma33_gaussian_bathtub` (`Theorem4Probabilistic.lean`). | Independent human inspection of statement alignment. |
| **Prop. 4.4** ($\ell_1$ $\Theta(p^2)$ vs. $\ell_2$ $\Theta(p^3)$) | None | — | Pen-and-paper exact diagonal Gram & 2D polar calculation for $d \ge 2, p \in (0, 1/2)$. |
| **Thm. 4.5** (General-$r$ population sharp growth) | Partial | Components Lem. 4.1 & Lem. 4.3 verified. | Assembly via Lem. 4.2 and expectation bound (pen-and-paper only). |
| **Thm. 5.1** (Main finite-sample robust sharp growth) | **Full** | `theorem4_unconditional_probabilistic` & `theorem4_from_pi_min` (`Theorem4Probabilistic.lean`): zero unproved event assumptions; verified quantifier order (`1 - ofReal(δ_fail) ≤ iidStdGaussian E m {a \| ∀ ξ supported on S_bad, ...}`); fixed oblivious signs `s`, arbitrary data-dependent `ξ`, $\alpha < 1/2$, shared measurable event `B_all^c`, both `frobNorm` and `blockL1L2Norm`, global `2`-Lipschitzness, and Part (3) noiseless half-radius distance identity. | Independent human inspection of Lean-to-LaTeX correspondence. |
| **Cor. 5.3** (Explicit noiseless $r=2$ constants) | Partial | Algebraic constants (`corollary41_exact_identities`) verified. | Numerical domination check $m \ge 3400\,d + 480\log(6/\delta_{\mathrm{fail}})$ covering cone branch ($1494.35\,d + 402.12\log$) and flip branch ($3046.45\,d + 477.93\log$) (pen-and-paper + Python check). |
| **Cor. 5.4** (`PolyakSGM` / `SuperPolyak` convergence) | Partial | `(A1)` verified via Thm. 5.1. | Semialgebraic `(A2)` and algorithm convergence cite Charisopoulos & Davis (`arXiv:2201.04611`, Prop. 2.1, Thm. 2.1, Cor. 2.3); paywalled MOR 49(3) numbering unchecked. |
| **Prop. 5.5** ($\alpha > 1/2$ breakdown converse) | **Full** | `proposition41_prime_breakdown_necessity` (`ConeConcentration.lean`). | Independent human inspection of statement alignment. |
| **Lem. 5.6–5.8** (Concentration lemmas) | **Full** | `prob_operator_norm_event`, `prob_cone_net_event`, `prob_flip_net_event`, `exists_sphere_eps_net`. | Independent human inspection of statement alignment. |
| **Lem. A.1–A.3** (Appendix lemmas) | **Full** | All three kernel-checked (`Theorem2Probabilistic.lean`, `GaussianOperatorNorm.lean`, `FlipConcentration.lean`). | Independent human inspection of statement alignment. |

---

## 3. Explicitly Excluded / Unproved Claims

To avoid any overclaiming, this preprint explicitly does **not** prove:
- **No global initialization guarantee:** Theorem 5.1 establishes *local* sharp growth in $B(\beta^*, \rho)$ and does not analyze how to enter $B(\beta^*, \rho)$ from a random start under gross outliers.
- **No provable $f(\beta^*)$-free convergence guarantee for non-weakly-convex sharp losses:** Corollary 5.4 applies to oracle-$f^*$ Polyak/SuperPolyak methods (which require knowing $f(\beta^*)$ when $\alpha > 0$). The new `GeomDecaySGM` experiment (`experiments/geom_decay_comparison.py`) is strictly empirical and still uses local initialization $\|\beta^{(0)} - \beta^*\|_F = 0.25$.
- **No omniscient adversarial outlier robustness up to $\alpha < 1/2$:** Theorem 5.1 assumes an oblivious fixed corruption index set $S_{\mathrm{bad}}$ (though corruption magnitudes $\xi_i$ on $S_{\mathrm{bad}}$ may depend arbitrarily on $a$). As verified in Supplement SM2 and `experiments/adversarial_tests.py`, an omniscient adversary selecting $S_{\mathrm{bad}}$ as a function of $a$ breaks sharpness already at $\alpha = 0.25$ ($e^{-z_{0.25}^2/2} \approx 0.516 > 0.5$).
- **No dense observation noise theory:** All finite-sample guarantees assume exact sparse corruptions ($\xi_i = 0$ on $S_{\mathrm{bad}}^c$).
- **No non-Gaussian design generalization:** All probabilistic theorems assume isotropic standard Gaussian covariates $a_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, I_d)$.

---

## 4. Open Mathematical Problems (Section 7 of `paper/main.pdf`)

1. **Tight $r$- and $\pi_{\min}$-dependence of sample complexity:**
   Theorem 5.1 paired with Lemma 4.3 yields $m = \tilde{O}(d / (\gamma^2 \pi_{\min}^4))$ (or $\tilde{O}(r^4 d)$ for balanced cones where $\pi_{\min} = \Theta(1/r)$), whereas the parameter count is $rd$. For symmetric balanced cones where $\alpha_{\min} = \Theta(1/r)$, the $\alpha_{\min}$-parameterized bound already improves to $\tilde{O}(r^2 d)$, and tightening the $\varepsilon$-net covering and flip concentration arguments to reach $\tilde{O}(rd)$ (or establishing an information-theoretic lower bound for $\ell_1$ sharp growth) remains open.
2. **Dense noise and heavy-tailed / sub-Gaussian designs:**
   Extending Lemma 4.3 (Gaussian bathtub) and Lemmas 5.6–5.8 beyond exact sparse corruptions and isotropic $\mathcal{N}(0, I_d)$ covariates—for instance via small-ball methods (Mendelson) under general sub-Gaussian or elliptical designs—remains open.
3. **Provable $f^*$-free first-order solvers and outlier-robust initialization:**
   Establishing provable local linear convergence without knowing $f(\beta^*)$ for *non-weakly-convex* sharp objectives (extending the weakly convex geometric step-decay theory of Davis, Drusvyatskiy, & Charisopoulos 2024), together with a provably outlier-robust spectral or convex initialization scheme that enters $B(\beta^*, \rho)$ when $\alpha \in (0, 1/2)$, remains open.
4. **Sharp global population constant for $r = 2$ (and general $r$):**
   Theorem 3.1 proves the scale-free global constant $\frac{\sqrt{2}-1}{\sqrt{\pi}} \approx 0.23382$ in Frobenius norm, while Remark 3.2 exhibits $\beta^* = (e_1, -e_1), \beta = (e_2, -e_2)$ with ratio $\frac{2-\sqrt{2}}{\sqrt{\pi}} \approx 0.330495$. Determining the exact infimum $\inf_{\beta^* \in \mathbb{R}^{2\times d}} \inf_{\beta \notin X_{\mathrm{pop}}^*} F(\beta) / \operatorname{dist}(\beta, X_{\mathrm{pop}}^*)$ for $d \ge 2$ remains open.
5. **Exact relationship to unpublished alternating LAD / Gauss–Newton proofs:**
   Kim, Kanj, & Lee (2024, SIAM MDS24 MS49 abstract) and Kim (2024, OSU PhD thesis `osu1732636662590036`) announced an alternating LAD / Gauss–Newton approach for robust max-affine regression whose full proofs are not publicly available at the time of writing. Comparing active-cone and wedge-flip concentration machinery once full published proofs appear remains an open bibliographic check.
