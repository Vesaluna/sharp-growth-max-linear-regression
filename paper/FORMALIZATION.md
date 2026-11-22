# Lean 4 Companion Formalization Guide

This document summarizes the machine-checked Lean 4 verification companion to the standalone research preprint *"Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression"* (`paper/main.tex`, `paper/main.pdf`, and `paper/supplement.pdf`; Zenodo Version DOI [`10.5281/zenodo.24443089`](https://doi.org/10.5281/zenodo.24443089)). The Lean project lives independently in `../lean/` so it can be audited, built, or inspected on its own.

For the full verification boundary—including pen-and-paper results that have **not** yet been independently verified by a human mathematician—see `../docs/verification_boundary_and_open_problems.md` and Section SM1 (Table SM1) of `paper/supplement.pdf`.

---

## 1. Theorem-by-Theorem Verification Map

Verification levels follow a strict three-tier classification (matching Table SM1 in `paper/supplement.pdf`):
- **Fully formalized**: The complete mathematical statement (including measure-theoretic Gaussian expectations or probabilities and explicit constants) is kernel-checked in Lean 4 from `mathlib4` axioms alone, with zero `sorry`, zero `admit`, and zero custom axioms.
- **Partially formalized**: Key deterministic, algebraic, or component lemmas are kernel-checked in Lean 4, while the assembled manuscript statement also relies on pen-and-paper steps or cited external results.
- **Pen-and-paper only**: Proved strictly in the manuscript (and/or cited from published literature); not encoded in Lean 4. Numerical/symbolic checks in Python do not substitute for formal or independent human proof review.

| Manuscript Result (`paper/main.pdf`) | Lean 4 Declaration (`../lean/Research107/`) | Status | Scope & Caveats |
| :--- | :--- | :--- | :--- |
| **Proposition 2.1** (Deterministic piecewise-affine error bounds) | — | **Pen-and-paper only** | Classical polyhedral error bound theory (Robinson 1981; Dolgopolik 2023) plus 4-point $d=2, r=2$ non-coercivity counterexample without positive spanning. |
| **Proposition 2.2** (Non-weak-convexity & directional V-kink criterion $K(\beta;E)<0$) | `theorem1b_counterexample_constant`, `theorem1b_class_not_weakly_convex` (`Deterministic.lean`) | **Partially formalized** | Naive-tie cancellation counterexample and Part (a) class witness ($d=1, r=2, m=1$) are verified in Lean; the general Part (b) directional jump criterion $K(\beta;E)<0$ is pen-and-paper only. |
| **Proposition 2.3** (Active-set stability radius: $d=1$ vs. $d \ge 2$) | — | **Pen-and-paper only** | Exact $d=1$ invariance and uniform non-asymptotic Beta tail bounds for all $d \ge 2, m \ge 1$. |
| **Theorem 3.1** (Global $r=2$ population remainder & scale-free sharpness $\frac{\sqrt{2}-1}{\sqrt{\pi}}$) | `theorem2_gaussian_remainder_bounds`, `theorem2_unconditional_global_sharpness`, `theorem2_global_quadratic_norm_bound` (`Theorem2Probabilistic.lean`, `Population.lean`) | **Fully formalized** | Zero extra hypotheses beyond `[FiniteDimensional ℝ E] [BorelSpace E]`; covers all $d \ge 1$, collinear vectors, and $\beta_1^* = \beta_2^*$. |
| **Remark 3.2** (Relation to real amplitude phase retrieval & constant slack) | — | **Pen-and-paper only** | Notes non-optimality of $\frac{\sqrt{2}-1}{\sqrt{\pi}}$ in Frobenius norm; direct 2D polar calculation at $\beta^*=(e_1,-e_1), \beta=(e_2,-e_2)$ gives $\frac{2-\sqrt{2}}{\sqrt{\pi}} \approx 0.330495$ (cross-checked in Python). |
| **Lemma 4.1** (Deterministic pointwise flip decomposition) | `lemma31_pointwise_flip_decomp` (`Deterministic.lean`) | **Fully formalized** | Any real inner product space $E$ and all $r \ge 1$. |
| **Lemma 4.2** (2D Gaussian polar flip integral) | — | **Pen-and-paper only** | Used only in Theorem 4.5 (not used in Theorem 5.1). Note: Lean proves the closely related 2D Gaussian min-wedge integral `integral_gaussian_min_wedge` in `Theorem2Probabilistic.lean` for Theorem 3.1. |
| **Lemma 4.3** (Gaussian bathtub lower bound $\frac{\sqrt{2\pi}}{6}p^2$) | `lemma33_gaussian_bathtub` (`Theorem4Probabilistic.lean`) | **Fully formalized** | True `stdGaussian E` integral for any measurable $C \subseteq E$ and $p \in [0, 1]$. |
| **Proposition 4.4** ($\ell_1$ $\Theta(p^2)$ vs. $\ell_2$ $\Theta(p^3)$ cones) | — | **Pen-and-paper only** | Exact diagonal Gram matrix & 2D polar calculation for $d \ge 2, p \in (0, 1/2)$; numerically cross-checked in `experiments/paper_experiments.py`. |
| **Theorem 4.5** (General-$r$ population sharp growth) | Components: `lemma31_pointwise_flip_decomp`, `lemma33_gaussian_bathtub` | **Partially formalized** | Pointwise decomposition and Gaussian bathtub bound are verified; Lemma 4.2 integration and final expectation assembly are pen-and-paper only. |
| **Theorem 5.1** (Main finite-sample sharp growth under oblivious outliers) | `theorem4_unconditional_probabilistic`, `theorem4_from_pi_min` (`Theorem4Probabilistic.lean`) | **Fully formalized** | Zero unproved sample-event hypotheses (`h_event_op`, `h_event_cone_net`, `h_event_flip_net`, `h_active` all proved inside Lean); outputs both $\|\cdot\|_{1,2}$ and $\|\cdot\|_F$ bounds with rate $\gamma/4$, global $2$-Lipschitzness, noiseless half-radius distance identity, and simultaneous uniformity over all $\xi$ supported on $S_{\mathrm{bad}}$. Available in both $\alpha_{\min}$-parameterized and $\pi_{\min}$-bridged forms (`[Nontrivial E]` $\iff d \ge 1$). |
| **Remark 5.2** (Sample complexity structure & geometric scope) | `theorem4_from_pi_min` (`Theorem4Probabilistic.lean`) | **Partially formalized** | Discusses $\kappa$-free and $\log(m/d)$-free scaling, redundancy of the $16d$ branch, and the purely geometric $\pi_{\min}$-parameterized version obtained via Lemma 4.3 (formalized in Lean as `theorem4_from_pi_min`). |
| **Corollary 5.3** (Explicit noiseless $r=2$ constants) | `corollary41_exact_identities` (`Concentration.lean`) | **Partially formalized** | Exact algebraic constants $\rho = \|v\|_2/(52\sqrt{\pi})$, $\rho/2 = \|v\|_2/(104\sqrt{\pi})$, $L/\mu = 8\sqrt{2\pi}$ verified in Lean; the numerical domination check $m \ge 3400\,d + 480\log(6/\delta_{\mathrm{fail}})$ (covering cone branch $\approx 1494.35\,d + 402.12\log(6/\delta_{\mathrm{fail}})$ and flip branch $\approx 3046.45\,d + 477.93\log(6/\delta_{\mathrm{fail}})$) is pen-and-paper / cross-checked in Python (`experiments/adversarial_tests.py`). |
| **Corollary 5.4** (`PolyakSGM` / `SuperPolyak` local convergence) | `(A1)` via `theorem4_unconditional_probabilistic` | **Partially formalized** | Sharp growth `(A1)` and isolation are fully verified in Lean; semialgebraic active-manifold regularity `(A2)` and algorithm convergence cite Charisopoulos & Davis (2024, `arXiv:2201.04611`, Proposition 2.1, Theorem 2.1, Corollary 2.3). |
| **Proposition 5.5** ($\alpha > 1/2$ breakdown converse) | `proposition41_prime_breakdown_necessity` (`ConeConcentration.lean`) | **Fully formalized** | Single fixed corruption vector $\xi_i = \langle a_i, \hat h\rangle$ ($i \in S_{\mathrm{bad}}$) on `iidStdGaussian E m`, failure probability $\le \exp(-\frac{(2\alpha-1)^2}{2\pi}m)$. |
| **Lemmas 5.6, 5.7, 5.8** (Operator norm, cone & flip concentration) | `prob_operator_norm_event`, `prob_cone_net_event`, `prob_flip_net_event`, `exists_sphere_eps_net` (`GaussianModel.lean`, `GaussianOperatorNorm.lean`, `ConeConcentration.lean`, `FlipConcentration.lean`) | **Fully formalized** | Complete measure-theoretic proofs on `iidStdGaussian E m`, including volumetric sphere covering numbers. |
| **Lemmas A.1, A.2, A.3** (Appendix technical lemmas) | `theorem2_wedge_trig_integral`, `thirteen_pow_d_mul_chisq_le`, `integral_pow_mul_exp_neg_sq_div_two`, `lemma43_moment_induction` | **Fully formalized** | All three appendix lemmas are kernel-checked. |

---

## 2. Pinned Toolchain, Dependencies, and Clean-Environment Rebuild

All dependencies are pinned in `../lean/lean-toolchain`, `../lean/lakefile.toml`, and `../lean/lake-manifest.json`:
- **Lean 4 toolchain:** `leanprover/lean4:v4.35.0`
- **Mathlib4:** tag `v4.35.0`, git commit `56a005855ea17e0b0958f73ec801ae140b0a1679`
- **Codebase size:** 12 `.lean` files (`Research107.lean` + 11 modules in `Research107/`), **5,851 lines**.
- **External ML/Stats libraries:** None (self-contained on `mathlib4` alone).

### Rebuilding from a Clean Machine
1. Install `elan` (the Lean version manager) from https://github.com/leanprover/elan.
2. From the repository root, enter `lean/`, fetch precompiled `mathlib` `.olean` caches (to avoid compiling `mathlib` from scratch), and build:
   ```bash
   cd lean
   lake exe cache get
   lake build
   ```
3. Expected output (re-verified live on 2026-11-22):
   - Exit code `0` with final line `Build completed successfully (3803 jobs).`
   - **39** `info:` lines from `#print axioms`, every single one reporting exclusively:
     `depends on axioms: [propext, Classical.choice, Quot.sound]`.
4. Optional hygiene audit (reports zero code occurrences):
   ```bash
   grep -rn "\bsorry\b\|\badmit\b\|^axiom \|unsafe \|implemented_by" Research107/ Research107.lean
   ```

---

## 3. Historical Alignment Note

Throughout Phases IV–VIII and the `v1.0.0-preprint` archival release, the Lean 4 codebase in `../lean/` was intentionally frozen once all probabilistic theorems compiled with zero `sorry`s; subsequent LaTeX refinements (including fixing the Lemma 5.6/A.2 Chernoff exponent transcription slip, adding Remark 3.2 on non-optimality of $\frac{\sqrt{2}-1}{\sqrt{\pi}}$, and adding Remark 5.2 shifting Corollaries 5.3–5.4 and Proposition 5.5) were cross-checked directly against the frozen Lean statements and confirmed consistent.
