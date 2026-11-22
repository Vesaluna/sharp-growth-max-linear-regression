# Lean 4 Companion Formalization Guide

This document summarizes the machine-checked Lean 4 verification companion to the standalone research preprint *"Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression"* (`paper/main.tex`, `paper/main.pdf`, and `paper/supplement.pdf`). The Lean project lives independently in `../lean/` so it can be audited, built, or inspected on its own.

For the full verification boundary—including pen-and-paper results that have **not** yet been independently verified by a human mathematician—see `../docs/verification_boundary_and_open_problems.md` and Section SM1 (Table SM1) of `paper/supplement.pdf`.

---

## 1. Theorem-by-Theorem Verification Map

Verification levels follow a strict three-tier classification (matching Table SM1 in `paper/supplement.pdf`):
- **Fully formalized**: The complete mathematical statement (including measure-theoretic Gaussian expectations or probabilities and explicit constants) is kernel-checked in Lean 4 from `mathlib4` axioms alone, with zero `sorry`, zero `admit`, and zero custom axioms.
- **Partially formalized**: Key deterministic, algebraic, or component lemmas are kernel-checked in Lean 4, while the assembled manuscript statement also relies on pen-and-paper steps or cited external results.
- **Pen-and-paper only**: Proved strictly in the manuscript (and/or cited from published literature); not encoded in Lean 4. Numerical/symbolic checks in Python do not substitute for formal or independent human proof review.

| Manuscript Result (`paper/main.pdf`) | Lean 4 Declaration (`../lean/Research107/`) | Status | Scope & Caveats |
| :--- | :--- | :--- | :--- |
| **Proposition 2.1** (Non-weak-convexity & directional jump $K(\beta;E)<0$) | `theorem1b_counterexample_constant`, `theorem1b_class_not_weakly_convex` (`Deterministic.lean`) | **Partially formalized** | Counterexample to the naive active-tie condition and the class witness (Part 1) are verified in Lean; the general $K(\beta;E)<0$ criterion (Part 2) is pen-and-paper only. |
| **Proposition 2.2** (Robinson–Dolgopolik deterministic error bounds) | — | **Pen-and-paper only** | Classical polyhedral error bound theory (Robinson 1981; Dolgopolik 2023). |
| **Proposition 2.3** (Active-set stability radius: $d=1$ vs. $d \ge 2$) | — | **Pen-and-paper only** | Exact $d=1$ invariance and uniform non-asymptotic Beta tail bounds for all $d \ge 2, m \ge 1$. |
| **Theorem 3.1** (Global $r=2$ population remainder & scale-free sharpness $\frac{\sqrt{2}-1}{\sqrt{\pi}}$) | `theorem2_gaussian_remainder_bounds`, `theorem2_unconditional_global_sharpness`, `theorem2_global_quadratic_norm_bound` (`Theorem2Probabilistic.lean`, `Population.lean`) | **Fully formalized** | Zero extra hypotheses beyond `[FiniteDimensional ℝ E] [BorelSpace E]`; covers all $d \ge 1$, collinear vectors, and $\beta_1^* = \beta_2^*$. |
| **Remark 3.2** (Non-optimality of $\frac{\sqrt{2}-1}{\sqrt{\pi}}$; balanced counterexample $\frac{2-\sqrt{2}}{\sqrt{\pi}}$) | — | **Pen-and-paper only** | Direct 2D polar integration; numerically cross-checked in Python. |
| **Lemma 4.1** (Deterministic pointwise flip decomposition) | `lemma31_pointwise_flip_decomp` (`Deterministic.lean`) | **Fully formalized** | Any real inner product space $E$ and all $r \ge 1$. |
| **Lemma 4.2** (2D Gaussian polar flip integral) | — | **Pen-and-paper only** | Used only in Theorem 4.5 (not used in Theorem 5.1). Note: Lean proves the closely related 2D Gaussian min-wedge integral `integral_gaussian_min_wedge` in `Theorem2Probabilistic.lean` for Theorem 3.1. |
| **Lemma 4.3** (Gaussian bathtub lower bound $\frac{\sqrt{2\pi}}{6}p^2$) | `lemma33_gaussian_bathtub` (`Theorem4Probabilistic.lean`) | **Fully formalized** | True `stdGaussian E` integral for any measurable $C \subseteq E$ and $p \in [0, 1]$. |
| **Proposition 4.4** ($\ell_1$ $\Theta(p^2)$ vs. $\ell_2$ $\Theta(p^3)$ cones) | — | **Pen-and-paper only** | Exact diagonal Gram matrix & 2D polar calculation for $d \ge 2, p \in (0, 1/2)$; numerically cross-checked in `experiments/paper_experiments.py`. |
| **Theorem 4.5** (General-$r$ population sharp growth) | Components: `lemma31_pointwise_flip_decomp`, `lemma33_gaussian_bathtub` | **Partially formalized** | Pointwise decomposition and Gaussian bathtub bound are verified; Lemma 4.2 integration and final expectation assembly are pen-and-paper only. |
| **Theorem 5.1** (Main finite-sample sharp growth under oblivious outliers) | `theorem4_unconditional_probabilistic`, `theorem4_from_pi_min` (`Theorem4Probabilistic.lean`) | **Fully formalized** | Zero unproved sample-event hypotheses (`h_event_op`, `h_event_cone_net`, `h_event_flip_net`, `h_active` all proved inside Lean); outputs both $\|\cdot\|_{1,2}$ and $\|\cdot\|_F$ bounds with rate $\gamma/4$, global $2$-Lipschitzness, noiseless half-radius distance identity, and simultaneous uniformity over all $\xi$ supported on $S_{\mathrm{bad}}$. Available in both $\alpha_{\min}$-parameterized and $\pi_{\min}$-bridged forms (`[Nontrivial E]` $\iff d \ge 1$). |
| **Remark 5.2** (Quantifier order: fixed $S_{\mathrm{bad}}$ & fixed signs vs. arbitrary data-dependent $\xi$) | Reflected directly in `theorem4_unconditional_probabilistic` type signature | **Verified by inspection** | Quantifier order verified directly against `Theorem4Probabilistic.lean` (`∀ ξ, ...` inside the high-probability event over `a ~ iidStdGaussian E m`). |
| **Corollary 5.3** (Explicit noiseless $r=2$ constants) | `corollary41_exact_identities` (`Concentration.lean`) | **Partially formalized** | Exact algebraic constants $\rho = \|v\|_2/(52\sqrt{\pi})$, $\rho/2 = \|v\|_2/(104\sqrt{\pi})$, $L/\mu = 8\sqrt{2\pi}$ verified in Lean; the tighter numerical constants $1495d + 403\log(6/\delta)$ (tight $\alpha_{\min} = \frac{1}{\sqrt{2\pi}}$) and $3047d + 478\log(6/\delta)$ (generic $\pi_{\min} = 1/2$) are pen-and-paper calculations cross-checked in Python. |
| **Corollary 5.4** (`PolyakSGM` / `SuperPolyak` local convergence) | `(A1)` via `theorem4_unconditional_probabilistic` | **Partially formalized** | Sharp growth `(A1)` is fully verified in Lean; semialgebraic active-manifold regularity `(A2)` and algorithm convergence cite Charisopoulos & Davis (2024, `arXiv:2201.04611`, Proposition 2.1, Theorem 2.1, Corollary 2.3). |
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

Throughout Phases IV–VIII and the final archival release, the Lean 4 codebase in `../lean/` was intentionally frozen once all probabilistic theorems compiled with zero `sorry`s; subsequent LaTeX refinements (including fixing the Lemma 5.6/A.2 Chernoff exponent transcription slip, tightening the Corollary 5.3 numerical constants, adding Remark 3.2 on non-optimality of $\frac{\sqrt{2}-1}{\sqrt{\pi}}$, and renumbering Propositions 2.1–2.2 and Corollaries 5.3–5.4) were cross-checked directly against the frozen Lean statements and confirmed consistent.
