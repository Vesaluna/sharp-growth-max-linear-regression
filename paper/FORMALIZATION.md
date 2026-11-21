# Lean 4 Companion Formalization Guide

This document describes the machine-checked Lean 4 verification companion to the manuscript *"Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression"* (`paper/main.tex`). The Lean project lives independently in `../lean/` so it can be audited, built, or released as a standalone verification repository.

---

## 1. Theorem-by-Theorem Verification Map

Verification levels follow a strict four-tier classification:
- **Fully formalized**: Complete mathematical statement (including measure-theoretic Gaussian expectations / probabilities and all constants) is kernel-checked in Lean 4 from `mathlib` axioms alone, with zero `sorry`, zero `admit`, and zero custom axioms.
- **Partially formalized**: Key deterministic, algebraic, or component lemmas are kernel-checked in Lean 4, while the assembled manuscript statement also relies on pen-and-paper steps or cited external results.
- **Human proof only**: Proved strictly in the manuscript (and/or cited from published literature); not encoded in Lean 4.
- **Proof sketch / unresolved**: Not claimed as a proved theorem in the manuscript.

| Manuscript Theorem (`paper/main.tex`) | Lean 4 Declaration (`../lean/Research107/`) | Verification Status | Additional Hypotheses / Scope |
| :--- | :--- | :--- | :--- |
| **Proposition 2.1** (Robinson–Dolgopolik deterministic error bounds) | — | **Human proof only** | Classical polyhedral theory (Robinson 1981; Dolgopolik 2023). |
| **Proposition 2.2** (Non-weak-convexity & directional jump $K(\beta;E)<0$) | `theorem1b_counterexample_constant`, `theorem1b_class_not_weakly_convex` (`Deterministic.lean`) | **Partially formalized** | Counterexample to naive tie condition and Part~(a) class witness are fully verified; Part~(b)'s general $K(\beta;E)<0$ criterion is human proof only. |
| **Proposition 2.3** (Active-set stability radius: $d=1$ vs. $d \ge 2$) | — | **Human proof only** | Exact $d=1$ invariance and uniform non-asymptotic Beta tail bounds for all $d \ge 2, m \ge 1$. |
| **Theorem 3.1** (Global $r=2$ population remainder & scale-free sharpness $\frac{\sqrt{2}-1}{\sqrt{\pi}}$) | `theorem2_gaussian_remainder_bounds`, `theorem2_unconditional_global_sharpness`, `theorem2_global_quadratic_norm_bound` (`Theorem2Probabilistic.lean`, `Population.lean`) | **Fully formalized** | Zero extra hypotheses beyond `[FiniteDimensional ℝ E] [BorelSpace E]`; covers all $d \ge 1$, collinear vectors, and $\beta_1^* = \beta_2^*$. |
| **Lemma 4.1** (Deterministic pointwise flip decomposition) | `lemma31_pointwise_flip_decomp` (`Deterministic.lean`) | **Fully formalized** | Any real inner product space $E$ and all $r \ge 1$. |
| **Lemma 4.2** (2D Gaussian polar flip integral) | — | **Human proof only** | Used only in Theorem 4.5 (not used in Theorem 5.1). Note: Lean proves the closely related 2D Gaussian min-wedge integral `integral_gaussian_min_wedge` in `Theorem2Probabilistic.lean` for Theorem 3.1. |
| **Lemma 4.3** (Gaussian bathtub lower bound $\frac{\sqrt{2\pi}}{6}p^2$) | `lemma33_gaussian_bathtub` (`Theorem4Probabilistic.lean`) | **Fully formalized** | True `stdGaussian E` integral for any measurable $C \subseteq E$ and $p \in [0, 1]$. |
| **Proposition 4.4** ($\ell_1$ $\Theta(p^2)$ vs. $\ell_2$ $\Theta(p^3)$ cones) | — | **Human proof only** | Exact diagonal Gram matrix & 2D polar calculation for $d \ge 2, p \in (0, 1/2)$; numerically cross-checked in `experiments/paper_experiments.py`. |
| **Theorem 4.5** (General-$r$ population sharp growth) | Components: `lemma31_pointwise_flip_decomp`, `lemma33_gaussian_bathtub` | **Partially formalized** | Pointwise decomposition and Gaussian bathtub bound are verified; Lemma 4.2 integration and final expectation assembly are human proof only. |
| **Theorem 5.1** (Main finite-sample sharp growth under oblivious outliers) | `theorem4_unconditional_probabilistic`, `theorem4_from_pi_min` (`Theorem4Probabilistic.lean`) | **Fully formalized** | Zero sample-event hypotheses (`h_event_op`, `h_event_cone_net`, `h_event_flip_net`, `h_active` all proved); outputs both $\|\cdot\|_{1,2}$ and $\|\cdot\|_F$ bounds with rate $\gamma/4$, global $2$-Lipschitzness, noiseless half-radius distance identity, and simultaneous uniformity over all $\xi$ supported on $S_{\mathrm{bad}}$. Available in both `α_min`-parameterized and `π_min`-bridged forms (`[Nontrivial E]` $\iff d \ge 1$). |
| **Corollary 5.2** (Explicit noiseless $r=2$ constants) | `corollary41_exact_identities` (`Concentration.lean`) | **Partially formalized** | Exact algebraic constants $\rho = \|v\|/(52\sqrt{\pi})$, $\rho/2 = \|v\|/(104\sqrt{\pi})$, $L/\mu = 8\sqrt{2\pi}$ verified in Lean; the numerical domination check $3400d + 480\log(6/\delta)$ is verified in Python (`experiments/adversarial_tests.py`). |
| **Corollary 5.3** (`PolyakSGM` / `SuperPolyak` convergence) | `(A1)` via `theorem4_unconditional_probabilistic` | **Partially formalized** | Assumption `(A1)` is fully verified; semialgebraic active-manifold regularity `(A2)` and algorithm convergence cite Charisopoulos & Davis (2024). |
| **Proposition 5.4** ($\alpha > 1/2$ breakdown converse) | `proposition41_prime_breakdown_necessity` (`ConeConcentration.lean`) | **Fully formalized** | Single fixed corruption vector $\xi_i = \langle a_i, \hat h\rangle$ ($i \in S_{\mathrm{bad}}$) on `iidStdGaussian E m`, failure probability $\le \exp(-\frac{(2\alpha-1)^2}{2\pi}m)$. |
| **Lemmas 5.5, 5.6, 5.7** (Operator norm, cone & flip concentration) | `prob_operator_norm_event`, `prob_cone_net_event`, `prob_flip_net_event`, `exists_sphere_eps_net` (`GaussianModel.lean`, `GaussianOperatorNorm.lean`, `ConeConcentration.lean`, `FlipConcentration.lean`) | **Fully formalized** | Complete measure-theoretic proofs on `iidStdGaussian E m`, including volumetric sphere covering numbers. |
| **Lemmas A.1, A.2, A.3** (Appendix technical lemmas) | `theorem2_wedge_trig_integral`, `thirteen_pow_d_mul_chisq_le`, `integral_pow_mul_exp_neg_sq_div_two`, `lemma43_moment_induction` | **Fully formalized** | All three appendix lemmas are kernel-checked. |
| *(Archived Stage D small-ball sketch, omitted from manuscript)* | — | **Proof sketch / unresolved** | Not claimed as a proved theorem in `paper/main.tex`; noted only as an open direction in Section 7. |

---

## 2. Pinned Toolchain, Dependencies, and Clean-Environment Rebuild

All dependencies are pinned in `../lean/lean-toolchain`, `../lean/lakefile.toml`, and `../lean/lake-manifest.json`:
- **Lean 4 toolchain:** `leanprover/lean4:v4.35.0`
- **Mathlib4:** tag `v4.35.0`, git commit `56a005855ea17e0b0958f73ec801ae140b0a1679`
- **External ML/Stats libraries:** None (100% self-contained on `mathlib4` alone).

### Rebuilding from a Clean Machine
1. Install `elan` (the Lean version manager) from `https://github.com/leanprover/elan`.
2. From the repository root, enter `lean/`, fetch precompiled `mathlib` `.olean` caches (to avoid compiling `mathlib` from scratch), and build:
   ```bash
   cd lean
   lake exe cache get
   lake build
   ```
3. Expected output:
   - Exit code `0` with final line `Build completed successfully (3803 jobs).`
   - **39** `info:` lines from `#print axioms`, every single one reporting exclusively:
     `depends on axioms: [propext, Classical.choice, Quot.sound]`.
4. Optional hygiene audit (should report zero code occurrences):
   ```bash
   grep -rn "\bsorry\b\|\badmit\b\|^axiom \|unsafe \|implemented_by" Research107/ Research107.lean
   ```
5. Codebase totals: 12 `.lean` files, 5,851 lines, 109 declarations (`Research107.lean` and `Research107/*.lean`).

### Mathematical Cross-Check Note
During mathematical audits (`../docs/mathematical_errata.md`), two LaTeX transcription slips were caught in an earlier draft of `paper/main.tex` (an erroneous $e^{-16/9}$ factor in Lemmas 5.5/A.2 instead of $e^{-8/9}$, and $\alpha_{\min}/4$ instead of $\gamma/4$ in Theorem 5.1 Part (3) when $\xi \equiv 0$ with $\alpha > 0$), plus human-proof-only refinements in Proposition 2.3 (`E7`), Lemma 4.2 (`E3`), and Proposition 4.4 (`E2`). Cross-checking against `../lean/Research107/GaussianOperatorNorm.lean` (`prob_chisq_unit_tail`, `thirteen_pow_d_mul_chisq_le`) and `../lean/Research107/Theorem4Probabilistic.lean` (`theorem4_unconditional_probabilistic`) confirmed that the Lean 4 formalization had **already enforced both exact formalized expressions**, and a fresh `lake build` confirmed `Build completed successfully` with zero Lean edits required.
