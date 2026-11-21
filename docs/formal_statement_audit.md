# Formal Statement Audit: Paper Theorems vs. Lean 4 Declarations

**Last Updated:** 2026-11-21 (`v0.1-research-draft`)  
**Lean Toolchain:** `leanprover/lean4:v4.35.0` ([lean/lean-toolchain](../lean/lean-toolchain))  
**Mathlib Dependency:** `v4.35.0` @ commit `56a005855ea17e0b0958f73ec801ae140b0a1679` ([lean/lake-manifest.json](../lean/lake-manifest.json))  
**Build Verification:** `lake build` exited with code `0` (`Build completed successfully`)  
**Codebase Totals:** 12 `.lean` files, **5,851 lines**, **109 declarations**, **0 `sorry`**, **0 `admit`**, **0 custom `axiom`**, **39 / 39 `#print axioms` checks** depending exclusively on `[propext, Classical.choice, Quot.sound]`.

---

## 1. Resolution of the Two Phase IV Static-Audit Alignment Issues

ChatGPT's independent static review of the Phase III Lean code flagged two discrepancies between our manuscript statements and our Phase III Lean declarations. Both have been **resolved directly in Lean 4 and verified by `lake build`**:

### Issue A: Block $\ell_{1,2}$ Norm Conclusion in Theorem 4 (Manuscript Theorem 5.1)
- **Phase III gap:** `theorem4_deterministic_core` proved the stronger block norm bound
  $$f(\beta^* + \Delta) - f(\beta^*) \ge \frac{\gamma}{4}\|\Delta\|_{1,2} \ge \frac{\gamma}{4}\|\Delta\|_F,$$
  but `main_theorem4_assembled` and `theorem4_unconditional_probabilistic` projected onto `.1`, returning only the Frobenius norm version.
- **Phase IV fix (zero extra hypotheses):** Both [`main_theorem4_assembled`](../lean/Research107/MainTheorem.lean#L20-L60) and [`theorem4_unconditional_probabilistic`](../lean/Research107/Theorem4Probabilistic.lean#L104-L144) (as well as `theorem4_from_pi_min`) now output the exact conjunction:
  ```lean
  (γ / 4) * frobNorm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) - l1EmpiricalLoss hr_pos a y β_star ∧
  (γ / 4) * blockL1L2Norm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) - l1EmpiricalLoss hr_pos a y β_star
  ```
- **Status:** **100% aligned.**

### Issue B: Geometric Cone Probability $\pi_{\min} > 0$ vs. Directional Modulus `hαmin` / `h_cone_pop`
- **Phase III gap:** `theorem4_unconditional_probabilistic` assumed explicit hypotheses `hαmin : 0 < α_min` and `h_cone_pop : ∀ j u, ‖u‖ = 1 → α_min ≤ popConeNorm β_star j u`, whereas the manuscript also derives $\alpha_{\min} \ge \frac{\sqrt{2\pi}}{6}\pi_{\min}^2 > 0$ from the geometric cone-probability hypothesis $\pi_{\min} := \min_j \mathbb{P}(a \in C_j^*) > 0$ via Lemma 3.3 (Manuscript Lemma 4.3).
- **Phase IV fix (full measure-theoretic bridge proved in Lean 4):**
  1. Proved [`Research107.lemma33_gaussian_bathtub`](../lean/Research107/Theorem4Probabilistic.lean#L368-L557) unconditionally on `stdGaussian E`: for any measurable set $C \subseteq E$, any $p \in [0, 1]$ with `ENNReal.ofReal p ≤ stdGaussian E C`, and any unit vector $u \in E$,
     $$\frac{\sqrt{2\pi}}{6}\,p^2 \le \int_E \mathbf{1}_C(a)\,|\langle a, u\rangle|\,d(\mathrm{stdGaussian}\ E)(a).$$
     *(Proof avoids quantile inversion by taking $t := \sqrt{\frac{\pi}{2}} p$ directly and using $\mathbb{P}(|Z| \le t) \le \frac{2t}{\sqrt{2\pi}} = p \le \mathbb{P}(C)$.)*
  2. Proved [`Research107.theorem4_from_pi_min`](../lean/Research107/Theorem4Probabilistic.lean#L563-L611) unconditionally, bridging directly from `∀ j, ENNReal.ofReal π_min ≤ stdGaussian E (activeCone β_star j)` (`0 < π_min ≤ 1`) to the full conclusion of `theorem4_unconditional_probabilistic` with `α_min := (√(2π) / 6) * π_min^2` — **eliminating both `hαmin` and `h_cone_pop`!**
- **Status:** **100% aligned.** Both the tighter `α_min`-parameterized form (`theorem4_unconditional_probabilistic`) and the purely geometric `π_min`-parameterized form (`theorem4_from_pi_min`) are kernel-verified, and both pass `#print axioms` with `[propext, Classical.choice, Quot.sound]` only.

---

## 2. Line-by-Line Theorem Audit Table (Manuscript ↔ Lean 4)

| Manuscript (`paper/main.tex`) | Internal Draft Label | Lean 4 Declaration(s) | Alignment Verdict | Exact Matches vs. Remaining Differences / Boundaries |
| :--- | :--- | :--- | :--- | :--- |
| **Proposition 2.1** (Robinson–Dolgopolik deterministic error bounds) | Theorem 1(1) | — | **Human proof only** | Classical polyhedral error bound theory (Robinson 1981, Dolgopolik 2023); intentionally not formalized. |
| **Proposition 2.2** (Non-weak-convexity & directional jump $K(\beta;E)<0$) | Theorem 1(2) | `theorem1b_counterexample_constant`, `theorem1b_class_not_weakly_convex` ([Deterministic.lean:683-765](../lean/Research107/Deterministic.lean#L683-L765)) | **Partially formalized** | Counterexample to naive tie condition (`d=1,r=2,m=2, a=(1,1), y=(1,-1)`) and Part (a) class witness (`d=1,r=2,m=1`) are **exact matches**. Part (b)'s general formula for $K(\beta; E) < 0$ is **human proof only**. |
| **Proposition 2.3** (Active-set stability radius: $d=1$ invariance vs. $d\ge 2$ non-asymptotic collapse) | Theorem 1(3) | — | **Human proof only** | Diagnostic result (strengthened in Phase V with exact $d=1$ identity and uniform non-asymptotic Beta tail bounds for all $d \ge 2, m \ge 1$); not formalized in Lean. |
| **Theorem 3.1** ($r=2$ exact remainder & global scale-free sharpness $\frac{\sqrt{2}-1}{\sqrt{\pi}}$) | Theorem 2 | `popLossR2`, `popLossR2_swap`, `integral_gaussian_min_wedge`, `theorem2_gaussian_remainder_bounds`, `theorem2_unconditional_global_sharpness`, `theorem2_global_quadratic_norm_bound` ([Theorem2Probabilistic.lean](../lean/Research107/Theorem2Probabilistic.lean), [Population.lean](../lean/Research107/Population.lean)) | **Fully formalized (Exact Match)** | Proved for ANY finite-dimensional real inner product space $E$ (generalizing $\mathbb{R}^d$, including $d=1$ and $\beta_1^* = \beta_2^*$). Note: the quadratic bound (3.2) is proved separately in `theorem2_global_quadratic_norm_bound` (`Population.lean:156`) and combines trivially with `theorem2_gaussian_remainder_bounds` (3.1); global sharpness (3.3) is proved end-to-end with zero extra hypotheses. |
| **Lemma 4.1** (Deterministic pointwise flip decomposition) | Lemma 3.1 | `lemma31_pointwise_flip_decomp` ([Deterministic.lean:35](../lean/Research107/Deterministic.lean#L35)) | **Fully formalized (Exact Match)** | Holds for any real inner product space $E$ and all $r \ge 1$. |
| **Lemma 4.2** (2D Gaussian polar flip integral) | Lemma 3.2 | — | **Human proof only** | Used only in Theorem 4.5 (population $r \ge 2$); finite-sample Theorem 5.1 does **not** use Lemma 4.2 (it uses Lemma 5.7 instead). Phase IV.1 added explicit $d=1$ and collinear cases in `paper/main.tex`. |
| **Lemma 4.3** (Gaussian bathtub lower bound $\frac{\sqrt{2\pi}}{6}p^2$) | Lemma 3.3 | `lemma33_gaussian_bathtub` ([Theorem4Probabilistic.lean:368](../lean/Research107/Theorem4Probabilistic.lean#L368)) | **Fully formalized (Exact Match)** | Full measure-theoretic Gaussian expectation bound on `stdGaussian E` for any measurable $C \subseteq E$ and $p \in [0, 1]$. (The paper also notes the intermediate bound $\sqrt{2/\pi}(1 - e^{-\pi p^2/4})$, which appears verbatim inside the Lean proof.) |
| **Proposition 4.4** ($\ell_1$ $\Theta(p^2)$ vs. $\ell_2$ $\Theta(p^3)$ 2D cones) | Proposition 3.4 | — | **Human proof only** | Exact diagonal Gram matrix & two-sided $\Theta(p^2)$ / $\Theta(p^3)$ proof for $d \ge 2, p \in (0, 1/2)$ (strengthened in Phase IV.1); verified numerically in Python (`paper_experiments.py` Exp. D). |
| **Theorem 4.5** (General-$r$ population sharp growth) | Theorem 3 | Components: `lemma31_pointwise_flip_decomp`, `lemma33_gaussian_bathtub` | **Partially formalized** | Pointwise flip decomposition and Gaussian bathtub lower bound are formalized; Lemma 4.2 integration and the final population expectation assembly are **human proof only**. |
| **Theorem 5.1** (Main finite-sample sharp growth under oblivious outliers) | Theorem 4 | `theorem4_unconditional_probabilistic` ([Theorem4Probabilistic.lean:104](../lean/Research107/Theorem4Probabilistic.lean#L104)), `theorem4_from_pi_min` ([Theorem4Probabilistic.lean:563](../lean/Research107/Theorem4Probabilistic.lean#L563)) | **Fully formalized (Exact Match)** | Both `α_min`-parameterized and `π_min`-bridged forms are kernel-verified with **exact verbatim sample complexity**, **both** $\|\cdot\|_{1,2}$ and $\|\cdot\|_F$ bounds with rate $\gamma/4$, global $2$-Lipschitzness, noiseless half-radius distance identity, and simultaneous uniformity over all $\xi$ supported on $S_{\mathrm{bad}}$. See Section 3 below for modeling remarks. |
| **Corollary 5.2** (Noiseless $r = 2$ explicit constants $3400d + 480\log(6/\delta)$) | Corollary 4.1 | `corollary41_exact_identities` ([Concentration.lean:445](../lean/Research107/Concentration.lean#L445)) | **Partially formalized** | Exact algebraic identities $\rho = \|v\|/(52\sqrt{\pi})$, $\rho/2 = \|v\|/(104\sqrt{\pi})$, $L/\mu = 8\sqrt{2\pi}$ are formalized in Lean; the 4-term numerical domination check $3400d + 480\log(6/\delta)$ is verified in Python (`adversarial_tests.py` Test 4) rather than wrapped as a separate Lean corollary. |
| **Corollary 5.3** (`PolyakSGM` & `SuperPolyak` convergence via `(A1)`–`(A2)`) | Corollary 4.2 | `(A1)` via `theorem4_unconditional_probabilistic` | **Partially formalized (`(A1)` only)** | Assumption `(A1)` is fully formalized; Assumption `(A2)` (semialgebraic active-manifold regularity) and algorithmic theorems are cited from Charisopoulos & Davis (2024). |
| **Proposition 5.4** ($\alpha > 1/2$ breakdown converse via uniform translations) | Proposition 4.1′ (C9 fixed) | `proposition41_prime_breakdown_necessity` ([ConeConcentration.lean:500](../lean/Research107/ConeConcentration.lean#L500)) | **Fully formalized (Exact Match)** | Exact single-corruption uniform-translation theorem on `iidStdGaussian E m` with failure probability $\le \exp(-\frac{(2\alpha-1)^2}{2\pi}m)$. |
| **Lemmas 5.5, 5.6, 5.7** (Operator norm, cone concentration, flip concentration) | Lemmas 4.1–4.3 | `prob_operator_norm_event`, `lemma41_gaussian_mgf`, `lemma41_empirical_tails`, `prob_cone_net_event`, `lemma43_gaussian_moments`, `lemma43_gaussian_bernstein_mgf`, `lemma43_pointwise_flip_tail`, `prob_flip_net_event` | **Fully formalized (Exact Match)** | Full measure-theoretic proofs including volumetric sphere covering (`exists_sphere_eps_net`) and 2D polar moment integrals. |
| *(Omitted from manuscript)* | Proposition 4.3 (Small-ball $O(r^3 d\log r)$ sketch) | — | **Proof sketch / unresolved** | Explicitly excluded from manuscript theorems; mentioned only as an open direction in Section 7. |

---

## 3. Subtle Formalization Modeling Checks (Transparency Audit)

Even where a theorem is **Fully formalized**, careful formal-verification practice requires checking for any subtle modeling nuances between informal mathematics and Lean types:

1. **Ambient Euclidean space (`[Nontrivial E]`):** Lean proves Theorem 5.1 on any finite-dimensional real inner product space `E` with `[BorelSpace E] [Nontrivial E]` (which is equivalent to $\mathbb{R}^d$ with $d \ge 1$, matching $d \ge 1$ in the manuscript). Theorem 3.1 does not even need `[Nontrivial E]`.
2. **Outer measure vs. measurability of the `∀ ξ` event:** In `theorem4_unconditional_probabilistic`, the high-probability set is `Good := {a : Fin m → E | ∀ ξ, (∀ i, s i = 1 → ξ i = 0) → ...}`, and the proof shows `B_allᶜ ⊆ Good` where `B_all` is a finite union of bad events of measure $\le \delta_{\mathrm{fail}}$, concluding `1 - ENNReal.ofReal δ_fail ≤ iidStdGaussian E m Good` via `measure_mono`. In Mathlib, `μ S` is Carathéodory outer measure, so for ANY specific measurable data-dependent corruption map `ξ : (Fin m → E) → Fin m → ℝ` supported on `{i | s i = -1}`, `B_allᶜ ⊆ Good ⊆ {a | P a (ξ a)}` immediately gives the exact same lower bound on the measurable set (or its measurable subset `B_allᶜ`) without any hidden measurability assumption on `ξ`. In the manuscript, Theorem 5.1 states *"there exists an event $\mathcal{E}$ of probability at least $1 - \delta_{\mathrm{fail}}$ on which, simultaneously for every corruption vector $\xi$ supported on $S_{\mathrm{bad}}$, …"*, which corresponds literally to $\mathcal{E} := B_{\mathrm{all}}^c$ (a finite intersection of measurable sets) and is 100% equivalent.
3. **Distance to $X^*$ in Part (3) of Theorem 5.1:** In Lean, Part (3) proves `∀ β z, frobNorm (β - β*) ≤ ρ / 2 → l1EmpiricalLoss a y z = 0 → frobNorm (β - β*) ≤ frobNorm (β - z)`. Since $f(\beta^*) = 0$ and $f \ge 0$, `l1EmpiricalLoss a y z = 0` is equivalent to $z \in X^* = \argmin f$, and `∀ z ∈ X*, ‖β - β*‖_F ≤ ‖β - z‖_F` is the exact definition of $\inf_{z \in X^*} \|\beta - z\|_F = \|\beta - \beta^*\|_F$ (since $\beta^* \in X^*$).
4. **Strict cone membership in `activeCone`:** In `Definitions.lean`, `activeCone β_star j := {a : E | ∀ k, k ≠ j → ⟪a, β_star k⟫ < ⟪a, β_star j⟫}`, matching $C_j^*$ verbatim. Almost-sure exhaustiveness `iidStdGaussian_ae_active` proves that on `iidStdGaussian E m`, `∀ i, ∃ j₀, a i ∈ activeCone β_star j₀` holds with probability $1$ whenever $\Delta_{\min} > 0$.

---

## 4. Complete Axiom Audit (Phase IV, 39 / 39 Clean)

Running `lake build` in `lean/` executed **39 `#print axioms` checks** across `MainTheorem.lean` (21), `Theorem4Probabilistic.lean` (14, including `lemma33_gaussian_bathtub` and `theorem4_from_pi_min`), and `Theorem2Probabilistic.lean` (4). Every single check returned exclusively:
```text
[propext, Classical.choice, Quot.sound]
```
with **zero** `sorryAx`, **zero** custom axioms, and **zero** `unsafe` / `implemented_by` declarations.

---

## 5. Phase IV.1 Cross-Check Addendum (2026-11-21)

During Phase IV.1 ([paper/mathematical_errata.md](mathematical_errata.md)), six mathematical corrections and tightenings (`E1`–`E6`) were applied to [paper/main.tex](../paper/main.tex). Cross-checking the two formalized items (`E1` and `E4`) against `lean/Research107/` confirmed:
- **E1 (Lemmas 5.5 & A.2):** `paper/main.tex` previously miswrote `e^{-16/9}` in place of `e^{-8/9}`, whereas [`GaussianOperatorNorm.lean`](../lean/Research107/GaussianOperatorNorm.lean#L140-L280) (`prob_chisq_unit_tail` and `thirteen_pow_d_mul_chisq_le`) already proved the exact `((5/3) * exp (-8/9))^m` bound and two-step domination `13^d * ((5/3) * exp (-8/9))^m ≤ exp (-(9/32) * m)`. `paper/main.tex` now mirrors the exact Lean proof.
- **E4 (Theorem 5.1 Part (3)):** `paper/main.tex` previously wrote `\frac{\alpha_{\min}}{4}` when `\xi \equiv 0` without specifying `\alpha = 0`, whereas [`Theorem4Probabilistic.lean`](../lean/Research107/Theorem4Probabilistic.lean#L130-L144) proved `\frac{\gamma}{4}` throughout. `paper/main.tex` now states `\frac{\gamma}{4}` (and `\frac{\alpha_{\min}}{4}` specifically when `S_{\mathrm{bad}} = \emptyset`).
- **Conclusion:** Zero Lean defects were found; `lean/` was left unchanged and remains strictly aligned with the revised Phase IV.1 manuscript.

### Phase V Addendum (2026-11-21)
In Phase V ([docs/mathematical_errata.md](mathematical_errata.md), item `E7`), Proposition 2.3 (`prop:stab-decay`, human proof only) was corrected for $d = 1$ ($\rho_{\mathrm{stab}} = \|v\|_2/\sqrt{2}$ a.s.) and replaced for $d \ge 2$ by exact non-asymptotic two-sided Beta tail bounds valid uniformly for all $d \ge 2, m \ge 1$. A fresh `lake build` in `lean/` confirmed exit code `0` (`3803 jobs`) and 39/39 clean `#print axioms` checks (`[propext, Classical.choice, Quot.sound]`).
