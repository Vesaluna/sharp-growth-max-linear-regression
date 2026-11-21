# Final Originality & Literature Audit — Research Problem 107 (Phase IV.1 Revised)

**Date:** 2026-11-21 (Phase IV.1 Conservative Epistemic Revision)  
**Target Manuscript:** *Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression* ([paper/main.tex](../paper/main.tex))  
**Companion Evidence Dossier:** [novelty_claims_evidence.md](novelty_claims_evidence.md)  
**Supersedes:** Phase I `literature_review.md`, Phase II `novelty_audit.md`, and Phase IV draft `novelty_audit_final.md`

---

## 1. Epistemic Classification Framework (De-Escalated Certainty Standards)

Following Phase IV.1 review, we eliminate overly assertive novelty labels (*"New Theorem"*, *"Genuinely new"*, *"Not covered by any published theorem"*) and classify every result into four strict epistemic tiers:

1. **Tier 1 — Confirmed Known Result:** Directly proved in prior published literature (or an immediate corollary thereof).
2. **Tier 2 — Original Candidate (No Equivalent Found in Audited Public Literature):** No equivalent statement or proof was found across all publicly accessible literature audited through 2026-11-21, subject to the inherent limitation that unpublished manuscripts and paywalled internal lemmas cannot be exhaustively ruled out.
3. **Tier 3 — Potentially Implied / Adjacent to Existing Results:** Elementary or structurally close to published lemmas in related settings (e.g., linear LAD, symmetric phase retrieval, or deterministic censored LAD), so novelty lies mainly in packaging, explicit constants, or generalization to $r \ge 2$.
4. **Tier 4 — Unresolved Overlap Risk (Unpublished Proofs):** Directly adjacent to announced but unpublished research (specifically Kim, Kanj, & Lee's 2024 `RobustPA` program) whose underlying geometric concentration lemmas could plausibly imply our conclusion; absent public proofs, overlap cannot be ruled out.

---

## 2. Audit of Three Newly Investigated References (Phase IV.1)

### A. Haitham Kanj & Kiryung Lee (May 2026) — *Locally Near Optimal Piecewise Linear Regression in High Dimensions via Difference of Max-Affine Functions* (`arXiv:2605.06959`)
- **Bibliographic verification:** Verified on `arxiv.org` (`arXiv:2605.06959`, May 2026).
- **Exact model & objective:** Parameterizes continuous piecewise-linear functions as a difference of max-affine (DoMA) functions $\max_{j\in[k_1]}\ip{\xi_i}{\beta_j} - \max_{l\in[k_2]}\ip{\xi_i}{\alpha_l}$ and minimizes the **squared $\ell_2$ (MSE) loss**
  $$\ell(\beta, \alpha) = \frac{1}{2n}\sum_{i=1}^n \Bigl(y_i - \max_{j\in[k_1]}\ip{\xi_i}{\beta_j} + \max_{l\in[k_2]}\ip{\xi_i}{\alpha_l}\Bigr)^2$$
  via Adaptive Block Gradient Descent (ABGD) under sub-Gaussian covariates and sub-Gaussian additive noise, proving local linear convergence to minimax-optimal statistical error $\tilde O(d\max(\sigma_z/\epsilon, 1)^2)$.
- **Can it imply Theorem 3.1 or Theorem 5.1?** **No.** It analyzes the smooth-piecewise **$\ell_2$ least-squares** loss under sub-Gaussian noise (quadratic local curvature, no gross outliers, no $\ell_1$ sharp growth). Cited in `paper/main.tex` Sec. 1.

### B. Adil M. Bagirov, Sona Taheri, Napsu Karmitsa, Nargiz Sultanova, & Soodabeh Asadi (2022, online Dec. 2020) — *Robust Piecewise Linear $L_1$-Regression via Nonsmooth DC Optimization*
- **Bibliographic verification:** *Optimization Methods and Software*, Vol. 37, No. 4, pp. 1289–1309, 2022 (published online Dec. 2020); DOI: [`10.1080/10556788.2020.1855171`](https://doi.org/10.1080/10556788.2020.1855171).
- **Access limitation:** Full Taylor & Francis journal PDF is paywalled; audited from publisher metadata, abstract, and author-hosted descriptions (RMIT / Karmitsa).
- **Model & scope:** Formulates **deterministic** piecewise-linear $L_1$-regression (representing continuous piecewise-linear functions as difference-of-convex max-affine functions) as an unconstrained nonsmooth DC optimization problem and develops an incremental algorithm using an aggregate subgradient DC solver (`AggSub`), proving deterministic stationarity/convergence of the DC algorithm and demonstrating empirical robustness to outliers on synthetic and real datasets.
- **Can it imply Theorem 3.1 or Theorem 5.1?** Based on all accessible information, **no** — it is a deterministic DC optimization/algorithmic paper on fixed datasets, not a high-dimensional Gaussian statistical analysis deriving global population sharpness (Theorem 3.1) or finite-sample high-probability sharp growth constants and sample complexity (Theorem 5.1). *(Residual uncertainty from paywall recorded in `novelty_claims_evidence.md`.)* Cited in `paper/main.tex` Sec. 1.

### C. Robert S. Womersley (1986) — *Censored Discrete Linear $\ell_1$ Approximation* (and James L. Powell 1984)
- **Bibliographic verification:** *SIAM Journal on Scientific and Statistical Computing*, Vol. 7, No. 1, pp. 105–122, Jan. 1986; DOI: [`10.1137/0907008`](https://doi.org/10.1137/0907008). Builds directly on J. L. Powell (1984), *Least Absolute Deviations Estimation for the Censored Regression Model*, *Journal of Econometrics*, 25(3):303–325, DOI [`10.1016/0304-4076(84)90004-6`](https://doi.org/10.1016/0304-4076(84)90004-6).
- **Access limitation:** Full 1986 SIAM PDF is paywalled; audited from SIAM metadata, abstract, and secondary econometric/optimization citations.
- **Model & scope:** Minimizes the nonconvex piecewise-linear objective $F(x) = \sum_{i=1}^m |y_i - \max(z_i, x^\top a_i)|$ (censored LAD: equivalent to $r=2$ max-linear regression where one piece $z_i$ is **known/fixed** and only one vector $x \in \R^d$ is unknown). Characterizes the Clarke generalized gradient, gives **deterministic necessary and sufficient conditions for (strict) local minimizers** on fixed finite data, and proposes a finite direct-descent reduced-gradient algorithm.
- **Relation to our work:** Important classical precedent for deterministic nonconvex piecewise-linear $\ell_1$ local optimality (adjacent to our Propositions 2.1–2.2, which we never claim as novel). Does **not** treat $r \ge 2$ unknown parameter blocks, global Gaussian population sharpness (Theorem 3.1), or finite-sample Gaussian sharp growth / sample complexity (Theorem 5.1). Cited in `paper/main.tex` Sec. 1.

---

## 3. Deep Re-Assessment of Kim, Kanj, & Lee's `RobustPA` (2024–2026)

### Publication Status Check (Nov. 2024 – Nov. 2026)
Targeted searches across arXiv, SIAM, IEEE, OhioLINK ETD, and author records through 2026-11-21 confirm:
- **Published / Public:**
  1. Seonho Kim & Kiryung Lee, *Robust Phase Retrieval by Alternating Minimization*, *IEEE Trans. Signal Process.* 73:40–54, 2025 (`arXiv:2404.15302`, DOI [`10.1109/TSP.2024.3515008`](https://doi.org/10.1109/TSP.2024.3515008)) — symmetric 1-vector phase retrieval (`Robust-AM`, alternating LAD LPs).
  2. Seonho Kim, PhD Dissertation, The Ohio State University (2024, `osu1732636662590036`) — Ch. 1 (`Robust-AM`), Ch. 4 (`RobustPA` algorithm + empirical plots only, **zero theorems and zero proofs**).
  3. Haitham Kanj, Seonho Kim, & Kiryung Lee, *Sparse Max-Affine Regression*, *SIMODS* 2026 (`arXiv:2411.02225`, $\ell_2$ loss).
  4. Haitham Kanj & Kiryung Lee, *Locally Near Optimal Piecewise Linear Regression via Difference of Max-Affine Functions* (`arXiv:2605.06959`, May 2026, $\ell_2$ loss).
- **Still Unpublished (Abstracts Only):** Seonho Kim, Haitham Kanj, & Kiryung Lee, *Least Absolute Deviation Approach to Robust Max-Affine Regression* (SIAM MDS24 MS49 abstract, Oct. 2024, p. 44; IEEE vTools `m/444323`). **No public preprint, dissertation chapter with proofs, or journal article was found as of 2026-11-21.**

### Crucial Mathematical Analysis: Could `RobustPA`'s Local Geometry Imply Our Theorem 5.1?
**Yes — we must NOT dismiss overlap merely because `RobustPA` analyzes alternating LPs instead of subgradient methods.**
In Kim & Lee's published phase-retrieval proof (`arXiv:2404.15302`), local linear contraction of `Robust-AM` proceeds by bounding:
1. An inlier-minus-outlier $\ell_1$ lower bound $\frac{1}{m}\sum s_i |\ip{a_i}{h}| \ge c_1 \norm{h}_2$ uniformly over $h$, and
2. A spherical-wedge upper bound on sign-flipped samples $\frac{1}{m}\sum_{i \in \mathrm{flip}(x^{(t)}, x^*)} |\ip{a_i}{x^*}| \le c_2 \norm{x^{(t)} - x^*}_2$ (Lemma 1 of `arXiv:2404.15302`, with sample complexity $m \gtrsim \theta^{-2}(d\log(m/d) \vee \log(1/\delta))$).

If their unpublished `RobustPA` convergence proof generalizes these two ingredients to $r$-component max-affine regression—establishing (i) a uniform signed $\ell_1$ lower bound on each active cone $C_j^*$ and (ii) a uniform pairwise flip-wedge upper bound on a ball $B(\beta^*, \rho)$ with $c_2 < c_1$—then **those two geometric concentration events would immediately imply our local sharp growth inequality $f(\beta) - f(\beta^*) \ge (c_1 - c_2)\Fnorm{\beta - \beta^*}$ via one line of Lemma 4.1 (triangle inequality)!**

**Honest conclusion:**
- Because the `RobustPA` proofs are not public, we **cannot** claim *"no equivalent geometric condition exists in Kim–Kanj–Lee"* — nor can we assume it does. We explicitly classify Theorem 5.1 as **Tier 4 (Unresolved Overlap Risk with Unpublished `RobustPA`)** alongside **Tier 2 (Original Candidate in Published Literature)**.
- What remains **verifiably distinct based on all published evidence** (including `arXiv:2404.15302`) is: (a) direct formulation & verification of Charisopoulos–Davis `(A1)` for first-order subgradient methods (`PolyakSGM`/`SuperPolyak`); (b) our scale-free $2$-Lipschitz surrogate $\varphi_\eta$ avoiding the $\log(m/d)$ factor of `arXiv:2404.15302` Lemma 1 and avoiding $\kappa = \Delta_{\max}/\Delta_{\min}$ dependence, with fully explicit numerical constants; (c) the global scale-free $r=2$ population Theorem 3.1; (d) the $\Theta(\pi_j^2)$ vs. $\Theta(\pi_j^3)$ conditioning separation (Prop. 4.4); and (e) the end-to-end Lean 4 formalization.

---

## 4. Direct Answers to the Four Phase IV.1 Questions

1. **Does any direct or simple transformation of existing work yield Theorem 3.1 ($r=2$ global sharpness $\frac{\sqrt{2}-1}{\sqrt{\pi}}$)?**  
   **No evidence found in audited public literature.** Amplitude phase retrieval is only the 1-vector symmetric slice $\beta_2 = -\beta_1$ (where $\max(\ip{a}{x}, \ip{a}{-x}) = |\ip{a}{x}|$ is even in $a$); quadratic phase retrieval (Duchi & Ruan 2019; Davis et al. 2020) is scale-dependent ($\mu = \Omega(\norm{x^*}_2)$). Extending to two arbitrary independent blocks $(\beta_1, \beta_2)$ with exact antipodal remainder $\frac{\norm{v}_2+\norm{v+\delta}_2-\norm{2v+\delta}_2}{\sqrt{2\pi}}$ and scale-free global constant $\frac{\sqrt{2}-1}{\sqrt{\pi}}$ (persisting as $\beta_1^* \to \beta_2^*$) has no known equivalent in the audited literature (**Tier 2**).
2. **Has an equivalent finite-sample local sharp growth or error bound to Theorem 5.1 already been proved?**  
   - **In published literature:** No (Charisopoulos & Davis 2024 Sec. 5.2.2 leaves it open; Robinson 1981 & Dolgopolik 2023 give non-quantitative deterministic bounds; Womersley 1986 & Bagirov et al. 2022 give deterministic optimality/DC convergence; Ghosh et al. 2022, Kim & Lee 2024, Kanj et al. 2026, Kanj & Lee 2026 analyze $\ell_2$ loss; Kim & Lee 2025 `arXiv:2404.15302` treats only symmetric 1-vector phase retrieval via alternating LPs).
   - **In unpublished work:** **Cannot be ruled out** due to Kim, Kanj, & Lee's unpublished `RobustPA` analysis (**Tier 4**).
3. **Can our sharp growth conclusion be deduced from existing published local convergence analyses?**  
   - Not from $\ell_2$ max-affine convergence analyses (different objective, no outliers, $\pi_{\min}^3$ and $\kappa$ scaling).
   - For the 1-vector symmetric $r=2$ slice ($y_i = |\ip{a_i}{x^*}| + \xi_i$), Kim & Lee's (2025, `arXiv:2404.15302`) published `Robust-AM` concentration lemmas (inlier-outlier $\ell_1$ lower bound + spherical wedge Lemma 1) **could** be recombined via triangle inequality to deduce local sharp growth for that 1-vector symmetric slice (with a $\log(m/d)$ factor and $\alpha \le 1/4$ from Thm. 4). They do **not** directly cover two independent blocks $(\beta_1, \beta_2)$ or general $r \ge 2$ asymmetric polyhedral cones (**Tier 3** for the 1-vector symmetric slice, **Tier 2 / Tier 4** for general $r \ge 2$).
4. **What substantive increment do our explicit constants, sample complexity, and outlier model provide?**  
   - Fully explicit, non-asymptotic constants (e.g., $m \ge 3400d + 480\log(6/\delta)$, $\mu = \frac{1}{4\sqrt{2\pi}}$, $L/\mu \le 8\sqrt{2\pi}$ for noiseless $r=2$);
   - Zero dependence on $\kappa = \Delta_{\max}/\Delta_{\min}$ and zero $\log(m/d)$ factor in flip concentration via $\varphi_\eta$;
   - Simultaneous uniformity over all unbounded data-dependent corruption magnitudes on oblivious $S_{\mathrm{bad}}$ for the full range $\alpha \in [0, 1/2)$, paired with a finite-sample converse (Prop. 5.4) and explicit omniscient-location separation ($\alpha = 0.25$);
   - Kernel-checked Lean 4 verification on multivariate Gaussian measures.

---

## 5. Master Result-by-Result Epistemic Classification Table

| Manuscript Result (`paper/main.tex`) | Epistemic Tier | Primary Literature Context |
| :--- | :--- | :--- |
| **Proposition 2.1** (Deterministic piecewise-affine error bounds) | **Tier 1 (Confirmed Known)** | Direct consequence of Robinson (1981, Prop. 1) & Dolgopolik (2023, Thm. 1, Prop. 1, Cor. 2); Womersley (1986) for censored $r=2$. |
| **Proposition 2.2** (Non-weak-convexity & directional jump $K(\beta;E)<0$) | **Tier 3 (Elementary / Adjacent)** | Elementary variational calculus; related to directional/generalized gradient characterizations in Womersley (1986) & Charisopoulos–Davis (2024). |
| **Proposition 2.3** (Stability radius $\rho_{\mathrm{stab}}$ collapse) | **Tier 3 (Elementary Diagnostic)** | Elementary order-statistics scaling explaining why active-set-fixed proofs fail. |
| **Theorem 3.1** (Global $r=2$ antipodal remainder & $\frac{\sqrt{2}-1}{\sqrt{\pi}}$ sharpness) | **Tier 2 (Original Candidate — No Public Equivalent Found)** | No published or unpublished equivalent located across 1981–2026 literature; Lean-verified. |
| **Lemma 4.1** (Pointwise flip decomposition) | **Tier 3 (Elementary Building Block)** | Clean deterministic reverse-triangle decomposition for arbitrary $r \ge 2$; Lean-verified. |
| **Lemma 4.3 & Proposition 4.4** (Gaussian bathtub $\frac{\sqrt{2\pi}}{6}p^2$ & $\Theta(p^2)$ vs. $\Theta(p^3)$) | **Tier 2 / Tier 3 (Original Quantitative Comparison)** | Bathtub rearrangement is classical in spirit, while the explicit $\frac{\sqrt{2\pi}}{6}p^2$ Gaussian bound and exact $\ell_1$-vs.-$\ell_2$ 2D cone eigenvalue comparison are not found in Ghosh et al. (2022) or Kim–Lee (2024). |
| **Theorem 4.5** (General-$r$ population sharp growth) | **Tier 2 (Original Candidate)** | Combines Lemmas 4.1–4.3; no published equivalent located for $\ell_1$ max-linear regression. |
| **Theorem 5.1 & Corollary 5.2** (Finite-sample sharp growth under oblivious outliers $\alpha < 1/2$) | **Tier 2 (in Public Literature) / Tier 4 (Unresolved Overlap Risk with Unpublished Kim–Kanj–Lee `RobustPA`)** | Directly addresses Charisopoulos & Davis (2024, Sec. 5.2.2); strictly extends 1-vector symmetric `Robust-AM` (Kim & Lee 2025) to general $r \ge 2$ without $\log(m/d)$ or $\kappa$; overlap with unpublished `RobustPA` proofs cannot be ruled out. Lean-verified. |
| **Corollary 5.3** (`PolyakSGM` / `SuperPolyak` convergence) | **Tier 3 (Direct Corollary)** | Plugs Theorem 5.1 into Charisopoulos & Davis (2024, Thms. 1–2). |
| **Proposition 5.4** ($\alpha > 1/2$ breakdown converse) | **Tier 3 (Elementary Converse / Adjacent)** | Finite-sample general-$r$ counterpart to population linear LAD breakdown (cf. Kim 2024 Thesis Lemma 5, pp. 41–42); Lean-verified. |

---

## 6. Compact Comparison Table (Including All Newly Audited Papers)

| Reference | DOI / URL | Loss & Model | Setting & Method | Covers Thm. 3.1? | Covers Thm. 5.1? |
| :--- | :--- | :--- | :--- | :---: | :---: |
| **Powell (1984)** | [`10.1016/0304-4076(84)90004-6`](https://doi.org/10.1016/0304-4076(84)90004-6) | Censored LAD $|y_i - \max(0, x^\top a_i)|$ | Asymptotic consistency / normality (1 unknown vector) | No | No |
| **Womersley (1986)** | [`10.1137/0907008`](https://doi.org/10.1137/0907008) | Censored $\ell_1$ $|y_i - \max(z_i, x^\top a_i)|$ | Deterministic generalized gradient, local min conditions, descent solver | No | No |
| **Robinson (1981); Dolgopolik (2023)** | [`10.1007/BFb0120929`](https://doi.org/10.1007/BFb0120929); [`10.1007/s11228-023-00694-z`](https://doi.org/10.1007/s11228-023-00694-z) | General piecewise affine | Deterministic qualitative local/sublevel/global error bounds | No | No (qualitative only) |
| **Bagirov et al. (2022 / 2020)** | [`10.1080/10556788.2020.1855171`](https://doi.org/10.1080/10556788.2020.1855171) | Piecewise-linear $L_1$ via DC | Deterministic incremental DC optimization (`AggSub`) & experiments | No | No |
| **Duchi & Ruan (2019); Davis et al. (2020)** | [`10.1093/imaiai/iay015`](https://doi.org/10.1093/imaiai/iay015); [`10.1093/imanum/drz031`](https://doi.org/10.1093/imanum/drz031) | Quadratic $\ell_1$ phase retrieval (weakly convex) | High-prob. sharp growth + weak convexity, 1 vector | No | No |
| **Ghosh et al. (2022); Kim & Lee (2024); Kanj et al. (2026)** | [`10.1109/TIT.2021.3130717`](https://doi.org/10.1109/TIT.2021.3130717); [`10.1137/23M1594662`](https://doi.org/10.1137/23M1594662); [`10.1137/24M1709303`](https://doi.org/10.1137/24M1709303) | Max-affine **$\ell_2$ least squares** | AM / GD / SGD / Sp-GD under sub-Gaussian noise (no gross outliers) | No | No |
| **Kanj & Lee (2026)** | [`arXiv:2605.06959`](https://arxiv.org/abs/2605.06959) | Difference of max-affine **$\ell_2$ MSE** | ABGD local linear convergence under sub-Gaussian noise | No | No |
| **Charisopoulos & Davis (2024)** | [`10.1287/moor.2023.1390`](https://doi.org/10.1287/moor.2023.1390) | Sharp semismooth; Sec. 5.2.2 $\ell_1$ max-linear | `PolyakSGM` / `SuperPolyak` assuming `(A1)`–`(A2)`; `(A1)` left open | No | No (target open problem) |
| **Kim & Lee (2025)** | [`10.1109/TSP.2024.3515008`](https://doi.org/10.1109/TSP.2024.3515008) (`arXiv:2404.15302`) | Symmetric 1-vector amplitude LAD PR | Alternating LAD LPs (`Robust-AM`), $\alpha \le 1/4$, $d\log(m/d)$ | No | 1-vector symmetric slice only (indirectly via LP lemmas) |
| **Kim, Kanj, & Lee (2024, unpublished)** | SIAM MDS24 p. 44; Thesis Ch. 4 (`osu1732636662590036`) | General $r$-piece max-affine LAD (`RobustPA`) | Alternating LAD LPs; **full proofs unpublished as of 2026-11-21** | Unlikely (not mentioned) | **Unresolved overlap risk** (underlying cone/wedge lemmas could imply sharp growth) |

---

## 7. Honest Viability Assessment

Do the remaining, evidence-backed contributions still justify an independent research manuscript? **Yes — as a focused, modest 15–23 page technical paper / short note**, provided we maintain full transparency about the unpublished Kim–Kanj–Lee overlap risk:
1. **Theorem 3.1** (global scale-free $r=2$ population sharpness) stands cleanly on its own as a crisp geometric result with zero known overlap.
2. **Theorem 5.1 + Lemma 5.7 + Proposition 4.4** provide a complete, self-contained, $\kappa$-free, $\log(m/d)$-free finite-sample resolution of Charisopoulos & Davis (2024, Sec. 5.2.2) Assumption `(A1)` with explicit constants and an independent, kernel-checked Lean 4 verification.
3. No published paper was found that invalidates or subsumes these main results; the primary remaining uncertainty (Kim–Kanj–Lee's unpublished `RobustPA` proofs) is appropriately flagged for domain-expert pre-review rather than hidden.
