# Reviewer Readiness Brief: Top 5 Referee Questions & Candid Gap Assessment

**Manuscript:** *Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression* (`paper/main.tex`, 23 pp., Phase IV.1)  
**Purpose:** Anticipate the five sharpest criticisms a specialist referee in nonsmooth optimization, high-dimensional statistics, or formal verification will raise, and record our exact evidence, manuscript citations, and honest residual gaps.

---

## Question 1: How does Theorem 5.1 compare to Kim, Kanj, & Lee's `RobustPA` (and to Womersley 1986 / Bagirov et al. 2022 / Kanj & Lee 2026)? Could `RobustPA` already prove the core finite-sample geometry?

- **Why a referee will ask this:** `RobustPA` (Kim, Kanj, & Lee, SIAM MDS24 abstract, Oct. 2024; Kim 2024 OSU Ph.D. Thesis Ch. 4) studies the exact same $\ell_1$ Gaussian max-affine / max-linear model with oblivious corruptions up to $\alpha < 1/2$. Meanwhile, nonsmooth $\ell_1$ piecewise-linear optimization has classical roots in Powell (1984), Womersley (1986), and Bagirov et al. (2022), and Kanj & Lee (2026, `arXiv:2605.06959`) recently analyzed difference-of-max-affine regression.
- **Concrete evidence in hand:**
  - **Publicly verifiable non-overlap:** Kanj & Lee (2026) minimize **$\ell_2$ MSE** (no $\ell_1$ loss, no gross outliers, no sharp growth); Powell (1984) and Womersley (1986) analyze **censored linear $\ell_1$ regression** (one unknown vector, fixed censoring threshold) deterministically; Bagirov et al. (2022) analyze deterministic DC nonsmooth algorithms (`AggSub`) on fixed datasets; Kim & Lee (*IEEE TSP* 2025, `Robust-AM`) study **symmetric phase retrieval** ($|y_i - |\langle a_i, \beta\rangle||$). None of these establish quantitative Gaussian sharp growth (`(A1)`) for $r$-component $\ell_1$ max-linear regression or the exact global $r=2$ bound of Theorem 3.1.
  - **Manuscript transparency:** Section 1 and Section 7 explicitly cite all four works and accurately distinguish direct variational sharp growth of $f$ for first-order subgradient methods (`PolyakSGM`/`SuperPolyak`) from alternating LAD LP contraction (`RobustPA`).
- **Honest residual gap (MUST NOT be downplayed):**
  - The full proof of `RobustPA` is **not publicly accessible** (neither on arXiv nor in OhioLINK as of Nov. 2026). As analyzed in `novelty_audit_final.md` (Sec. 3.4), any Gaussian convergence proof for `RobustPA` very likely bounds (i) active-cone $\ell_1$ margins on clean vs. corrupted samples and (ii) pairwise wedge-flip errors — and **Lemma 4.1 shows that those two geometric events imply local sharp growth of $f$**.
  - Additionally, the full PDFs of Womersley (1986) and Bagirov et al. (2022) are paywalled (we verified metadata, abstracts, and DOIs, not every page).
- **Recommended pre-submission action:** Obtain or wait for the public `RobustPA` preprint (or politely ask Kanj/Lee during informal expert pre-review) before submitting to a journal so Theorem 5.1's geometric novelty is positioned with 100% precision.

---

## Question 2: Why is the sample complexity $\tilde O(d/\gamma^2 + (r/\gamma)d)$ (and $3400d$ for $r=2$, or $\tilde O(d/\pi_{\min}^4)$ via Lemma 4.3), when your own experiments succeed around $m \approx 5d$–$10d$?

- **Why a referee will ask this:** For balanced $r$-component max-linear regression ($\pi_{\min} = \Theta(1/r)$), the information-theoretic degrees of freedom are $rd$, whereas Theorem 5.1 via Lemma 4.3 gives $\alpha_{\min} \ge \frac{\sqrt{2\pi}}{6}\pi_{\min}^2 = \Omega(r^{-2})$ and therefore $m = \tilde O(r^4 d)$ (or $\tilde O(r^2 d)$ when $\alpha_{\min} = \Theta(1/r)$ for symmetric balanced cones). Even for noiseless $r=2$, Corollary 5.2 needs $3400d + 480\log(6/\delta)$.
- **Concrete evidence in hand:**
  - **Where the losses come from (clearly diagnosed in Section 5 and Section 7):**
    1. **Two-sided vs. one-sided concentration & union bound:** Lemma 5.6 uses a standard $\epsilon$-net Hoeffding/sub-Gaussian argument on $\mathbb{S}^{d-1}$ with scale-free Lipschitz discretization (`1/4` slack in $\gamma$), which gives $O((d/\gamma^2)\log(1/\gamma))$ with large explicit constants rather than a Mendelson small-ball / PAC-Bayes / localized Rademacher lower tail.
    2. **Worst-case cone geometry vs. balanced cones:** Theorem 5.1 is stated primarily in terms of the intrinsic directional modulus $\alpha_{\min}$, which is $\Theta(1/r)$ for balanced cones (giving $\tilde O(r^2 d)$) and only degrades to $\Omega(\pi_{\min}^2)$ (giving $\tilde O(d/\pi_{\min}^4)$) for maximally thin cones (Prop. 4.4 proves $\alpha_{\ell_1}(C_p) = \Theta(p^2)$ is **tight** for narrow 2D cones).
    3. **No $\kappa$ and no $\log(m/d)$ penalty:** Unlike naive bounded-flip / union-over-subsets bounds, Theorem 5.1 has **zero dependence on $\kappa = \Delta_{\max}/\Delta_{\min}$** and **no $\log(m/d)$ factor** because $\varphi_\eta$ is positively homogeneous and $2$-Lipschitz.
  - **Empirical honesty:** Section 6 (`Fig. 1` / Table 1) explicitly reports the empirical threshold ($m \approx 5d$–$10d$ for $r=2$) side by side with the theoretical $3400d$ bound, rather than hiding the gap.
- **Honest residual gap:**
  - Closing the $r$-dependence from $\tilde O(d/\gamma^2 + (r/\gamma)d)$ down to $O(rd)$ (e.g., via Mendelson small-ball for the lower tail + tighter flip chaining) remains **open**. We intentionally omitted an earlier unverified small-ball sketch from the manuscript rather than claiming an unproved sharper rate.

---

## Question 3: How realistic is the oblivious-support outlier model, and how can `PolyakSGM` / `SuperPolyak` be run under corruption ($\alpha > 0$) when $f(\beta^*) = \frac{1}{m}\sum_{i \in S_{\mathrm{bad}}} |\xi_i|$ is unknown?

- **Why a referee will ask this:**
  1. In Theorem 5.1, $S_{\mathrm{bad}}$ must be fixed independently of $\{a_i\}$, though $\xi_i$ ($i \in S_{\mathrm{bad}}$) may depend arbitrarily on $\{a_i\}$. An adversary who also *chooses* $S_{\mathrm{bad}}$ after seeing $\{a_i\}$ is strictly stronger.
  2. Corollary 5.3 invokes `PolyakSGM` and `SuperPolyak`, whose step size $\frac{f(\beta_k) - f^*}{\|g_k\|^2}$ requires knowing $f^* = f(\beta^*)$. When $\alpha = 0$ (noiseless), $f^* = 0$ is known; when $\alpha > 0$, $f^* = \frac{1}{m}\sum_{i \in S_{\mathrm{bad}}} |\xi_i| > 0$ is generally unknown!
- **Concrete evidence in hand:**
  - **Adversary boundary is explicitly characterized:** Section 6.3 (`Exp. C` / `adversarial_tests.py` Test 5) explicitly demonstrates that an **omniscient-location adversary** (choosing $S_{\mathrm{bad}}$ based on $a_i$) breaks local optimality of $\beta^*$ already at $\alpha = 0.25$ (consistent with the classic breakdown barrier for adversarial covariate-dependent corruption), whereas Proposition 5.4 (Lean-verified) proves that $\alpha < 1/2$ is tight for oblivious support.
  - **Unknown $f^*$ is explicitly flagged:** Remark after Corollary 5.3 in Section 5.5 explicitly points out that $f(\beta^*) = 0$ is known only in the noiseless regime ($\alpha = 0$), whereas under unknown $f(\beta^*) > 0$ ($\alpha > 0$), geometrically decaying step-size subgradient methods (Davis, Drusvyatskiy, & Paquette 2020; Charisopoulos & Davis 2024) or adaptive Polyak variants are needed instead of exact-target `PolyakSGM`.
- **Honest residual gap:**
  - For $\alpha > 0$, we prove the **geometric sharpness condition** $f(\beta) - f(\beta^*) \ge \frac{\gamma}{4}\|\beta - \beta^*\|_F$ (and local uniqueness of $\beta^*$ as the strict minimizer in $B(\beta^*, \rho)$), but we do **not** provide a new convergent algorithm that estimates $f(\beta^*)$ automatically under arbitrary unbounded outliers.

---

## Question 4: Theorem 5.1 is only *local* (radius $\rho \propto \frac{\gamma}{r-1}\Delta_{\min}$), and does not rule out spurious *higher-valued* local minima inside $B(\beta^*, \rho)$ — unlike Theorem 3.1, which is *global* for $r = 2$. Why?

- **Why a referee will ask this:**
  1. Sharpness relative to $\beta^*$, i.e., $f(\beta) - f(\beta^*) \ge \frac{\gamma}{4}\|\beta - \beta^*\|_F$ on $B(\beta^*, \rho)$, proves that $\beta^*$ is the **unique global minimizer on $B(\beta^*, \rho)$**, NOT that $f$ has no Clarke stationary points or higher-valued local minima inside $B(\beta^*, \rho) \setminus \{\beta^*\}$.
  2. For $r = 2$, Theorem 3.1 achieves a *global, scale-free* population bound $F(\beta) \ge \frac{\sqrt{2}-1}{\sqrt{\pi}}\mathrm{dist}(\beta, X_{\mathrm{pop}}^*)$ even as $\Delta_{\min} = \|v\|_2 \to 0$. Yet Theorem 5.1 collapses its radius $\rho \to 0$ as $\Delta_{\min} \to 0$.
- **Concrete evidence in hand:**
  - **Strict honesty about local minima:** The manuscript (Section 5.1 Remark, Section 5.5) explicitly distinguishes *"unique minimizer on $B(\beta^*, \rho)$"* from *"absence of higher-valued local minima or Clarke critical points"* (which is why Proposition 2.2's non-weak-convexity matters: without weak convexity, standard gradient-flow / proximal-point monotonicity arguments do not automatically follow from sharpness alone, and `PolyakSGM` relies on the specific sharp-growth + Lipschitz + Polyak step-size geometry of Charisopoulos & Davis 2024).
  - **Why finite-sample global $r=2$ sharpness is harder:** Theorem 3.1's global proof crucially relies on exact **antipodal symmetry** ($a \mapsto -a$, canceling the odd part of $R(a)$ pointwise). In a finite i.i.d.\ sample $\{a_i\}_{i=1}^m$, exact antipodal pairs do not exist; controlling $\frac{1}{m}\sum_i R(a_i)$ globally over all $\beta \in \mathbb{R}^{2 \times d}$ without $\rho \propto \|v\|_2$ requires uniform lower-tail concentration of the nonconvex difference $\max(\langle a, \beta_1\rangle, \langle a, \beta_2\rangle) - \max(\langle a, \beta_1^*\rangle, \langle a, \beta_2^*\rangle)$ across the singular locus $\beta_1 = \beta_2$.
- **Honest residual gap:**
  - Global finite-sample sharpness for $r = 2$ (matching Theorem 3.1 at $m = \Theta(d)$) and initialization schemes for reaching $B(\beta^*, \rho)$ (e.g., spectral / PCA initialization as in Ghosh et al. 2022 or Kim & Lee 2024) are left as open directions in Section 7.

---

## Question 5: How restrictive is the i.i.d.\ $\mathcal{N}(0, I_d)$ covariate assumption, and what exactly is vs. is not verified in Lean 4?

- **Why a referee will ask this:**
  1. Real regression covariates are anisotropic ($\mathcal{N}(0, \Sigma)$) or heavy-tailed / sub-Gaussian, not isotropic $\mathcal{N}(0, I_d)$.
  2. When a paper accompanies its proofs with a Lean 4 formalization, referees rightly check whether the machine-checked statements match the paper verbatim or quietly omit key steps (like measure-theoretic integration, `(A2)`, or degenerate cases).
- **Concrete evidence in hand:**
  - **Anisotropic $\mathcal{N}(0, \Sigma)$ reduction:** Replacing $a_i = \Sigma^{1/2} g_i$ ($g_i \sim \mathcal{N}(0, I_d)$) reduces anisotropic Gaussian covariates immediately to the isotropic case by reparameterizing $\tilde\beta_j = \Sigma^{1/2} \beta_j$, so every theorem transfers verbatim in the $\Sigma$-norm $\|\beta_j - \beta_j^*\|_\Sigma$ (with $\kappa(\Sigma)$ entering only when converting back to Euclidean norm). Extending beyond Gaussian to general sub-Gaussian distributions is genuinely nontrivial because Lemma 4.2, Lemma 4.3, Theorem 3.1, and Lemma 5.7 use rotational invariance / exact 2D polar densities.
  - **Strict four-tier Lean audit (`paper/FORMALIZATION.md` & `formal_statement_audit.md`):**
    - **Fully formalized (kernel-checked from `mathlib` axioms `[propext, Classical.choice, Quot.sound]` alone, 0 `sorry`, 39/39 `#print axioms`):** Theorem 3.1 (all $d \ge 1$, collinear & degenerate cases), Lemma 4.1, Lemma 4.3 (`lemma33_gaussian_bathtub`), Theorem 5.1 (both `α_min`-parameterized and `π_min`-bridged forms, both $\|\cdot\|_{1,2}$ and $\|\cdot\|_F$, all concentration Lemmas 5.5–5.7, and Appendix Lemmas A.1–A.3), and Proposition 5.4.
    - **Explicitly marked as Human Proof Only / Partially Formalized (zero overclaiming):** Proposition 2.1, Proposition 2.2(b) general $K(\beta; E) < 0$ criterion, Proposition 2.3, Lemma 4.2, Proposition 4.4, Theorem 4.5's final assembly, Corollary 5.2's numerical check $3400d + 480\log(6/\delta)$ (verified in Python), and Corollary 5.3's Assumption `(A2)` (semialgebraic active-manifold regularity, cited from Charisopoulos & Davis 2024).
  - **Phase IV.1 audit payoff:** Our Phase IV.1 cross-check actually demonstrated the practical value of the Lean companion: two subtle LaTeX transcription errors in the Phase IV draft (`e^{-16/9}` in Lemmas 5.5/A.2 and `\alpha_{\min}/4` in Theorem 5.1 Part (3)) were immediately confirmed to be LaTeX-only slips because Lean had already forced the exact `e^{-8/9}` and `\gamma/4` statements during compilation.
- **Honest residual gap:**
  - Extension to non-Gaussian (e.g., sub-Gaussian with small-ball anti-concentration) covariates is left to future work (Section 7).
  - Assumption `(A2)` for `SuperPolyak`'s superlinear convergence is cited via semialgebraicity from Charisopoulos & Davis (2024) rather than proved from scratch in Lean.
