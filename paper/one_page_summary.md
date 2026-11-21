# One-Page Technical Summary (For Informal Expert Review)

**Title:** *Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression*  
**Status:** **AI-assisted research preprint. Not peer-reviewed. Mathematical and novelty review ongoing.**  
**Materials:** Full LaTeX manuscript & compiled PDF (`paper/main.tex`, `paper/main.pdf`, 24 pp.), mathematical errata & audit trail (`docs/mathematical_errata.md`, `docs/formal_statement_audit.md`, `docs/novelty_audit_final.md`, `paper/reviewer_readiness.md`), reproducible Python experiments (`experiments/paper_experiments.py`, `experiments/adversarial_tests.py`), and companion Lean 4 (`v4.35.0`) formal verification archive (`lean/`, 5,851 lines, 0 `sorry`, 39/39 standard-axiom `#print axioms` checks).

---

### 1. Problem & Motivation
Consider the nonconvex, nonsmooth $\ell_1$ empirical risk for $r$-component max-linear regression,
$$f(\beta) := \frac{1}{m}\sum_{i=1}^m \Bigl|y_i - \max_{1 \le j \le r} \langle a_i, \beta_j\rangle\Bigr|, \qquad \beta = (\beta_1, \dots, \beta_r) \in \mathbb{R}^{r \times d},$$
with i.i.d.\ standard Gaussian covariates $a_i \sim \mathcal{N}(0, I_d)$ and observations $y_i = \max_{j \in [r]} \langle a_i, \beta_j^*\rangle + \xi_i$, where $\xi$ is supported on an oblivious index set $S_{\mathrm{bad}} \subseteq [m]$ of fraction $\alpha = |S_{\mathrm{bad}}|/m \in [0, 1/2)$ with arbitrary (possibly unbounded, data-dependent) corruption values.

Unlike quadratic phase retrieval (Duchi & Ruan 2019; Davis, Drusvyatskiy, & Paquette 2020) and bilinear low-rank matrix recovery (Charisopoulos et al. 2021), the objective $f$ is **not weakly convex** in general (exact directional jump criterion in Prop. 2.2). Charisopoulos & Davis (*Math. Oper. Res.* 2024, Sec. 5.2.2) observed rapid dimension-independent convergence of `PolyakSGM` and `SuperPolyak` on $f$ and left the verification of quantitative sharp growth (`(A1)`) open. Classical polyhedral theory (Robinson 1981; Dolgopolik 2023) and deterministic nonsmooth piecewise-linear $\ell_1$ analyses (Womersley 1986; Bagirov et al. 2022) settle local optimality or qualitative error bounds for fixed finite datasets, while under Gaussian design in dimension $d \ge 2$ the active-set stability radius (for $r = 2$) collapses uniformly as $\Theta_{\mathbb{P}}(\|v\|_2/(m\sqrt{d})) \to 0$ (Prop. 2.3, whereas for $d = 1$ it remains $\|v\|_2/\sqrt{2}$ a.s.); hence quantitative, $(m, d)$-independent sharp growth requires controlling active-set sign flips explicitly.

### 2. Main Mathematical Results
Let $\Delta_{\min} := \min_{j \ne k}\|\beta_j^* - \beta_k^*\|_2$, $C_j^* := \{a : \langle a, \beta_j^*\rangle > \langle a, \beta_k^*\rangle\ \forall k \ne j\}$, $\pi_{\min} := \min_j \mathbb{P}(a \in C_j^*)$, and $\alpha_{\min} := \min_j \inf_{\|u\|_2=1} \mathbb{E}[\mathbf{1}_{C_j^*}(a)|\langle a, u\rangle|]$.

1. **Global scale-free population sharpness for $r = 2$ (Theorem 3.1 — Lean-verified).**  
   An exact antipodal pairing identity $R(a) + R(-a) = \psi_u(D_1) - \psi_u(D_1 + X) \in [-2\min(X, u), 0]$ and 2D polar integration yield, for all $\beta^* = (\beta_1^*, \beta_2^*)$ and $\Delta = (\Delta_1, \Delta_2)$ ($v = \beta_1^* - \beta_2^*$, $\delta = \Delta_1 - \Delta_2$),
   $$0 \le \frac{\|\Delta_1\|_2 + \|\Delta_2\|_2}{\sqrt{2\pi}} - F(\beta^* + \Delta) \le \frac{\|v\|_2 + \|v + \delta\|_2 - \|2v + \delta\|_2}{\sqrt{2\pi}} \le \frac{\|\delta\|_2^2}{2\sqrt{2\pi}\|v\|_2},$$
   and hence **global, scale-free sharp growth on all of $\mathbb{R}^{2\times d}$** (persisting even as $\beta_1^* \to \beta_2^*$):
   $$F(\beta) \ge \frac{\sqrt{2} - 1}{\sqrt{\pi}}\,\mathrm{dist}(\beta, X_{\mathrm{pop}}^*) \approx 0.233695\,\mathrm{dist}(\beta, X_{\mathrm{pop}}^*).$$
2. **General-$r$ population geometry & $\ell_1$-vs.-$\ell_2$ conditioning (Lemma 4.3, Prop. 4.4, Theorem 4.5).**  
   A Gaussian bathtub bound proves $\alpha_j \ge \frac{\sqrt{2\pi}}{6}\pi_j^2$ (Lean-verified). For $d \ge 2$ and narrow 2D cones $C_p$ of Gaussian measure $p \in (0, 1/2)$, the exact diagonal Gram matrix yields $\lambda_{\min}(G_p) = \Theta(p^3)$ (governing $\ell_2$ max-affine regression, Ghosh et al. 2022; Kim & Lee 2024; Kanj & Lee 2026) versus the two-sided $\ell_1$ cone modulus $\alpha_{\ell_1}(C_p) = \Theta(p^2)$.
3. **Finite-sample sharp growth under oblivious outliers & matching converse (Theorem 5.1, Cor. 5.3–5.4, Prop. 5.5 — Lean-verified).**  
   Using a scale-free $2$-Lipschitz flip surrogate $\varphi_\eta(z_1, z_2) := \max(0, 2|z_2| - |z_1|/\eta)$ with exact 2D polar Bernstein moments ($v_0 = \frac{32}{3}\eta, B = 2$), for $\gamma = (1-2\alpha)\alpha_{\min}$, $\eta = \frac{\gamma}{26(r-1)}$, $\rho = \frac{\eta}{\sqrt{2}}\Delta_{\min}$, and explicit sample complexity $m \gtrsim \frac{d}{\gamma^2}\log\frac{1}{\gamma} + \frac{rd}{\gamma}\log\frac{r}{\gamma} + \frac{r}{\gamma}\log\frac{r^2}{\delta_{\mathrm{fail}}}$ (independent of $\kappa = \Delta_{\max}/\Delta_{\min}$ and without a $\log(m/d)$ factor), with probability $\ge 1 - \delta_{\mathrm{fail}}$, simultaneously for **all** corruption vectors $\xi$ supported on $S_{\mathrm{bad}}$:
   $$f(\beta) - f(\beta^*) \ge \frac{\gamma}{4}\|\beta - \beta^*\|_{1,2} \ge \frac{\gamma}{4}\|\beta - \beta^*\|_F \quad \forall \beta \in B(\beta^*, \rho), \qquad |f(\beta) - f(\beta')| \le 2\|\beta - \beta'\|_F.$$
   For noiseless $r = 2$, $m \ge 3400d + 480\log(6/\delta_{\mathrm{fail}})$ gives $f(\beta) - f^* \ge \frac{1}{4\sqrt{2\pi}}\mathrm{dist}(\beta, X^*)$ on $B(\beta^*, \frac{\|v\|_2}{104\sqrt{\pi}})$ with $L/\mu \le 8\sqrt{2\pi} \approx 20.05$, directly verifying Charisopoulos & Davis `(A1)`. Proposition 5.5 proves a matching finite-sample converse for $\alpha > 1/2$ via uniform translations, whereas an omniscient-location adversary already breaks local optimality at $\alpha = 0.25$.

### 3. Positioning, Overlap Caveat, & Specific Questions for Expert Feedback
Our direct variational sharp-growth analysis differs in loss or framework from $\ell_2$ max-affine / difference-of-max-affine analyses (Ghosh et al. 2022; Kim & Lee 2024; Kanj & Lee 2026), deterministic nonsmooth $\ell_1$ optimization (Womersley 1986; Bagirov et al. 2022), and symmetric phase-retrieval alternating LAD LPs (`Robust-AM`, Kim & Lee *IEEE TSP* 2025). However, we flag an **unresolved overlap risk** with the announced `RobustPA` alternating LAD LP analysis of Kim, Kanj, & Lee (SIAM MDS24 abstract; Kim 2024 OSU Thesis Ch. 4), whose proofs are not yet publicly posted: if `RobustPA`'s Gaussian convergence proof establishes both uniform signed active-cone $\ell_1$ bounds and uniform pairwise flip bounds, those two ingredients would directly imply local sharp growth of $f$ via Lemma 4.1.

Specific questions where expert feedback would be especially valuable:
1. Whether Theorem 3.1 (exact $r=2$ antipodal remainder and global $\frac{\sqrt{2}-1}{\sqrt{\pi}}$ sharpness) or the finite-sample geometry of Theorem 5.1 overlaps with any existing manuscript, including `RobustPA`.
2. Whether the $\tilde O(d/\gamma^2 + (r/\gamma)d)$ sample complexity (worst-case $\tilde O(d/\pi_{\min}^4)$ via Lemma 4.3) can be sharpened cleanly toward $O(rd)$ for balanced cones without losing explicit constants.
3. Whether global finite-sample sharp growth holds for $r = 2$ at $m = \Theta(d)$, matching Theorem 3.1's global population bound.
