# Claim-by-Claim Originality Evidence & Uncertainty Dossier

**Date:** 2026-11-21  
**Companion to:** [novelty_audit_final.md](novelty_audit_final.md) and [paper/main.tex](../paper/main.tex)

This file records, for every substantive mathematical claim in our manuscript, (1) the concrete supporting evidence, (2) potential counter-evidence or adjacent precedents, (3) inaccessible/paywalled/unpublished materials, and (4) remaining uncertainty that only a domain specialist or future publications can resolve.

---

### Claim 1: Theorem 3.1 — Exact $r = 2$ Antipodal Remainder & Global Scale-Free Sharpness $F(\beta) \ge \frac{\sqrt{2}-1}{\sqrt{\pi}}\dist(\beta, X_{\mathrm{pop}}^*)$
- **Classification:** Tier 2 — *Original Candidate (No Equivalent Found in Audited Public Literature)*.
- **Supporting evidence:**
  - Audited Charisopoulos & Davis (2024, `arXiv:2201.04611`), Duchi & Ruan (2019), Davis, Drusvyatskiy, & Paquette (2020), Ghosh et al. (2022), Kim & Lee (2024, 2025 `arXiv:2404.15302`), Kim (2024 Thesis), Kanj et al. (2026), and Kanj & Lee (2026 `arXiv:2605.06959`).
  - Phase-retrieval papers study either quadratic loss $\E|\ip{a}{x}^2 - \ip{a}{x^*}^2|$ (whose growth modulus vanishes as $\norm{x^*}_2 \to 0$) or the 1-vector symmetric slice $\beta_2 = -\beta_1$. None derives the exact antipodal pairing formula $R(a)+R(-a) = \psi_u(D_1)-\psi_u(D_1+X)$, the closed-form remainder $\frac{\norm{v}_2+\norm{v+\delta}_2-\norm{2v+\delta}_2}{\sqrt{2\pi}}$, or the global constant $\frac{\sqrt{2}-1}{\sqrt{\pi}}$ on all of $\R^{2\times d}$ including $\beta_1^* = \beta_2^*$.
  - Unconditionally machine-checked in Lean 4 (`theorem2_unconditional_global_sharpness`).
- **Potential counter-evidence / adjacent results:**
  - The 2D Gaussian wedge integral $\E[\ind_{\{\ip{a}{v}\ip{a}{w}<0\}}\min(|\ip{a}{v}|, |\ip{a}{w}|)]$ uses elementary 2D polar integration of the same flavor as Grothendieck / Sheppard-type Gaussian angle integrals, so an isolated special case could exist in geometric probability or ReLU-network population-loss papers outside the max-affine literature we searched.
- **Unobtainable materials:** Full text of paywalled papers (Bagirov et al. 2022; Womersley 1986), though both are deterministic fixed-data papers and do not compute Gaussian expectations.
- **Residual uncertainty:** **Low**, pending a check by an optimization/statistical-learning specialist familiar with 2-neuron ReLU / leaky-ReLU population $\ell_1$ landscapes.

---

### Claim 2: Lemma 4.3 & Proposition 4.4 — Gaussian Bathtub Bound $\alpha_j \ge \frac{\sqrt{2\pi}}{6}\pi_j^2$ and Exact $\Theta(p^2)$ vs. $\Theta(p^3)$ Cone Conditioning Separation
- **Classification:** Tier 2 / Tier 3 — *Original Quantitative Comparison Built on Elementary Rearrangement*.
- **Supporting evidence:**
  - Ghosh et al. (2022, IEEE TIT 68(3):1851–1885) and Kim & Lee (2024, SIMODS) establish $\ell_2$ active-cone conditioning scaling as $\pi_{\min}^3$ without contrasting it against $\ell_1$ cone conditioning.
  - Our Proposition 4.4 computes the exact diagonal Gram matrix $G_p$ on the narrow 2D wedge $C_p$ for all $d \ge 2$ ($\lambda_{\min}(G_p) = p - \frac{\sin(2\pi p)}{2\pi} = \frac{2\pi^2}{3}p^3 + O(p^5)$) alongside the two-sided $\ell_1$ bound $\frac{\sqrt{2\pi}}{6}p^2 \le \alpha_{\ell_1}(C_p) \le \frac{1-\cos(\pi p)}{\sqrt{2\pi}} = \frac{\pi^{3/2}}{2\sqrt{2}}p^2 + O(p^4)$, with Lemma 4.3 Lean-verified (`lemma33_gaussian_bathtub`).
- **Potential counter-evidence / adjacent results:**
  - The bathtub rearrangement principle ($\E[\ind_C |Z|] \ge \E[\ind_{\{|Z|\le t\}} |Z|]$) is a standard measure-theoretic rearrangement inequality (Hardy–Littlewood / Neyman–Pearson type). An analogous $\pi_j^2$ lower bound could appear as an auxiliary lemma inside an unpublished LAD max-affine proof (such as Kim–Kanj–Lee's `RobustPA`).
- **Unobtainable materials:** Unpublished proofs of Kim, Kanj, & Lee (2024).
- **Residual uncertainty:** **Low-to-Moderate** (rearrangement tool is standard; the explicit $\frac{\sqrt{2\pi}}{6}p^2$ constant and $\ell_1$-vs.-$\ell_2$ comparison are clean and specific).

---

### Claim 3: Theorem 4.5 — General-$r$ Population Sharp Growth on $B(\beta^*, \rho_{\mathrm{pop}})$ with Zero $\kappa$-Dependence
- **Classification:** Tier 2 — *Original Candidate (Population Benchmark)*.
- **Supporting evidence:**
  - No audited paper derives the explicit population bound $|F(\beta^*+\Delta) - \sum_j \E[\ind_{C_j^*}|\ip{a}{\Delta_j}|]| \le \frac{r\Fnorm{\Delta}^2}{2\sqrt{2\pi}\Delta_{\min}}$ or the $\kappa$-free local radius $\rho_{\mathrm{pop}}$.
- **Potential counter-evidence / adjacent results:**
  - Follows cleanly once Lemmas 4.1–4.3 are assembled; serves primarily as a clean conceptual precursor to the harder finite-sample Theorem 5.1.
- **Unobtainable materials:** Unpublished Kim–Kanj–Lee (2024) proofs.
- **Residual uncertainty:** **Low-to-Moderate**.

---

### Claim 4: Theorem 5.1 & Corollary 5.2 — Finite-Sample High-Probability Sharp Growth (`(A1)`) for General $r \ge 2$ Under Oblivious Arbitrary-Magnitude Outliers ($\alpha < 1/2$)
- **Classification:** **Tier 2 (No Published Equivalent Found)** AND **Tier 4 (Unresolved Overlap Risk With Unpublished Kim–Kanj–Lee `RobustPA`)**.
- **Supporting evidence:**
  - Directly resolves the open verification problem in Charisopoulos & Davis (*Math. Oper. Res.* 2024, Sec. 5.2.2); none of the 12 forward citations tracked on OpenAlex (`W4385878155`) addresses it.
  - All published general-$r$ max-affine/DoMA statistical papers (Ghosh et al. 2022; Kim–Bahmani–Lee 2024; Kim–Lee 2024; Kanj–Kim–Lee 2026; Kanj–Lee 2026) analyze $\ell_2$ least squares or convex relaxations, not the nonconvex $\ell_1$ objective $f$.
  - Published piecewise-linear $\ell_1$ optimization papers (Womersley 1986; Bagirov et al. 2022) are deterministic fixed-data analyses without Gaussian sample complexity or sharp growth constants.
  - Published robust LAD phase retrieval (Kim & Lee 2025, `arXiv:2404.15302`) treats only the 1-vector symmetric case ($r=2, \beta_2 = -\beta_1$), proves alternating LP contraction for $\alpha \le 1/4$ (Thm. 4), and incurs a $\log(m/d)$ factor in its wedge lemma (`Lemma 1`). Our Theorem 5.1 covers arbitrary $r \ge 2$, arbitrary oblivious $\alpha < 1/2$, removes $\log(m/d)$ and $\kappa$, outputs explicit constants in both $\Lonenorm{\cdot}$ and $\Fnorm{\cdot}$, and is unconditionally Lean-verified (`theorem4_unconditional_probabilistic`, `theorem4_from_pi_min`).
- **Potential counter-evidence / overlap risks:**
  1. **Unpublished `RobustPA` (Kim, Kanj, & Lee, SIAM MDS24 abstract Oct. 2024; Kim 2024 Thesis Ch. 4):** As analyzed in `novelty_audit_final.md` Sec. 3, even though `RobustPA` is an alternating LP algorithm, a finite-sample convergence proof for `RobustPA` under Gaussian design and sparse outliers naturally requires (i) a uniform signed $\ell_1$ active-cone lower bound and (ii) a uniform pairwise flip-wedge upper bound — and **those two geometric events directly imply sharp growth of $f$ via Lemma 4.1**.
  2. **1-vector symmetric slice ($r=2, \beta_2 = -\beta_1$):** Can be indirectly inferred from Kim & Lee (`arXiv:2404.15302`) concentration lemmas (with weaker $\alpha \le 1/4$ and $\log(m/d)$ factor).
  3. **Sample complexity conservatism:** Our worst-case dependence on $\pi_{\min}$ is $\tilde O(d/\pi_{\min}^4)$ (when plugging Lemma 4.3 into $\gamma^{-2}$), which is looser than empirical $O(rd)$ scaling for balanced cones.
- **Unobtainable materials:**
  - Unpublished full manuscript/proofs of Kim, Kanj, & Lee (*Least Absolute Deviation Approach to Robust Max-Affine Regression*, SIAM MDS24);
  - Paywalled full PDFs of Bagirov et al. (2022) and Womersley (1986) (audited via metadata/abstracts/secondary citations; neither is a Gaussian statistical-learning paper).
- **Residual uncertainty:** **High regarding unpublished Kim–Kanj–Lee (2024)**; **Low regarding published literature through 2026-11-21**. Must be checked with a domain expert (or directly if Kim–Kanj–Lee publish a preprint) before any journal submission.

---

### Claim 5: Proposition 5.4 — Finite-Sample Converse Necessity of $\alpha < 1/2$ Under Oblivious Support
- **Classification:** Tier 3 — *Elementary Matching Converse (Adjacent to Linear LAD Breakdown)*.
- **Supporting evidence:**
  - Gives an explicit, Lean-verified finite-sample non-local-minimizer certificate using a single fixed corruption vector $\xi_i = \ip{a_i}{\hat h}$ and uniform translations $\tilde\beta(t)$ for general $r \ge 1$, cleanly paired with our empirical demonstration of omniscient-location breakdown at $\alpha = 0.25$.
- **Potential counter-evidence / adjacent results:**
  - Conceptually parallel to standard $50\%$ breakdown of median / linear LAD regression and to Seonho Kim (2024 OSU Thesis, Lemma 5, pp. 41–42) for population linear LAD with oracle phase signs. We present Proposition 5.4 explicitly as a matching converse rather than a standalone major theorem.
- **Residual uncertainty:** **Low** (properly positioned as an elementary converse).

---

### Claim 6: Propositions 2.1, 2.2, 2.3 and Corollary 5.3
- **Classification:** **Tier 1 (Prop. 2.1)** and **Tier 3 (Props. 2.2–2.3, Cor. 5.3)**.
- **Evidence:** Explicitly labeled in `paper/main.tex` as known polyhedral error bound theory (Robinson 1981; Dolgopolik 2023), elementary structural diagnostics (noting Womersley 1986 for deterministic censored LAD optimality), and a direct corollary of Theorem 5.1 + Charisopoulos & Davis (2024, Thms. 1–2). Zero overclaim risk.
