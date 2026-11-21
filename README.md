# Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression

[![Lean 4 CI](https://github.com/Vesaluna/sharp-growth-max-linear-regression/actions/workflows/lean.yml/badge.svg)](https://github.com/Vesaluna/sharp-growth-max-linear-regression/actions/workflows/lean.yml)
![Lean v4.35.0](https://img.shields.io/badge/Lean-v4.35.0-blue)
[![Code: Apache-2.0](https://img.shields.io/badge/code-Apache--2.0-green)](LICENSE)
[![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)](LICENSE-CC-BY-4.0)

> **AI-assisted research preprint. Not peer-reviewed. Mathematical and novelty review ongoing.**

**In brief.** Charisopoulos & Davis (2024) observed that simple subgradient methods converge fast and dimension-independently on $\ell_1$ max-linear regression, but did not prove the *sharp growth* property that would explain it. This preprint proves it: near the true parameters, the loss grows at least linearly with the distance to them, with constants that depend neither on the dimension nor on the sample size, and this continues to hold when a fraction $\alpha < 1/2$ of the observations is arbitrarily corrupted, provided the corrupted positions are chosen independently of the covariates (it fails for $\alpha > 1/2$). The main theorems are machine-checked in Lean 4; some supporting results are pen-and-paper only (see [Section 3](#3-actual-scope-of-lean-4-formal-verification)).

This repository contains the research preprint, companion Lean 4 (`v4.35.0`) formal verification library, reproducible Python experiments, and mathematical/novelty/AI-contribution audit records for an investigation of quantitative sharp growth and outlier robustness in $\ell_1$ max-linear regression (motivated by Charisopoulos & Davis, *Mathematics of Operations Research* 2024, Section 5.2.2, catalogued as CAM-Bench Open Problem 107).

- **Preprint PDF (24 pages):** [`paper/main.pdf`](paper/main.pdf) ([LaTeX source](paper/main.tex), [references](paper/references.bib))
- **One-Page Technical Summary:** [`paper/one_page_summary.md`](paper/one_page_summary.md)
- **Lean 4 Verification Guide:** [`paper/FORMALIZATION.md`](paper/FORMALIZATION.md)
- **Reviewer Readiness Brief:** [`paper/reviewer_readiness.md`](paper/reviewer_readiness.md)
- **Audit & Transparency Dossier:**
  - [`docs/mathematical_errata.md`](docs/mathematical_errata.md)
  - [`docs/formal_statement_audit.md`](docs/formal_statement_audit.md)
  - [`docs/novelty_audit_final.md`](docs/novelty_audit_final.md)
  - [`docs/novelty_claims_evidence.md`](docs/novelty_claims_evidence.md)
  - [`docs/ai_contribution_record.md`](docs/ai_contribution_record.md)

> **Note on numbering.** The audit records in `docs/` were written alongside earlier drafts and sometimes refer to results by their numbering at the time (e.g. "Theorem 4", "Corollary 5.2", "Proposition 5.4", "Lemmas 5.5–5.7"). The current manuscript [`paper/main.pdf`](paper/main.pdf) is authoritative; in it, the explicit $r = 2$ corollary is **Corollary 5.3**, the algorithmic corollary is **Corollary 5.4**, the $\alpha > 1/2$ converse is **Proposition 5.5**, and the three probabilistic lemmas are **Lemmas 5.6–5.8**. This README and the files in `paper/` use the current numbering.

---

## 1. Research Problem

Consider the nonconvex, nonsmooth least absolute deviations ($\ell_1$) empirical risk for $r$-component max-linear regression,

$$f(\beta) := \frac{1}{m}\sum_{i=1}^m \Bigl|y_i - \max_{1 \le j \le r} \langle a_i, \beta_j \rangle\Bigr|, \qquad \beta = (\beta_1, \dots, \beta_r) \in \mathbb{R}^{r \times d},$$

with i.i.d. standard Gaussian covariates $a_i \sim \mathcal{N}(0, I_d)$ and observations $y_i = \max_{j \in [r]} \langle a_i, \beta_j^* \rangle + \xi_i$, where $\xi$ is supported on an oblivious index set $S_{\mathrm{bad}} \subseteq [m]$ of fraction $\alpha = |S_{\mathrm{bad}}|/m \in [0, 1/2)$ with arbitrary (possibly unbounded, data-dependent) corruption values.

Unlike quadratic phase retrieval and bilinear low-rank matrix recovery, $f$ is **not weakly convex** in general (Proposition 2.2 gives an exact directional slope-jump criterion). While classical polyhedral error-bound theory (Robinson 1981; Dolgopolik 2023) guarantees qualitative local sharpness for any fixed finite dataset, under Gaussian design in every dimension $d \ge 2$ the active-set stability radius (for $r = 2$) collapses uniformly as $\Theta_{\mathbb{P}}(\|v\|_2 / (m\sqrt{d})) \to 0$ (Proposition 2.3; whereas for $d = 1$ it remains $\|v\|_2/\sqrt{2}$ a.s.). Establishing $(m, d)$-independent sharp growth therefore requires explicitly controlling active-set sign flips.

---

## 2. Summary of Main Results (Theorem 3.1 & Theorem 5.1)

Let $\Delta_{\min} := \min_{j \ne k} \|\beta_j^* - \beta_k^*\|_2$, $C_j^* := \{a \in \mathbb{R}^d : \langle a, \beta_j^* \rangle > \langle a, \beta_k^* \rangle\ \forall k \ne j\}$, $\pi_{\min} := \min_j \mathbb{P}(a \in C_j^*)$, and $\alpha_{\min} := \min_j \inf_{\|u\|_2 = 1} \mathbb{E}[\mathbf{1}_{C_j^*}(a)|\langle a, u \rangle|]$.

### Theorem 3.1 — Global, Scale-Free Population Sharpness for $r = 2$ *(Lean-verified)*
For any $d \ge 1$, any $\beta^* = (\beta_1^*, \beta_2^*) \in \mathbb{R}^{2 \times d}$, and any perturbation $\Delta = (\Delta_1, \Delta_2)$ (with $v := \beta_1^* - \beta_2^*$ and $\delta := \Delta_1 - \Delta_2$), an exact antipodal pairing argument yields the one-sided remainder bound

$$0 \le \frac{\|\Delta_1\|_2 + \|\Delta_2\|_2}{\sqrt{2\pi}} - F(\beta^* + \Delta) \le \frac{\|v\|_2 + \|v + \delta\|_2 - \|2v + \delta\|_2}{\sqrt{2\pi}} \le \frac{\|\delta\|_2^2}{2\sqrt{2\pi}\,\|v\|_2},$$

and hence **global, scale-free sharp growth on all of $\mathbb{R}^{2 \times d}$** (persisting even in the degenerate limit $\beta_1^* = \beta_2^*$):

$$F(\beta) \ge \frac{\sqrt{2} - 1}{\sqrt{\pi}}\,\mathrm{dist}(\beta, X_{\mathrm{pop}}^*) \approx 0.233695\,\mathrm{dist}(\beta, X_{\mathrm{pop}}^*).$$

### Theorem 5.1 — Finite-Sample Sharp Growth Under Oblivious Outliers *(Lean-verified)*
For any $d \ge 1$, $r \ge 2$, $\Delta_{\min} > 0$, $\alpha_{\min} > 0$ (guaranteed unconditionally by $\alpha_{\min} \ge \frac{\sqrt{2\pi}}{6}\pi_{\min}^2$ via Lemma 4.3, also Lean-verified), and any fixed oblivious outlier set $S_{\mathrm{bad}} \subseteq [m]$ with fraction $\alpha \in [0, 1/2)$, set $\gamma := (1 - 2\alpha)\alpha_{\min}$, $\eta := \frac{\gamma}{26(r-1)}$, and $\rho := \frac{\eta}{\sqrt{2}}\Delta_{\min}$. Whenever

$$m \ge \max\!\left\{16d,\; \frac{32}{9}\log\frac{3}{\delta_{\mathrm{fail}}},\; \frac{64}{\gamma^2}\!\left(d\log\!\left(1 + \frac{16}{\gamma}\right) + \log\frac{3r}{\delta_{\mathrm{fail}}}\right),\; \frac{22}{3\eta}\!\left(d\log\frac{9}{\eta} + \log\frac{3r^2}{2\delta_{\mathrm{fail}}}\right)\right\},$$

there exists an event $\mathcal{E}$ of probability at least $1 - \delta_{\mathrm{fail}}$ on which, **simultaneously for every corruption vector $\xi$ supported on $S_{\mathrm{bad}}$**:
1. $f(\beta) - f(\beta^*) \ge \frac{\gamma}{4}\|\beta - \beta^*\|_{1,2} \ge \frac{\gamma}{4}\|\beta - \beta^*\|_F$ for all $\beta \in B(\beta^*, \rho)$;
2. $|f(\beta) - f(\beta')| \le 2\|\beta - \beta'\|_F$ for all $\beta, \beta' \in \mathbb{R}^{r \times d}$;
3. If $\xi \equiv 0$, then $f(\beta) - f^* \ge \frac{\gamma}{4}\mathrm{dist}(\beta, X^*)$ on $B(\beta^*, \rho/2)$ (in particular $\frac{\alpha_{\min}}{4}\mathrm{dist}(\beta, X^*)$ when $S_{\mathrm{bad}} = \emptyset$).

For noiseless $r = 2$ (Corollary 5.3), $m \ge 3400d + 480\log(6/\delta_{\mathrm{fail}})$ gives $f(\beta) - f^* \ge \frac{1}{4\sqrt{2\pi}}\mathrm{dist}(\beta, X^*)$ on $B(\beta^*, \frac{\|v\|_2}{104\sqrt{\pi}})$ with condition ratio $L/\mu \le 8\sqrt{2\pi} \approx 20.05$, directly verifying Assumption `(A1)` of Charisopoulos & Davis (2024). Proposition 5.5 (Lean-verified) proves a matching finite-sample converse for $\alpha > 1/2$, while Section 6 demonstrates empirically that an omniscient-location adversary already breaks local optimality at $\alpha = 0.25$.

---

## 3. Actual Scope of Lean 4 Formal Verification

**Important:** Only specific declarations in `lean/Research107/` are kernel-checked in Lean 4; the manuscript as a whole is **not** fully machine-verified. See [`paper/FORMALIZATION.md`](paper/FORMALIZATION.md) and [`docs/formal_statement_audit.md`](docs/formal_statement_audit.md) for the exact line-by-line boundary:

- **Kernel-checked in Lean 4 (`v4.35.0`, 12 files, 5,851 lines, 0 `sorry`, 39/39 `#print axioms` using only `[propext, Classical.choice, Quot.sound]`):**
  - **Theorem 3.1** (`theorem2_gaussian_remainder_bounds`, `theorem2_unconditional_global_sharpness`, `theorem2_global_quadratic_norm_bound`)
  - **Lemma 4.1** (`lemma31_pointwise_flip_decomp`) and **Lemma 4.3** (`lemma33_gaussian_bathtub`)
  - **Theorem 5.1** (`theorem4_unconditional_probabilistic` and `theorem4_from_pi_min`, covering both $\|\cdot\|_{1,2}$ and $\|\cdot\|_F$, global $2$-Lipschitzness, and noiseless half-radius distance identity)
  - **Lemmas 5.6, 5.7, 5.8, A.1, A.2, A.3** (Gaussian operator norm, cone concentration, flip concentration, volumetric sphere covering, and moment induction)
  - **Proposition 5.5** (`proposition41_prime_breakdown_necessity`)
  - Counterexample and class witness of **Proposition 2.2** (`theorem1b_counterexample_constant`, `theorem1b_class_not_weakly_convex`) and exact algebraic identities of **Corollary 5.3** (`corollary41_exact_identities`)
- **Human proof only (NOT formalized in Lean 4):**
  - **Propositions 2.1, 2.2(b), 2.3, 4.4**
  - **Lemma 4.2** and final assembly of **Theorem 4.5** (general-$r$ population sharp growth)
  - Numerical domination check (`3400d + 480 log(6/δ)`) in **Corollary 5.3** (checked in Python)
  - Semialgebraic active-manifold regularity `(A2)` and algorithmic convergence in **Corollary 5.4** (cited from Charisopoulos & Davis 2024)

---

## 4. Reproducing the Lean 4 Build from a Clean Environment

The Lean project is pinned to `leanprover/lean4:v4.35.0` and `mathlib v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`) with no other external dependencies.

1. Install [`elan`](https://github.com/leanprover/elan) (the Lean version manager).
2. Fetch precompiled `mathlib` `.olean` caches and run `lake build`:
   ```bash
   cd lean
   lake exe cache get
   lake build
   ```
3. Expected result: exit code `0` (`Build completed successfully`) with 39 `#print axioms` lines, each reporting exclusively `[propext, Classical.choice, Quot.sound]`.
4. Optional hygiene check:
   ```bash
   grep -rnE '^\s*(sorry|admit)\b|^axiom |unsafe |implemented_by' Research107/ Research107.lean
   ```

---

## 5. Reproducing the Numerical Experiments

The Python scripts use fixed random seeds and require only `numpy`, `scipy`, and `sympy` (`experiments/requirements.txt`):

```bash
cd experiments
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt

python paper_experiments.py   # Generates results/paper_experiments.json (Tables & Fig. 1)
python adversarial_tests.py   # Runs constant & counterexample checks (results/adversarial_results.json)
python run_experiments.py     # Exploratory sharpness & PolyakSGM diagnostics
```

---

## 6. Peer-Review Status & Ongoing Novelty Uncertainties

- **Not peer-reviewed:** This repository is an open research preprint and verification archive. Its proofs (especially the unformalized pen-and-paper portions listed in Section 3) have not undergone formal journal or conference peer review.
- **Unresolved novelty/overlap risk:** As documented transparently in [`docs/novelty_audit_final.md`](docs/novelty_audit_final.md) and [`docs/novelty_claims_evidence.md`](docs/novelty_claims_evidence.md), we have audited publicly accessible literature (including Charisopoulos & Davis 2024; Robinson 1981; Powell 1984; Womersley 1986; Ghosh et al. 2022; Bagirov et al. 2022; Dolgopolik 2023; Kim & Lee 2024, 2025; Kanj & Lee 2026). However, Kim, Kanj, & Lee announced `RobustPA` (alternating LAD LPs for Gaussian max-affine regression under oblivious outliers up to $\alpha < 1/2$, SIAM MDS24 abstract & Kim 2024 OSU Ph.D. Thesis Ch. 4), whose full proofs are not publicly available as of November 2026. If those unpublished proofs establish uniform active-cone $\ell_1$ lower bounds and uniform pairwise flip bounds, they would directly imply local sharp growth via Lemma 4.1. Additionally, full PDFs of Womersley (1986) and Bagirov et al. (2022) were behind publisher paywalls during our audit (verified via abstracts, DOIs, and secondary citations).

---

## 7. Attribution & Disclosure of AI Assistance

This research preprint was developed by the project owner with substantial AI assistance, recorded in full in [`docs/ai_contribution_record.md`](docs/ai_contribution_record.md):
- **Human Investigator (Project Owner):** Selected the research problem (CAM-Bench Open Problem 107), defined mathematical rigor and anti-overclaiming standards, initiated multi-round independent adversarial audits, mandated zero-`sorry` Lean 4 formalization of the main statistical theorems, enforced correction/retraction of every identified error, and oversees ongoing independent human proof verification.
- **Google DeepMind Antigravity (Autonomous Research Agent):** Used extensively for mathematical proof exploration, derivation, Lean 4 formalization (`lean/Research107/`), numerical experiment implementation (`experiments/`), LaTeX drafting (`paper/main.tex`), and literature cross-checking.
- **OpenAI ChatGPT (Human-Initiated Independent Critique):** Used by the human project owner across multiple audit rounds for independent adversarial review, which uncovered critical mathematical counterexamples and proof gaps (including the non-weak-convexity counterexample, Theorem 5.1 local-uniqueness phrasing, Chernoff exponent / Prop. 4.4 / Lemma 4.2 / Prop. 2.3 $d = 1$ issues, and missed literature leads including Kim–Kanj–Lee 2024 and Kanj & Lee 2026).

No AI system is listed as an author.

---

## 8. Repository Structure

```text
sharp-growth-max-linear-regression/
├── README.md
├── LICENSE                          # Apache-2.0 (Lean 4 and Python code)
├── LICENSE-CC-BY-4.0                # CC BY 4.0 (manuscript and documentation)
├── .github/workflows/lean.yml       # Automated Lean 4 (v4.35.0) CI build
├── paper/                           # LaTeX manuscript, compiled PDF, Lean guide, summary, referee brief
├── lean/                            # Pinned Lean 4 (v4.35.0) + Mathlib4 formalization
├── experiments/                     # Reproducible Python verification & benchmark scripts + JSON outputs
└── docs/                            # Mathematical errata, statement/novelty audits, AI contribution record
```

---

## 9. License

Copyright © 2026 Vesaluna.

- **Code** — the Lean 4 formalization (`lean/`), the Python experiments (`experiments/`), and the CI configuration (`.github/`) — is licensed under the [Apache License 2.0](LICENSE), the same license as `mathlib4`.
- **Text** — the manuscript and its sources (`paper/`, including `main.pdf`, `main.tex`, and `references.bib`), the documentation (`docs/`), and this README — is licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](LICENSE-CC-BY-4.0).

The release tagged `v0.1-research-draft` predates these license files and was published without a license.
