# Sharp Growth and Outlier-Robust Local Recovery in $`\ell_1`$ Max-Linear Regression

> **Status:** **Standalone Research Preprint (AI-assisted). Not peer-reviewed.** Core statistical theorems are machine-checked in Lean 4, while pen-and-paper proofs and Lean-to-LaTeX correspondence have **not** yet undergone independent review by a human mathematician.

**Author:** Haixin Huang (Independent Researcher, Naples, Italy)  
**ORCID:** [0009-0005-5243-0680](https://orcid.org/0009-0005-5243-0680)  
**Contact:** `huanghaixin061028@gmail.com`  
**Zenodo Preprint (`v1.0.0-preprint`, 2026-11-22):** [10.5281/zenodo.24443089](https://doi.org/10.5281/zenodo.24443089) (Version DOI) · [10.5281/zenodo.24443088](https://doi.org/10.5281/zenodo.24443088) (Concept DOI, latest version)  
**Manuscript:** [paper/main.pdf](paper/main.pdf) (20 pages) · **Supplementary Materials:** [paper/supplement.pdf](paper/supplement.pdf) (4 pages)

---

## 1. Overview

This repository accompanies the research preprint *"Sharp Growth and Outlier-Robust Local Recovery in $`\ell_1`$ Max-Linear Regression"*, which studies the nonsmooth, nonconvex least absolute deviations ($`\ell_1`$) empirical risk for $r$-component max-linear regression under isotropic Gaussian covariates $`a_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, I_d)`$:

```math
f(\beta) := \frac{1}{m}\sum_{i=1}^m \Bigl|y_i - \max_{1 \le j \le r} \langle a_i, \beta_j \rangle\Bigr|,
\qquad \beta = (\beta_1, \dots, \beta_r) \in \mathbb{R}^{r \times d}.
```

Unlike quadratic $`\ell_1`$ phase retrieval or low-rank matrix recovery, $f$ is **not weakly convex** in general (**Proposition 2.2**), and its naive active-set stability radius collapses as $`\Theta_{\mathbb{P}}(\|v\|_2/(m\sqrt{d})) \to 0`$ for $`d \ge 2`$ (**Proposition 2.3**). Nevertheless, by replacing active-set freezing with pointwise flip-set decomposition (**Lemma 4.1**) and active-cone Gaussian concentration (**Lemmas 4.3, 5.6–5.8**), we establish non-asymptotic, dimension-free local sharp growth and outlier-robust recovery for arbitrary $`r \ge 2`$.

---

## 2. Main Results (`paper/main.pdf`)

- **Structural Preliminaries (Section 2):**
  - **Proposition 2.1:** Deterministic piecewise-affine error bounds via Robinson (1981) and Dolgopolik (2023), showing coercivity and a global error bound when $`\{a_i\}_{i=1}^m`$ positively spans $`\mathbb{R}^d`$, and a 4-point $d=2, r=2$ counterexample where coercivity and global error bounds fail without positive spanning.
  - **Proposition 2.2:** Non-weak-convexity and directional V-kink criterion: Part (a) gives an explicit $d=1, r=2, m=1$ non-weakly-convex witness, and Part (b) characterizes local non-weak-convexity via the directional slope jump $`K(\beta; E) < 0`$ (paired with a cancellation counterexample refuting the naive active-tie condition).
  - **Proposition 2.3:** Sharp dimensional dichotomy for the active-set stability radius ($d = 1$ invariance $`\rho_{\mathrm{stab}} = \|v\|_2/\sqrt{2}`$ a.s. vs. uniform non-asymptotic $`\Theta_{\mathbb{P}}(\|v\|_2/(m\sqrt{d}))`$ collapse for $`d \ge 2`$).
- **Global $r = 2$ Gaussian Population Sharpness (Section 3):**
  - **Theorem 3.1 & Remark 3.2:** Exact coupled one-sided remainder identity in block coordinates and scale-free global sharpness

    $$
    F(\beta) \ge \frac{\sqrt{2}-1}{\sqrt{\pi}}\,\mathrm{dist}(\beta, X_{\mathrm{pop}}^*)
    $$

    for all $`d \ge 1`$ (Remark 3.2 notes non-optimality of the Frobenius constant via the balanced witness $`\frac{2-\sqrt{2}}{\sqrt{\pi}} \approx 0.330495`$).
- **General-$`r`$ Population Geometry & $`\ell_1`$-vs.-$`\ell_2`$ Conditioning (Section 4):**
  - **Lemmas 4.1–4.3, Proposition 4.4, Theorem 4.5:** Pointwise flip decomposition (**Lemma 4.1**), exact 2D Gaussian polar flip integral (**Lemma 4.2**), universal Gaussian bathtub bound $`\alpha(C) \ge \frac{\sqrt{2\pi}}{6}\pi(C)^2`$ (**Lemma 4.3**), explicit $`\Theta(p^2)`$ vs. $`\Theta(p^3)`$ active-cone conditioning advantage of $`\ell_1`$ over $`\ell_2`$ (**Proposition 4.4**), and general-$`r`$ local population sharp growth (**Theorem 4.5**).
- **Finite-Sample Outlier-Robust Sharp Growth (Section 5):**
  - **Theorem 5.1 & Remark 5.2:** Under isotropic Gaussian covariates and an oblivious fixed corruption subset $`S_{\mathrm{bad}}`$ of fraction $`\alpha < 1/2`$, with high probability over $a$ *simultaneously* for all arbitrary (possibly data-dependent) outlier magnitudes $`\xi`$ supported on $`S_{\mathrm{bad}}`$,

    $$
    f_\xi(\beta) - f_\xi(\beta^*) \ge \frac{(1 - 2\alpha)\alpha_{\min}}{4}\max\bigl(\|\beta - \beta^*\|_{1,2},\, \|\beta - \beta^*\|_F\bigr)
    \qquad \forall \beta \in B(\beta^*, \rho),
    $$

    with global $2$-Lipschitzness and unique local recovery $`\beta^* \in X^*`$ (plus exact half-radius distance identity when $`\xi \equiv 0`$). **Remark 5.2** details the $`\kappa`$-free and $`\log(m/d)`$-free sample complexity structure and its purely geometric $`\pi_{\min}`$-parameterized version via Lemma 4.3.
  - **Corollaries 5.3–5.4:** Explicit noiseless $r = 2$ sample threshold $`m \ge 3400\,d + 480\log(6/\delta_{\mathrm{fail}})`$ (dominating both the cone-event branch $`\approx 1494.35\,d + 402.12\log(6/\delta_{\mathrm{fail}})`$ and flip-event branch $`\approx 3046.45\,d + 477.93\log(6/\delta_{\mathrm{fail}})`$) with $`\rho/2 = \|v\|_2/(104\sqrt{\pi})`$ and $`L/\mu \le 8\sqrt{2\pi}`$ (**Corollary 5.3**), and verification of Assumption `(A1)` in Charisopoulos & Davis (2024, `arXiv:2201.04611`, Prop. 2.1, Thm. 2.1, Cor. 2.3) (**Corollary 5.4**).
  - **Proposition 5.5:** Matching breakdown converse showing recovery fails with probability $`\ge 1 - \exp(-\frac{(2\alpha-1)^2}{2\pi}m)`$ whenever $`\alpha > 1/2`$.

---

## 3. Limitations & Scope Boundary

This preprint explicitly does **not** claim:

- **No global initialization guarantee** under gross outliers (Theorem 5.1 is strictly local in $`B(\beta^*, \rho)`$).
- **No provable $`f(\beta^*)`$-free convergence theorem** for non-weakly-convex sharp losses (Corollary 5.4 applies to oracle-$`f^*`$ Polyak/SuperPolyak methods; the `GeomDecaySGM` experiment in Section 6 and Supplement SM2 is strictly empirical and still uses local initialization $`\|\beta^{(0)}-\beta^*\|_F = 0.25`$).
- **No omniscient adversarial outlier robustness up to $`\alpha < 1/2`$** (selecting $`S_{\mathrm{bad}}`$ adversarially as a function of $a$ breaks sharpness at $`\alpha = 0.25`$, as verified in Supplement SM2 and `experiments/adversarial_tests.py`).
- **No dense observation noise or non-Gaussian covariate theory** (all probabilistic bounds assume $`a_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, I_d)`$ and exact sparse corruptions).

See [docs/verification_boundary_and_open_problems.md](docs/verification_boundary_and_open_problems.md) for the complete verification boundary and the five open problems from Section 7.

---

## 4. Machine-Checked Formal Verification (Lean 4)

The core statistical theorems (**Theorem 3.1**, **Theorem 5.1**, **Proposition 5.5**), all supporting concentration lemmas (**Lemmas 4.1, 4.3, 5.6–5.8**), and **Lemmas A.1–A.3** are formally verified in Lean 4 inside `lean/`:

- **Toolchain:** `leanprover/lean4:v4.35.0` · **Mathlib4:** `v4.35.0` (`56a00585`)
- **Size:** 12 `.lean` files, **5,851 lines**
- **Hygiene:** **0** `sorry`, **0** `admit`, **0** custom `axiom`, **0** `unsafe`/`implemented_by`
- **Axiom check:** All **39** audited `#print axioms` declarations depend exclusively on `[propext, Classical.choice, Quot.sound]`.

Pen-and-paper results (**Propositions 2.1, 2.2(b), 2.3, 4.4**, **Remark 3.2**, **Lemma 4.2**, **Theorem 4.5** assembly, **Corollary 5.3** numerical domination check, **Corollary 5.4** external citations) are **not** formalized in Lean 4 and have not yet been independently audited by a human mathematician. See [paper/FORMALIZATION.md](paper/FORMALIZATION.md) and Table SM1 of [paper/supplement.pdf](paper/supplement.pdf).

---

## 5. Reproducibility

### Rebuild Lean 4 Proofs
```bash
cd lean
lake exe cache get
lake build
```
Expected result: exit code `0`, `Build completed successfully (3803 jobs).`, and 39 standard-axiom lines.

### Rebuild Standalone PDFs
```bash
cd paper
pdflatex -interaction=nonstopmode main.tex && bibtex main && pdflatex -interaction=nonstopmode main.tex && pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode supplement.tex && pdflatex -interaction=nonstopmode supplement.tex
```

### Run Python Numerical Experiments
```bash
python3 -m venv experiments/.venv
experiments/.venv/bin/pip install -r experiments/requirements.txt

# Main manuscript Experiments A–D
experiments/.venv/bin/python experiments/paper_experiments.py

# f(beta*)-free GeomDecaySGM vs. oracle-f(beta*) PolyakSGM (5-seed comparison, Table SM3)
experiments/.venv/bin/python experiments/geom_decay_comparison.py

# Adversarial mathematical stress tests (including omniscient alpha = 0.25 attack)
experiments/.venv/bin/python experiments/adversarial_tests.py
```

Full logs and observed metrics appear in [docs/reproducibility_report.md](docs/reproducibility_report.md).

---

## 6. Repository Structure

```text
.
├── LICENSE                             # Apache License 2.0 (Lean 4, Python code, and CI)
├── CITATION.cff                        # CFF 1.2.0 citation metadata (Zenodo Version & Concept DOIs)
├── RELEASE_NOTES.md                    # Changelog from v0.1-research-draft to v1.0.0-preprint
├── .github/workflows/lean.yml          # Automated Lean 4 (v4.35.0) CI build
├── paper/                              # Standalone preprint LaTeX, PDFs, figures, & formalization guide
│   ├── main.tex, main.pdf              #   Main manuscript (20 pages)
│   ├── supplement.tex, supplement.pdf  #   Standalone Supplementary Materials SM1–SM2 (4 pages)
│   ├── references.bib                  #   29 audited BibTeX entries (29/29 cited)
│   ├── figures/                        #   PGFPlots vector figures (fig_cones.tex, fig_outliers_polyak.tex)
│   └── FORMALIZATION.md                #   Theorem-by-theorem Lean 4 guide
├── lean/                               # Self-contained Lean 4 (v4.35.0) verification project
│   ├── Research107.lean                #   Root module
│   ├── Research107/                    #   11 proof modules (5,851 lines total)
│   └── lean-toolchain, lakefile.toml, lake-manifest.json
├── experiments/                        # Reproducible Python simulations & JSON outputs
│   ├── paper_experiments.py            #   Manuscript Experiments A–D
│   ├── geom_decay_comparison.py        #   5-seed GeomDecaySGM vs. PolyakSGM comparison
│   ├── adversarial_tests.py            #   5 mathematical & omniscient-outlier stress tests
│   ├── run_experiments.py              #   Exploratory diagnostic suite
│   ├── requirements.txt
│   └── results/                        #   Saved JSON datasets
└── docs/                               # Audit reports, errata, bibliography & AI disclosure logs
    ├── bibliography_audit.md           #   Primary-source citation audit (all 29 entries)
    ├── reproducibility_report.md       #   Live Lean, LaTeX, & Python verification report
    ├── verification_boundary_and_open_problems.md
    ├── ai_contribution_record.md       #   Detailed AI assistance record
    ├── formal_statement_audit.md       #   Statement-by-statement Lean audit
    ├── mathematical_errata.md          #   Mathematical errata log
    ├── novelty_audit_final.md          #   Literature & novelty audit
    └── novelty_claims_evidence.md      #   Evidence map for novelty claims
```

---

## 7. Citation

See [CITATION.cff](CITATION.cff). For exact scientific reproducibility of `v1.0.0-preprint`, cite the **Version DOI** (`10.5281/zenodo.24443089`); to refer to the latest version across future updates, use the **Concept DOI** (`10.5281/zenodo.24443088`):

```bibtex
@misc{huang2026sharpgrowth,
  author    = {Haixin Huang},
  title     = {Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression},
  year      = {2026},
  month     = {November},
  publisher = {Zenodo},
  version   = {1.0.0-preprint},
  doi       = {10.5281/zenodo.24443089},
  url       = {https://doi.org/10.5281/zenodo.24443089},
  note      = {Research Preprint (not peer-reviewed). Concept DOI: 10.5281/zenodo.24443088. Code and Lean 4 proofs: \url{https://github.com/Vesaluna/sharp-growth-max-linear-regression}}
}
```

---

## 8. License

Copyright © 2026 Haixin Huang (Vesaluna).

- **Archived Preprint Manuscript Text (Zenodo `1.0.0-preprint`):** The archived preprint manuscript deposited on Zenodo ([`10.5281/zenodo.24443089`](https://doi.org/10.5281/zenodo.24443089) — `main.pdf`, `supplement.pdf`, and the corresponding archived manuscript LaTeX sources in that release) is licensed under [Creative Commons Attribution 4.0 International (CC BY 4.0)](https://creativecommons.org/licenses/by/4.0/).
- **Code:** The Lean 4 formalization (`lean/`), the Python experiments (`experiments/`), and the CI configuration (`.github/`) are licensed under the [Apache License 2.0](LICENSE), the same license as `mathlib4`.
- **Other Repository Files & Unarchived Revisions:** Other files in this repository that are not explicitly covered above (including repository documentation in `docs/`, `README.md`, `RELEASE_NOTES.md`, and any future unarchived manuscript revisions unless explicitly licensed) are **not** granted a CC BY 4.0 or Apache-2.0 license by default; all rights are reserved unless stated otherwise. Previously distributed versions carrying CC BY 4.0 remain subject to that license (removing or changing a notice does not revoke already granted rights). The earliest release tagged `v0.1-research-draft` predated these license files and was published without a license.

---

## 9. AI Contribution Disclosure

This research preprint, its Lean 4 formalization, and its numerical scripts were developed by **Haixin Huang** with substantial assistance from AI systems (Google Antigravity and OpenAI ChatGPT) across mathematical exploration, proof drafting, Lean 4 formalization, independent error auditing, bibliography checking, and typesetting. All claims, limitations, and final editorial responsibilities rest with the human author. A detailed role-by-role record is preserved in [docs/ai_contribution_record.md](docs/ai_contribution_record.md).
