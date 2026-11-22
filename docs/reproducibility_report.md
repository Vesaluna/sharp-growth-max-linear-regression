# Reproducibility Report

**Date:** 2026-11-22  
**Project:** *Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression*  
**Branch:** `final-zenodo-release-candidate`  
**Scope:** End-to-end verification of Lean 4 formal proofs, standalone LaTeX builds (`paper/main.pdf` and `paper/supplement.pdf`), and Python numerical experiments.

---

## 1. Lean 4 Formal Verification Rebuild

### Environment & Pinned Versions
- **Lean toolchain (`lean/lean-toolchain`):** `leanprover/lean4:v4.35.0`
- **Mathlib4 (`lean/lake-manifest.json`):** tag `v4.35.0`, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`
- **Lean codebase size:** 12 `.lean` files (`lean/Research107.lean` + 11 modules in `lean/Research107/`), **5,851 lines** total.
- **External dependencies:** `mathlib4` only (no external statistics or ML packages).

### Commands Executed Live (2026-11-22)
```bash
# 1. Hygiene audit across all Lean source files
grep -rn "\bsorry\b\|\badmit\b\|^axiom \|unsafe \|implemented_by" lean/Research107/ lean/Research107.lean

# 2. Full project build
cd lean && lake build
```

### Observed Results
- **Hygiene audit:** **0** code matches for `sorry`, `admit`, custom `axiom`, `unsafe`, or `implemented_by` (only docstring text mentions).
- **`lake build`:** Exit code **`0`**, final status: `Build completed successfully (3803 jobs).`
- **`#print axioms` audit:** All **39** audited theorem declarations report exclusively Lean's three standard axioms:
  `[propext, Classical.choice, Quot.sound]`.
- **Clean-machine rebuild command:**
  ```bash
  cd lean
  lake exe cache get
  lake build
  ```

---

## 2. Standalone Preprint LaTeX Build

### Build Commands
```bash
cd paper
pdflatex -interaction=nonstopmode main.tex
bibtex main
pdflatex -interaction=nonstopmode main.tex
pdflatex -interaction=nonstopmode main.tex

pdflatex -interaction=nonstopmode supplement.tex
pdflatex -interaction=nonstopmode supplement.tex
```

### Observed Results (2026-11-22)
- **`paper/main.pdf`:** **20 pages** (`659,178` bytes), **0** errors, **0** warnings, **0** undefined references/citations, **0** overfull `\hbox`es.
  - Compiles using standard `article` class (`11pt`, `1in` margins, `lmodern`, `microtype`, `amsthm`, `natbib` + `abbrvnat`, `cleveref`, `hyperref`, `pgfplots`/`tikz`) with **zero** journal-specific review chrome (no line numbers, no review footer, no SIMODS footnote).
  - Visually inspected page-by-page (pp. 1–20).
- **`paper/supplement.pdf`:** **4 pages** (`SM1`–`SM4`, `422,617` bytes), **0** errors, **0** warnings, **0** overfull `\hbox`es.
  - Compiles completely standalone (no `.aux` cross-dependency on `main.tex`).
  - Contains Section SM1 (Lean 4 verification mapping, `Table SM1`) and Section SM2 (experimental reproducibility tables, `Table SM2` and `Table SM3`).
  - Visually inspected page-by-page (pp. SM1–SM4).

---

## 3. Python Numerical Experiments

### Environment
- **Virtual environment:** `experiments/.venv/`
- **Observed versions:** Python `3.9.6`, `numpy 2.0.2`, `scipy 1.13.1`
- **Requirements file (`experiments/requirements.txt`):** `numpy>=1.24`, `scipy>=1.10`, `sympy>=1.12`

### Scripts, Commands, and Output Artifacts

| Script | Purpose | Command (from repo root) | Output JSON | Live Status |
| :--- | :--- | :--- | :--- | :---: |
| `experiments/paper_experiments.py` | Main manuscript Experiments A–D (Pop. $r=2$, Cone $\ell_1$ vs. $\ell_2$, Active-set stability radius, Oblivious outliers & oracle `PolyakSGM`) | `experiments/.venv/bin/python experiments/paper_experiments.py` | `experiments/results/paper_experiments.json` | Verified (preserved intact from original baseline) |
| `experiments/geom_decay_comparison.py` | New $f(\beta^*)$-free `GeomDecaySGM` vs. oracle-$f(\beta^*)$ `PolyakSGM` 5-seed comparison under Experiment D setup | `experiments/.venv/bin/python experiments/geom_decay_comparison.py` | `experiments/results/geom_decay_comparison.json` | Executed live (`1.46s`, exit `0`) |
| `experiments/adversarial_tests.py` | 5 adversarial mathematical stress tests (non-weak-convexity, 3D Thm. 3.1, Thm. 4.5 edge cases, Thm. 5.1 constants & omniscient $\alpha=0.25$ adversary, Prop. 2.3 radius audit) | `experiments/.venv/bin/python experiments/adversarial_tests.py` | `experiments/results/adversarial_results.json` | Executed live (exit `0`; omniscient gap `-0.011841 < 0`) |
| `experiments/run_experiments.py` | Earlier exploratory diagnostic suite | `experiments/.venv/bin/python experiments/run_experiments.py` | `experiments/results/experiment_results.json` | Preserved archival baseline |

### New Experiment Summary: `GeomDecaySGM` vs. Oracle-$f(\beta^*)$ `PolyakSGM` (`experiments/geom_decay_comparison.py`)

Setup (identical to Experiment D in `paper/main.pdf`, Section 6 and Supplement SM2, Table SM3):
- Problem dimensions: $d = 20$, $r = 3$, $m = 500$, standard Gaussian design $a_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, I_d)$.
- Corruptions: oblivious $\pm 100$ gross outliers on a fixed $\alpha$-fraction subset $S_{\mathrm{bad}}$ ($\alpha \in \{0.00, 0.20, 0.30, 0.40\}$).
- Initialization: identical local perturbation $\|\beta^{(0)} - \beta^*\|_F = 0.25$, run for $T = 250$ iterations across 5 fixed seeds (`20261123`–`20261127`).
- Step sizes:
  - `PolyakSGM`: exact Polyak step size using the **oracle** optimal value $f(\beta^*)$.
  - `GeomDecaySGM`: normalized subgradient step $\beta^{(k+1)} = \beta^{(k)} - \lambda_0 q^k \frac{g^{(k)}}{\|g^{(k)}\|_F}$ with a single fixed $f(\beta^*)$-free schedule $(\lambda_0, q) = (0.04, 0.95)$ across all $\alpha$ values and seeds.

| Outlier fraction $\alpha$ | Oracle-$f(\beta^*)$ `PolyakSGM` final $\|\beta^{(250)} - \beta^*\|_F$ median [min, max] | $f(\beta^*)$-free `GeomDecaySGM` final $\|\beta^{(250)} - \beta^*\|_F$ median [min, max] |
| :---: | :---: | :---: |
| $0.00$ | $2.76 \times 10^{-14}$ $[2.58 \times 10^{-14},\; 3.17 \times 10^{-14}]$ | $8.99 \times 10^{-8}$ $[2.55 \times 10^{-8},\; 9.22 \times 10^{-8}]$ |
| $0.20$ | $1.88 \times 10^{-13}$ $[3.05 \times 10^{-14},\; 1.67 \times 10^{-8}]$ | $6.33 \times 10^{-8}$ $[5.67 \times 10^{-8},\; 7.42 \times 10^{-8}]$ |
| $0.30$ | $1.76 \times 10^{-11}$ $[1.78 \times 10^{-12},\; 1.52 \times 10^{-6}]$ | $8.76 \times 10^{-8}$ $[7.31 \times 10^{-8},\; 8.97 \times 10^{-8}]$ |
| $0.40$ | $7.02 \times 10^{-7}$ $[8.53 \times 10^{-14},\; 2.27 \times 10^{-4}]$ | $9.11 \times 10^{-8}$ $[8.02 \times 10^{-8},\; 9.46 \times 10^{-8}]$ |

### Honest Oracle & Methodological Caveats
1. **`PolyakSGM` requires the unknown oracle value $f(\beta^*)$** whenever $\alpha > 0$ (since $f(\beta^*) > 0$ under gross outliers).
2. **`GeomDecaySGM` removes the $f(\beta^*)$ oracle**, but **both** methods still start from a local initialization $\|\beta^{(0)} - \beta^*\|_F = 0.25$ and `GeomDecaySGM` uses a hand-selected schedule $(\lambda_0, q) = (0.04, 0.95)$.
3. Neither experiment constitutes a proved end-to-end practical solver with global initialization; both serve strictly as numerical illustrations of the local sharp-growth landscape established by Theorem 5.1.

---

## 4. Independent Python Sanity Checks of Pen-and-Paper Calculations

In addition to the main experiment scripts, a standalone Python numerical/symbolic verification pass was run on 2026-11-22 covering every unformalized algebraic/integral calculation in `paper/main.pdf`:
- **Proposition 2.1:** 4-point $d=2, r=2$ non-coercivity counterexample (`((0,1),(0,-1))` and `((0,-1),(0,1))`) — verified exact $X^*$ and failure of coercivity/global error bound without positive spanning.
- **Proposition 2.3:** Uniform Beta/Gamma bounds for $d \in [2, 200]$ — verified numerically.
- **Remark 3.2:** 2D polar quadrature at $\beta^* = (e_1, -e_1), \beta = (e_2, -e_2)$ — verified $F(\beta) = \frac{4 - 2\sqrt{2}}{\sqrt{\pi}}$ and $F(\beta)/\operatorname{dist}(\beta, X_{\mathrm{pop}}^*) = \frac{2 - \sqrt{2}}{\sqrt{\pi}} \approx 0.330495$.
- **Lemma 4.2 & Proposition 4.4:** Polar flip integral and diagonal $\ell_1$/$\ell_2$ cone conditioning formulas — verified numerically.
- **Corollary 5.3:** Exact branch evaluations (`1494.35`, `402.12` for cone event; `3046.45`, `477.93` for flip event) — verified both dominated by $m \ge 3400\,d + 480\log(6/\delta_{\mathrm{fail}})$.
- **Supplement SM2 ($\alpha = 0.25$ omniscient adversary):** Tail bound $e^{-z_{0.25}^2/2} \approx 0.51600 > 0.5$ — verified.

**Important caveat:** Numerical and symbolic sanity checks catch arithmetic errors, but they do **not** substitute for Lean 4 formalization or independent line-by-line review by a human mathematician.
