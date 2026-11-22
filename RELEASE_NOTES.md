# Release Notes — `v1.0.0-preprint` (Final Archival Release Candidate)

**Date:** 2026-11-22  
**Author:** Haixin Huang (ORCID: [0009-0005-5243-0680](https://orcid.org/0009-0005-5243-0680))  
**Status:** Standalone Research Preprint (AI-assisted, **not peer-reviewed**, local release candidate prepared for manual Zenodo archival; **not yet uploaded or published**).

---

## Summary of Changes from Earlier Versions

### 1. Standalone Preprint Typography
- Formatted the manuscript as a clean standalone `article`-class preprint (`paper/main.pdf`, 20 pages) paired with a completely standalone Supplementary Materials PDF (`paper/supplement.pdf`, 4 pages, SM1–SM4).
- Removed all journal-review chrome: SIAM review footer (`This manuscript is for review purposes only.`), left-margin review line numbers, SIMODS submission title-page footnote, and SIAM-specific AI editorial policy phrasing.
- Resolved a TeX Live 2026 `cleveref` + `amsthm` shared-counter labeling issue via `\AddToHook{env/.../begin}{\crefalias{theorem}{...}}` so every theorem, proposition, lemma, corollary, remark, and figure cross-reference renders cleanly; both PDFs compile with **0** warnings, **0** errors, and **0** overfull `\hbox`es.

### 2. Mathematical & Proof Refinements (vs. `v0.1-research-draft` and Phase VII/VIII)
- **Theorem 3.1 & Remark 3.2:** Removed the erroneous Phase VII optimality claim for $\frac{\sqrt{2}-1}{\sqrt{\pi}}$ in Frobenius norm; added **Remark 3.2** explicitly documenting non-optimality via the balanced perturbation witness $\beta^* = (e_1, -e_1), \beta = (e_2, -e_2)$ ($d \ge 2$), where $F(\beta) = \frac{4-2\sqrt{2}}{\sqrt{\pi}}$ and $F(\beta)/\operatorname{dist}(\beta, X_{\mathrm{pop}}^*) = \frac{2-\sqrt{2}}{\sqrt{\pi}} \approx 0.330495$.
- **Proposition 2.1:** Verified exact 4-point $d=2, r=2$ counterexample with explicit minus sign (`((0, -1), (0, 1))`) alongside the directional curvature jump characterization $K(\beta; E) < 0$.
- **Proposition 2.3:** Preserved the exact $d = 1$ invariance ($\rho_{\mathrm{stab}} = \|v\|_2/\sqrt{2}$ a.s.) versus uniform non-asymptotic $d \ge 2$ Beta tail collapse.
- **Theorem 5.1 & Remark 5.2:** Verified Part (3) noiseless half-radius distance identity and exact quantifier order (fixed oblivious corruption subset $S_{\mathrm{bad}}$ and fixed signs, simultaneous uniformity over all arbitrary data-dependent corruption magnitudes $\xi$ supported on $S_{\mathrm{bad}}$).
- **Corollary 5.3:** Tightened explicit noiseless $r = 2$ sample complexity thresholds to $1495d + 403\log(6/\delta)$ (tight $\alpha_{\min} = \frac{1}{\sqrt{2\pi}}$) and $3047d + 478\log(6/\delta)$ (generic $\pi_{\min} = 1/2$).

### 3. Primary-Source Bibliography Corrections (4 Concrete Fixes vs. Phase VIII)
All 29 BibTeX entries (29/29 cited in `paper/main.tex`) were audited in `docs/bibliography_audit.md`:
1. **`kim2024thesis`:** Corrected title to the official OhioLINK record ***Nonlinear Inverse Problems: Efficient and Guaranteed Algorithms*** (`osu1732636662590036`) and removed unverified `"Chapter 4"`, `"extended toward 1/2"`, and `"RobustPA"` acronym claims from `paper/main.tex`.
2. **`charisopoulos2024superpolyak`:** Fixed mis-cited `Corollary 2.1` $\to$ **Corollary 2.3** (`cor:corsuperpolyak`) and `Figure 3` $\to$ **Figure 5** (`fig:max-linear-regression`), verified directly against the `arXiv:2201.04611` LaTeX source, and explicitly qualified as `(in arXiv:2201.04611)` because the paywalled *Math. Oper. Res.* 49(3) PDF was not inspected.
3. **`kanj2026sparse`:** Updated to published *SIAM J. Math. Data Sci.* **8(4):1155–1178 (2026)** (`10.1137/24M1709303`).
4. **`dolgopolik2023nonlocal`:** Directly verified `Theorem 4`, `Proposition 1`, and `Corollary 2` against `arXiv:2210.02606` (`PWAff_ErrorBounds.tex`).

### 4. New Numerical Diagnostic Experiment (`GeomDecaySGM` vs. Oracle-$f(\beta^*)$ `PolyakSGM`)
- Added `experiments/geom_decay_comparison.py` and `experiments/results/geom_decay_comparison.json` (plus Figure 1 overlay and Table SM3 in `paper/supplement.pdf`), comparing an $f(\beta^*)$-free normalized geometric step-decay schedule $(\lambda_0, q) = (0.04, 0.95)$ against oracle-$f(\beta^*)$ `PolyakSGM` over 5 seeds under Experiment D ($d=20, r=3, m=500$, $\pm 100$ oblivious outliers, $\alpha \in \{0.00, 0.20, 0.30, 0.40\}$).
- Explicitly documented that both methods use local initialization $\|\beta^{(0)} - \beta^*\|_F = 0.25$ and serve solely as empirical illustrations of the local sharpness landscape rather than a proved practical solver.

### 5. Lean 4 Formal Verification & Repository Packaging
- Re-verified the frozen Lean 4 (`v4.35.0`) proof archive live on 2026-11-22: `lake build` exited `0` (`3803 jobs`), 12 `.lean` files, **5,851 lines**, **0** `sorry`/`admit`/custom `axiom`, **39/39** `#print axioms` checks reporting exclusively `[propext, Classical.choice, Quot.sound]`.
- Added three standalone audit reports: `docs/bibliography_audit.md`, `docs/reproducibility_report.md`, and `docs/verification_boundary_and_open_problems.md`.
- Removed obsolete `v0.1` summary files with superseded theorem numbering from `paper/` and updated `paper/FORMALIZATION.md` to match the final numbering.
- Preserved the repository's existing Apache License 2.0 (`LICENSE`) for code (`lean/`, `experiments/`, `.github/`) and existing all-rights-reserved / non-revoked prior CC BY 4.0 licensing notice for manuscript text, and added `CITATION.cff` ready for Zenodo DOI archival.
