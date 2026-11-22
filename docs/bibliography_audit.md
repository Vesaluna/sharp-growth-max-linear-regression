# Final Bibliography and Primary-Source Citation Audit

**Date:** 2026-11-22  
**Audited Manuscript:** `paper/main.tex` / `paper/main.pdf` (20 pages) and `paper/references.bib` (29 BibTeX entries, 29/29 cited, 0 uncited).  
**Scope:** Primary-source verification of all cited external theorems, propositions, corollaries, sections, figures, and bibliographic metadata.

---

## 1. Strict Verification Classification

To prevent conflating metadata lookup with full-text verification, every entry and every specific internal citation is tagged with one of three strict statuses:

- **`[VERIFIED-PRIMARY]`**: Open-access LaTeX source or full text was downloaded and inspected directly to verify both bibliographic details and the exact mathematical statement, model, or theorem/section/figure numbering cited in `paper/main.tex`.
- **`[VERIFIED-METADATA]`**: Bibliographic record (authors, title, venue, volume/number/pages/year, DOI or accession ID) was verified via publisher landing page, Crossref/DOI metadata, arXiv abstract, or official university repository record, **without** inspecting a paywalled full PDF. In `paper/main.tex`, these entries are cited only for high-level context or results confirmed through public abstracts/open secondary sources—not uninspected internal page or chapter numbers.
- **`[UNVERIFIED]`**: Full-text details (such as paywalled published renumbering or unpublished proofs) that could **not** be inspected directly and are therefore explicitly bounded or omitted from `paper/main.tex`.

---

## 2. Four Real Citation/Numbering Errors Caught and Repaired (vs. Pre-Release Draft)

During the final primary-source audit on 2026-11-22, four concrete discrepancies from the pre-release draft were detected and fixed in `paper/main.tex` and `paper/references.bib`:

1. **`kim2024thesis` (S. Kim, Ohio State University PhD Thesis, 2024):**
   - *Error in earlier draft:* Cited with an incorrect title (`"Structured Non-Convex Estimation..."`) and made unverified claims referencing `"Chapter 4"`, `"extended toward 1/2"`, and a `"RobustPA"` acronym.
   - *Primary check:* Official OhioLINK ETD Center record (`osu1732636662590036`) confirms the true title is ***Nonlinear Inverse Problems: Efficient and Guaranteed Algorithms*** (The Ohio State University, 2024). The thesis PDF itself was not full-text-inspected.
   - *Fix applied:* Corrected the title and accession note in `paper/references.bib`; removed all unverified `"Chapter 4"`, `"extended toward 1/2"`, and `"RobustPA"` claims from `paper/main.tex` (Section 1 and Section 7 Item 5).
2. **`charisopoulos2024superpolyak` (V. Charisopoulos & D. Davis, *Math. Oper. Res.* 2024 / `arXiv:2201.04611`):**
   - *Error in earlier draft:* Cited `Corollary 2.1` for SuperPolyak local superlinear convergence and `Figure 3` for the Gaussian max-linear regression experiment.
   - *Primary check:* Direct inspection of the `arXiv:2201.04611` LaTeX source confirmed that `\label{cor:corsuperpolyak}` is **Corollary 2.3** (not Corollary 2.1), `\label{thm:polyak_sgm}` is **Theorem 2.1**, `\label{prop:b_reg}` is **Proposition 2.1**, Section **5.2.2** covers max-linear regression, and `\label{fig:max-linear-regression}` is **Figure 5** (not Figure 3).
   - *Fix applied:* Corrected both citations in `paper/main.tex` (Corollary 5.4 and Section 7 Item 3) and explicitly qualified all internal numbering as `(in arXiv:2201.04611)`, because the paywalled *Math. Oper. Res.* 49(3) typeset PDF was not inspected to check whether the journal renumbered theorems or figures.
3. **`kanj2026sparse` (H. Kanj, S. Kim, & K. Lee, *SIAM J. Math. Data Sci.* 2026):**
   - *Update applied:* Verified published SIAM record (`10.1137/24M1709303`) as **Vol. 8, No. 4, pp. 1155–1178 (2026)** and updated `paper/references.bib` accordingly.
4. **`dolgopolik2023nonlocal` (M. V. Dolgopolik, *Set-Valued Var. Anal.* 2023 / `arXiv:2210.02606`):**
   - *Primary check:* Direct inspection of `PWAff_ErrorBounds.tex` from `arXiv:2210.02606` confirmed that `Theorem 4` (`thrm:Robinson`), `Proposition 1` (`prp:UniformLocalErrorBound`), and `Corollary 2` (coercive piecewise-affine functions admit a global error bound) match the exact citations used in Proposition 2.2 of `paper/main.tex`.

---

## 3. Complete Verification Table for All 8 Specific Internal Citations in `paper/main.tex`

| Citation in `paper/main.tex` | Target Work | Specific Internal Reference | Status | Verification Evidence & Boundary |
| :--- | :--- | :--- | :--- | :--- |
| Prop. 2.2 | `robinson1981some` | Proposition 1 | `[VERIFIED-METADATA]` | Classical polyhedral multifunction upper Lipschitzness (Proposition 1 in Robinson 1981) confirmed via Dolgopolik (`arXiv:2210.02606`, Theorem 4 citation & statement) and Pang (1997); paywalled 1981 Springer PDF not directly inspected. |
| Prop. 2.2 | `dolgopolik2023nonlocal` | Theorem 4, Proposition 1 | `[VERIFIED-PRIMARY]` | Directly read in `arXiv:2210.02606` (`PWAff_ErrorBounds.tex`): `thrm:Robinson` = Theorem 4, `prp:UniformLocalErrorBound` = Proposition 1. |
| Prop. 2.2 | `dolgopolik2023nonlocal` | Corollary 2 | `[VERIFIED-PRIMARY]` | Directly read in `arXiv:2210.02606` (`PWAff_ErrorBounds.tex`): Corollary 2 establishes global error bound under coercivity / bounded sublevel sets. |
| Sec. 1, Cor. 5.4 | `charisopoulos2024superpolyak` | Section 5.2.2 | `[VERIFIED-PRIMARY]` | Directly read in `arXiv:2201.04611` LaTeX source (max-linear regression application & open verification of `(A1)`). |
| Cor. 5.4 | `charisopoulos2024superpolyak` | Proposition 2.1 (in `arXiv:2201.04611`) | `[VERIFIED-PRIMARY]` | Directly verified in `arXiv:2201.04611` LaTeX source (`prop:b_reg`: semialgebraic functions with isolated minimizers satisfy `(A2)`). Paywalled MOR 49(3) numbering `[UNVERIFIED]`. |
| Cor. 5.4 | `charisopoulos2024superpolyak` | Theorem 2.1 & Corollary 2.3 (in `arXiv:2201.04611`) | `[VERIFIED-PRIMARY]` | Directly verified in `arXiv:2201.04611` LaTeX source (`thm:polyak_sgm`, `cor:corsuperpolyak`). Paywalled MOR 49(3) numbering `[UNVERIFIED]`. |
| Sec. 7 (Item 3) | `charisopoulos2024superpolyak` | Figure 5 (in `arXiv:2201.04611`) | `[VERIFIED-PRIMARY]` | Directly verified in `arXiv:2201.04611` LaTeX source (`fig:max-linear-regression`). Paywalled MOR 49(3) numbering `[UNVERIFIED]`. |
| Lem. 5.6, 5.7, 5.8 | `vershynin2018high` | Corollary 4.2.13 | `[VERIFIED-PRIMARY]` | Standard volumetric covering number of the unit Euclidean sphere $\mathcal{N}(\mathbb{S}^{d-1}, \varepsilon) \le (1 + 2/\varepsilon)^d$ (Vershynin 2018, Cor. 4.2.13); also independently proved from scratch inside Lean 4 (`exists_sphere_eps_net` in `GaussianModel.lean`). |

---

## 4. Entry-by-Entry Audit of `paper/references.bib` (All 29 Entries)

| # | BibTeX Key | Authors & Year | Venue / Identifier | Status | Notes / Primary Source Checked |
| :-: | :--- | :--- | :--- | :---: | :--- |
| 1 | `bagirov2022robust` | Bagirov, Taheri, Karmitsa, Sultanova, Asadi (2022) | *Optim. Methods Softw.* 37(4):1289–1309, DOI `10.1080/10556788.2020.1855171` | `[VERIFIED-METADATA]` | Metadata & abstract verified; paywalled full PDF not inspected. Cited only for algorithmic context (nonsmooth DC optimization for piecewise-linear $L_1$ regression). |
| 2 | `bandeira2014saving` | Bandeira, Cahill, Mixon, Nelson (2014) | *Appl. Comput. Harmon. Anal.* 37(1):106–125, DOI `10.1016/j.acha.2013.10.002` | `[VERIFIED-METADATA]` | Metadata verified; cited only for real phase retrieval equivalence context in Remark 3.2. |
| 3 | `charisopoulos2021lowrank` | Charisopoulos, Chen, Davis, Díaz, Ding, Drusvyatskiy (2021) | *Found. Comput. Math.* 21(6):1505–1593, DOI `10.1007/s10208-020-09490-9` | `[VERIFIED-METADATA]` | Metadata verified; cited only for weakly convex $\ell_1$ low-rank matrix recovery background. |
| 4 | `charisopoulos2024superpolyak` | Charisopoulos & Davis (2024) | *Math. Oper. Res.* 49(3):1678–1709, DOI `10.1287/moor.2023.1390`, `arXiv:2201.04611` | `[VERIFIED-PRIMARY]` | `arXiv:2201.04611` LaTeX source directly inspected (Prop. 2.1, Thm. 2.1, Cor. 2.3, Sec. 5.2.2, Fig. 5). Paywalled MOR 49(3) PDF numbering `[UNVERIFIED]`. |
| 5 | `davis2018subgradient` | Davis, Drusvyatskiy, MacPhee, Paquette (2018) | *J. Optim. Theory Appl.* 179(3):962–982, DOI `10.1007/s10957-018-1372-8` | `[VERIFIED-METADATA]` | Metadata verified; cited for geometrically decaying subgradient methods on sharp weakly convex functions. |
| 6 | `davis2020nonsmooth` | Davis, Drusvyatskiy, Paquette (2020) | *IMA J. Numer. Anal.* 40(4):2652–2695, DOI `10.1093/imanum/drz031` | `[VERIFIED-PRIMARY]` | `arXiv:1711.09847` source directly inspected for nonsmooth phase retrieval sharpness context. |
| 7 | `davis2024stochastic` | Davis, Drusvyatskiy, Charisopoulos (2024) | *Math. Program.* 207:145–190, DOI `10.1007/s10107-023-02003-w` | `[VERIFIED-METADATA]` | Metadata verified; cited for geometric step-decay motivation in Sec. 1 and Sec. 6 (`GeomDecaySGM`). |
| 8 | `dolgopolik2023nonlocal` | Dolgopolik (2023) | *Set-Valued Var. Anal.* 31, Art. 32, DOI `10.1007/s11228-023-00694-z`, `arXiv:2210.02606` | `[VERIFIED-PRIMARY]` | `arXiv:2210.02606` (`PWAff_ErrorBounds.tex`) directly inspected: Thm. 4, Prop. 1, Cor. 2 verified verbatim. |
| 9 | `duchi2019solving` | Duchi & Ruan (2019) | *Inf. Inference* 8(3):471–529, DOI `10.1093/imaiai/iay015` | `[VERIFIED-PRIMARY]` | `arXiv:1705.02356` source directly inspected for robust quadratic $\ell_1$ phase retrieval ($\alpha < 1/2$ oblivious outliers, weak convexity). |
| 10 | `eldar2014phase` | Eldar & Mendelson (2014) | *Appl. Comput. Harmon. Anal.* 36(3):473–494, DOI `10.1016/j.acha.2013.08.003` | `[VERIFIED-METADATA]` | Metadata verified; cited for real phase retrieval stability context in Remark 3.2. |
| 11 | `ghosh2022maxaffine` | Ghosh, Pananjady, Guntuboyina, Ramchandran (2022) | *IEEE Trans. Inform. Theory* 68(3):1851–1885, DOI `10.1109/TIT.2021.3130717` | `[VERIFIED-PRIMARY]` | `arXiv:1906.09255` source directly inspected for $\ell_2$ max-affine AM, $\kappa$, and $\pi_{\min}^3$ Gram eigenvalue scaling. |
| 12 | `gowda1996analysis` | Gowda (1996) | *SIAM J. Matrix Anal. Appl.* 17(3):594–609, DOI `10.1137/S0895479894278940` | `[VERIFIED-METADATA]` | Metadata verified; cited alongside Robinson/Pang/Dolgopolik for piecewise-affine error bounds. |
| 13 | `hannah2013multivariate` | Hannah & Dunson (2013) | *J. Mach. Learn. Res.* 14(102):3261–3294 | `[VERIFIED-METADATA]` | Open-access JMLR record verified; cited for adaptive convex regression background. |
| 14 | `hoffman1952approximate` | Hoffman (1952) | *J. Res. Nat. Bur. Standards* 49(4):263–265 | `[VERIFIED-METADATA]` | Classical bibliographic record verified; cited for polyhedral error bound origin. |
| 15 | `kanj2026sparse` | Kanj, Kim, & Lee (2026) | *SIAM J. Math. Data Sci.* 8(4):1155–1178, DOI `10.1137/24M1709303` | `[VERIFIED-PRIMARY]` | Published SIMODS Vol. 8(4) metadata verified; `arXiv:2411.17903` source inspected for sparse $\ell_2$ max-affine context. |
| 16 | `kanj2026doma` | Kanj & Lee (2026) | Preprint `arXiv:2605.06959` | `[VERIFIED-PRIMARY]` | `arXiv:2605.06959` source directly inspected for difference-of-max-affine (DoMA) / ABGD $\ell_2$ model context. |
| 17 | `kim2024convex` | Kim, Bahmani, & Lee (2024) | *IEEE Trans. Inform. Theory* 70(3):1897–1912, DOI `10.1109/TIT.2024.3350518` | `[VERIFIED-METADATA]` | Metadata verified; cited for convex programming approach to $\ell_2$ max-linear regression. |
| 18 | `kim2024firstorder` | Kim & Lee (2024) | *SIAM J. Math. Data Sci.* 6(2):534–552, DOI `10.1137/23M1594662` | `[VERIFIED-PRIMARY]` | `arXiv:2207.06505` source directly inspected for first-order $\ell_2$ max-affine regression context. |
| 19 | `kim2024thesis` | Kim (2024) | Ohio State Univ. PhD Thesis, OhioLINK `osu1732636662590036` | `[VERIFIED-METADATA]` | Official OhioLINK title fixed (*Nonlinear Inverse Problems: Efficient and Guaranteed Algorithms*). Full thesis PDF `[UNVERIFIED]`; all uninspected chapter/acronym claims removed from `paper/main.tex`. |
| 20 | `kim2024mds` | Kim, Kanj, & Lee (2024) | SIAM MDS24 Minisymposium MS49 Abstract, p. 44 | `[VERIFIED-METADATA]` | Official MDS24 abstract record verified; full proofs not publicly available and explicitly disclosed as such in Sec. 7 Item 5. |
| 21 | `kim2025robustpr` | Kim & Lee (2025) | *IEEE Trans. Signal Process.* 73:40–54, DOI `10.1109/TSP.2024.3515008` | `[VERIFIED-PRIMARY]` | `arXiv:2404.15302` (`TSP_main.tex`) directly inspected: verified `Robust-AM` for robust phase retrieval with outlier fraction $\alpha \le 1/4$. |
| 22 | `magnani2009convex` | Magnani & Boyd (2009) | *Optim. Eng.* 10(1):1–17, DOI `10.1007/s11081-008-9045-3` | `[VERIFIED-METADATA]` | Metadata verified; cited for convex piecewise-linear fitting background. |
| 23 | `pang1997error` | Pang (1997) | *Math. Program.* 79(1–3):299–332, DOI `10.1007/BF02614322` | `[VERIFIED-METADATA]` | Metadata verified; cited for error bound survey context. |
| 24 | `polyak1969minimization` | Polyak (1969) | *USSR Comput. Math. Math. Phys.* 9(3):14–29, DOI `10.1016/0041-5553(69)90061-5` | `[VERIFIED-METADATA]` | Classical bibliographic record verified; cited for Polyak subgradient step size origin. |
| 25 | `powell1984censored` | Powell (1984) | *J. Econometrics* 25(3):303–325, DOI `10.1016/0304-4076(84)90004-6` | `[VERIFIED-METADATA]` | Metadata verified; cited for classical censored LAD ($r=2$ with one fixed zero component) econometric origin. |
| 26 | `robinson1981some` | Robinson (1981) | *Math. Program. Stud.* 14:206–214, DOI `10.1007/BFb0120929` | `[VERIFIED-METADATA]` | Metadata verified; Proposition 1 cross-checked via Dolgopolik (`arXiv:2210.02606`, Thm. 4); paywalled 1981 full PDF not directly inspected. |
| 27 | `tan2019phase` | Tan & Vershynin (2019) | *Inf. Inference* 8(1):97–123, DOI `10.1093/imaiai/iay005` | `[VERIFIED-METADATA]` | Metadata verified; cited for Gaussian phase-retrieval context. |
| 28 | `vershynin2018high` | Vershynin (2018) | Cambridge University Press, DOI `10.1017/9781108231596` | `[VERIFIED-PRIMARY]` | Corollary 4.2.13 ($\mathbb{S}^{d-1}$ covering number) verified and additionally proved from first principles inside Lean 4 (`exists_sphere_eps_net`). |
| 29 | `womersley1986censored` | Womersley (1986) | *SIAM J. Sci. Stat. Comput.* 7(1):105–122, DOI `10.1137/0907008` | `[VERIFIED-METADATA]` | Metadata verified; paywalled full PDF not directly inspected; cited only for historical censored discrete linear $\ell_1$ approximation context. |

---

## 5. Summary of Remaining Uninspected Primary Texts (`[UNVERIFIED]`)

For complete transparency before archival release or future journal submission:
- **Paywalled MOR 49(3) (2024) final typeset PDF** of Charisopoulos & Davis (`10.1287/moor.2023.1390`): internal numbers (`Proposition 2.1`, `Theorem 2.1`, `Corollary 2.3`, `Figure 5`) are verified against `arXiv:2201.04611` and explicitly labeled as such in `paper/main.tex`.
- **Full PDF of Kim (2024) OSU PhD Thesis** (`osu1732636662590036`) and **unpublished proofs of Kim, Kanj, & Lee (2024)** (MDS24 MS49 abstract): not inspected; Section 7 Item 5 explicitly refrains from making unverified technical overlap claims.
- **Paywalled full PDFs** of Bagirov et al. (2022), Robinson (1981), and Womersley (1986): cited only for standard verified metadata / classical polyhedral background, with zero unverified internal claims.
