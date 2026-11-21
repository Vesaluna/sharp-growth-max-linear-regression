# Author Responsibility & AI Contribution Record

**Project:** Research Problem 107 (*Sharp Growth and Outlier-Robust Local Recovery in $\ell_1$ Max-Linear Regression*)  
**Last Updated:** 2026-11-21 (Phases I–V)  
**Purpose:** Maintain a transparent, auditable record of human versus AI contributions across Phases I–V, identify exactly which mathematical components still require independent human line-by-line verification, and document accurate AI disclosures for the public research preprint repository.

---

## 1. Transparent Attribution of Contributions Across Phases I–V

> **Policy Principle:** AI systems cannot be listed as authors, cannot assume legal or scholarly responsibility, and must never be disguised as human contributions. Likewise, no fabricated institutional affiliation or overstated human proof authorship is permitted.

| Phase / Activity | Human Investigator (Project Owner) | GPT-Assisted Human Review (External Critique Initiated by Human) | Antigravity (Autonomous Research Agent) |
| :--- | :--- | :--- | :--- |
| **Problem selection & framing** | Selected CAM-Bench Open Problem 107 (Charisopoulos & Davis 2024, Sec. 5.2.2), set mathematical rigor standards, explicitly forbade fake novelty or unverified claims, and directed the four-phase audit-and-formalization strategy. | — | Audited original paper (`arXiv:2201.04611`) vs. benchmark wording; diagnosed Robinson/Dolgopolik deterministic resolution vs. quantitative statistical gap. |
| **Literature search & novelty audit** | Ordered independent originality re-audits; insisted on downgrading/retracting overbroad novelty claims and documenting unresolved overlap risks honestly. | Flagged the critical missed literature of **Kim, Kanj, & Lee (2024)** (*SIAM MDS24*, IEEE vTools `m/444323`, OSU PhD Thesis 2024) as well as Kanj & Lee (2026), Bagirov et al. (2022), and Womersley (1986). | Conducted primary-source verification of Charisopoulos & Davis (2024), Robinson (1981), Powell (1984), Womersley (1986), Bagirov et al. (2022), Dolgopolik (2023), Ghosh et al. (2022), Kim–Bahmani–Lee (2024), Kim–Lee (2024 SIMODS, 2025 IEEE TSP), Kim (2024 Thesis), and Kanj & Lee (2026); authored `docs/novelty_audit_final.md` and `docs/novelty_claims_evidence.md`. |
| **Mathematical discovery & error correction** | Enforced strict correction/retraction whenever flaws were identified rather than patching over them. | Identified counterexample refuting the initial non-weak-convexity claim, local minimizer uniqueness overclaim, "optimal 50% breakdown" terminology issue, block-permutation quantifier flaw in Prop. 5.4, Lean–manuscript alignment items (block $\ell_{1,2}$ norm & $\pi_{\min}$ bridge), and errata `E1`–`E3`, `E7` (`docs/mathematical_errata.md`). | Formulated and proved Theorems 3.1, 4.5, 5.1, Lemmas 4.1–4.3, 5.5–5.7, Propositions 2.2, 2.3 (non-asymptotic Beta tail bounds), 4.4, 5.4; discovered and fixed additional algebraic/constant slips across audits (`docs/mathematical_errata.md`). |
| **Computational experiments** | Required reproducibility checks and additional sweeps across dimension, outlier ratio, and separation/condition number. | — | Authored and executed deterministic Python scripts (`experiments/run_experiments.py`, `experiments/adversarial_tests.py`, `experiments/paper_experiments.py`) and archived JSON results in `experiments/results/`. |
| **Lean 4 formalization** | Mandated zero-`sorry`, zero-custom-axiom unconditional verification of the main statistical theorems and explicit separation of verified vs. unverified statements. | Conducted static source reviews of intermediate Lean files, identifying conditional hypotheses and statement-alignment gaps that were subsequently closed. | Authored and built the 12-file, 5,851-line Lean 4 (`v4.35.0`) library (`lean/Research107/`), achieving 39/39 clean `#print axioms` checks (`[propext, Classical.choice, Quot.sound]`), including `theorem2_unconditional_global_sharpness`, `lemma33_gaussian_bathtub`, `theorem4_unconditional_probabilistic`, `theorem4_from_pi_min`, and `proposition41_prime_breakdown_necessity`. |
| **Manuscript & public release archive** | Directed creation of the English LaTeX preprint (`paper/main.tex`), standalone formalization guide (`paper/FORMALIZATION.md`), audit dossier (`docs/`), and public GitHub research preprint archive (`v0.1-research-draft`), while maintaining an ongoing personal comprehension plan to verify every proof independently. | Flagged final pre-release issues `E1`–`E3` and `E7` (`docs/mathematical_errata.md`). | Drafted and updated `paper/main.tex`, `paper/references.bib`, compiled `paper/main.pdf`, proved all errata fixes (`E1`–`E7`), configured GitHub Actions Lean CI (`.github/workflows/lean.yml`), and authored `docs/` audit records. |

---

## 2. Verification Status: Human-Verified vs. AI + Lean-Kernel Checked

To preserve complete intellectual honesty:

### Currently Checked by Lean 4 Kernel + AI Audit (NOT Yet Independently Line-by-Line Checked by the Human Author)
- **Theorem 3.1** (`theorem2_unconditional_global_sharpness`, `theorem2_gaussian_remainder_bounds`)
- **Lemma 4.1** (`lemma31_pointwise_flip_decomp`) and **Lemma 4.3** (`lemma33_gaussian_bathtub`)
- **Theorem 5.1** (`theorem4_unconditional_probabilistic`, `theorem4_from_pi_min`)
- **Proposition 5.4** (`proposition41_prime_breakdown_necessity`)
- **Lemmas 5.5, 5.6, 5.7, A.1, A.2, A.3** and the counterexample/witness parts of **Proposition 2.2**
- *Note:* Lean 4's kernel guarantees logical soundness of the formalized proof terms relative to `mathlib v4.35.0` and Lean's standard axioms `[propext, Classical.choice, Quot.sound]`, **provided** a human mathematician independently verifies that the Lean type signatures faithfully match the mathematical definitions in `paper/main.tex` (audited in `formal_statement_audit.md`).

### Currently Checked Only by AI + Python Numerical Tests (Neither Lean-Verified Nor Human Line-by-Line Verified)
- **Proposition 2.1** (cited from Robinson 1981 / Dolgopolik 2023)
- **Proposition 2.2(b)** (general directional jump formula $K(\beta; E) < 0$)
- **Proposition 2.3** (infinitesimal stability radius decay)
- **Lemma 4.2**, **Proposition 4.4**, and **Theorem 4.5** (general-$r$ population assembly)
- **Corollary 5.2** numerical domination check ($3400d + 480\log(6/\delta)$) and **Corollary 5.3** (`(A2)` semialgebraic regularity link to Charisopoulos & Davis 2024)

### Mandatory Action Required Before Any Human Authorship / Submission
Before submitting this manuscript to any journal, conference, or preprint server (such as arXiv), the human author must:
1. Study and independently verify every proof in `paper/main.tex` to the point of being able to reconstruct and defend every theorem without AI assistance;
2. Independently run `lake build` in `lean/` and verify the type signatures in `Theorem2Probabilistic.lean`, `Theorem4Probabilistic.lean`, and `ConeConcentration.lean` against `paper/main.tex`;
3. Obtain feedback from at least one qualified domain mathematician (optimization / high-dimensional statistics) on both correctness and literature positioning;
4. Decide personally on the final author list, affiliation (if any — e.g., independent researcher), and disclosure text.

---

## 3. Ready-to-Use AI Use Disclosure Drafts (For Future Submission)

Below are accurate, honest disclosure templates aligned with current editorial policies of **SIAM Journals**, **INFORMS (*Mathematics of Operations Research*)**, and **arXiv**. The human author should edit and verify these before use.

### Option A: SIAM Journals / INFORMS (*Mathematics of Operations Research*) Disclosure Draft
> **Disclosure of AI Assistance.** Large language model and agentic AI tools (specifically Google DeepMind Antigravity for proof exploration, Lean 4 formalization, numerical coding, and LaTeX drafting, and OpenAI ChatGPT for independent counterexample search and proof auditing) were used extensively during the preparation of this research and manuscript. No AI system is listed as an author. Every core statistical theorem (Theorems 3.1 and 5.1, Lemmas 4.1, 4.3, 5.5–5.7, and Proposition 5.4) has been formally verified in Lean 4 (`v4.35.0`) with zero `sorry`s and only standard axioms, and all remaining mathematical arguments, literature citations, and numerical experiments have been independently reviewed and verified by the human author, who takes full scholarly responsibility for the entire contents of the paper.

*(Important: Do NOT include the final clause "have been independently reviewed and verified by the human author" until you have genuinely completed that independent review!)*

### Option B: Informal Cover Note When Requesting Technical Feedback From a Researcher (Pre-Review Stage)
> **Transparency Note on AI-Assisted Research.** I am an independent student researcher working on CAM-Bench Problem 107 (Charisopoulos & Davis 2024, Sec. 5.2.2). This draft was developed with substantial assistance from AI research tools (Antigravity and ChatGPT) for proof exploration, adversarial error checking, numerical experiments, and Lean 4 formalization (5,851 lines, zero `sorry`, unconditionally verifying Theorems 3.1 and 5.1 and Proposition 5.4). I am currently working through every proof myself and would deeply appreciate any brief technical feedback from a domain expert on mathematical correctness, literature overlap (especially with Kim, Kanj, & Lee 2024–2025), and whether the results warrant further development.
