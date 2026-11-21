import Research107.Definitions

open scoped BigOperators InnerProductSpace

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Stage A.1: Lemma 3.1 (Deterministic Pointwise Flip Decomposition for all `r ≥ 1`) -/

/-- If `a ∈ activeCone β_star j₀`, then `maxLinearPred hr a β_star = ⟪a, β_star j₀⟫_ℝ`. -/
lemma maxLinearPred_eq_of_mem_activeCone {r : ℕ} (hr : 0 < r)
    (a : E) (β_star : Fin r → E) {j₀ : Fin r} (hj₀ : a ∈ activeCone β_star j₀) :
    maxLinearPred hr a β_star = ⟪a, β_star j₀⟫_ℝ := by
  unfold maxLinearPred
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun k _ => ?_)
    by_cases hkj : k = j₀
    · subst hkj; exact le_rfl
    · exact le_of_lt (hj₀ k hkj)
  · exact Finset.le_sup' (fun j => ⟪a, β_star j⟫_ℝ) (Finset.mem_univ j₀)

/-- Active cones are pairwise disjoint: if `a ∈ activeCone β_star j₁` and `a ∈ activeCone β_star j₂`, then `j₁ = j₂`. -/
lemma activeCone_unique {r : ℕ} (β_star : Fin r → E) {a : E} {j₁ j₂ : Fin r}
    (h1 : a ∈ activeCone β_star j₁) (h2 : a ∈ activeCone β_star j₂) : j₁ = j₂ := by
  by_contra hne
  have hlt1 := h1 j₂ (Ne.symm hne)
  have hlt2 := h2 j₁ hne
  linarith

/-- **Lemma 3.1 (Deterministic Pointwise Flip Decomposition)**:
For any `r ≥ 1`, any `β_star, Δ : Fin r → E`, and any `a` lying in some strict active cone `C_{j₀}^*`:
`| |ŷ(a; β* + Δ) - ŷ(a; β*)| - ∑_j 1_{C_j^*}(a) |⟪a, Δ_j⟫| |`
`≤ ∑_{j < k} |⟪a, (β_j^* - β_k^*) + (Δ_j - Δ_k)⟫| * 1{⟪a, β_j^* - β_k^*⟫ * ⟪a, (β_j^* - β_k^*) + (Δ_j - Δ_k)⟫ < 0}`. -/
theorem lemma31_pointwise_flip_decomp {r : ℕ} (hr : 0 < r)
    (β_star Δ : Fin r → E) (a : E)
    (h_active : ∃ j₀ : Fin r, a ∈ activeCone β_star j₀) :
    let β := fun j => β_star j + Δ j
    let linTerm := open scoped Classical in
      ∑ j : Fin r, if a ∈ activeCone β_star j then |⟪a, Δ j⟫_ℝ| else 0
    let flipTerm := ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
      |⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
        flipInd ⟪a, β_star j - β_star k⟫_ℝ ⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ
    abs (|maxLinearPred hr a β - maxLinearPred hr a β_star| - linTerm) ≤ flipTerm := by
  classical
  intro β linTerm flipTerm
  rcases h_active with ⟨j₀, hj₀⟩
  -- Simplify `maxLinearPred hr a β_star` and `linTerm` using uniqueness of `j₀`
  have h_ystar : maxLinearPred hr a β_star = ⟪a, β_star j₀⟫_ℝ :=
    maxLinearPred_eq_of_mem_activeCone hr a β_star hj₀
  have h_lin : linTerm = |⟪a, Δ j₀⟫_ℝ| := by
    dsimp [linTerm]
    rw [Finset.sum_eq_single j₀]
    · simp [hj₀]
    · intro j _ hne
      have hnot : a ∉ activeCone β_star j := fun hj => hne (activeCone_unique β_star hj hj₀)
      simp [hnot]
    · intro h; exact absurd (Finset.mem_univ j₀) h
  rw [h_ystar, h_lin]
  -- Pick a maximizer `k₀` of `β` at `a`
  have hne_univ : (Finset.univ : Finset (Fin r)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩
  obtain ⟨k₀, _, hk₀_eq⟩ := Finset.exists_mem_eq_sup' hne_univ (fun j => ⟪a, β j⟫_ℝ)
  have h_yhat : maxLinearPred hr a β = ⟪a, β k₀⟫_ℝ := hk₀_eq
  have h_ge_j₀ : ⟪a, β j₀⟫_ℝ ≤ ⟪a, β k₀⟫_ℝ := by
    rw [← hk₀_eq]
    exact Finset.le_sup' (fun j => ⟪a, β j⟫_ℝ) (Finset.mem_univ j₀)
  -- Nonnegativity of every summand in `flipTerm`
  have h_term_nonneg : ∀ j k : Fin r,
      0 ≤ |⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
        flipInd ⟪a, β_star j - β_star k⟫_ℝ ⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ := by
    intro j k
    refine mul_nonneg (abs_nonneg _) ?_
    unfold flipInd
    split_ifs <;> norm_num
  have h_flip_nonneg : 0 ≤ flipTerm :=
    Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => h_term_nonneg j k))
  -- Case split: `⟪a, β k₀⟫ = ⟪a, β j₀⟫` vs `⟪a, β j₀⟫ < ⟪a, β k₀⟫`
  rcases eq_or_lt_of_le h_ge_j₀ with h_eq | h_lt
  · -- No strict flip: LHS is 0
    have hdiff : maxLinearPred hr a β - ⟪a, β_star j₀⟫_ℝ = ⟪a, Δ j₀⟫_ℝ := by
      rw [h_yhat, ← h_eq]
      dsimp [β]
      rw [inner_add_right]
      ring
    rw [hdiff, sub_self, abs_zero]
    exact h_flip_nonneg
  · -- Strict flip: `k₀ ≠ j₀`
    have hkj : k₀ ≠ j₀ := by
      intro h; subst h; exact lt_irrefl _ h_lt
    -- Bound LHS by `|⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫|`
    have h_lhs_le :
        abs (|maxLinearPred hr a β - ⟪a, β_star j₀⟫_ℝ| - |⟪a, Δ j₀⟫_ℝ|) ≤
        |⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫_ℝ| := by
      have h1 := abs_abs_sub_abs_le_abs_sub (maxLinearPred hr a β - ⟪a, β_star j₀⟫_ℝ) ⟪a, Δ j₀⟫_ℝ
      have h2 : (maxLinearPred hr a β - ⟪a, β_star j₀⟫_ℝ) - ⟪a, Δ j₀⟫_ℝ =
          -⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫_ℝ := by
        rw [h_yhat]
        dsimp [β]
        simp only [inner_add_right, inner_sub_right]
        ring
      rw [h2, abs_neg] at h1
      exact h1
    -- Show the flip condition holds strictly for pair `(j₀, k₀)`
    have h_v_pos : 0 < ⟪a, β_star j₀ - β_star k₀⟫_ℝ := by
      rw [inner_sub_right]
      linarith [hj₀ k₀ hkj]
    have h_vd_neg : ⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫_ℝ < 0 := by
      have h_eq' : ⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫_ℝ = ⟪a, β j₀⟫_ℝ - ⟪a, β k₀⟫_ℝ := by
        dsimp [β]
        simp only [inner_add_right, inner_sub_right]
        ring
      linarith
    have h_prod_neg : ⟪a, β_star j₀ - β_star k₀⟫_ℝ * ⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫_ℝ < 0 :=
      mul_neg_of_pos_of_neg h_v_pos h_vd_neg
    -- Match the unordered pair `{j₀, k₀}` into the ordered sum `j < k`
    rcases lt_or_gt_of_ne hkj with hlt_kj | hlt_jk
    · -- Case `k₀ < j₀`: extract term `(k₀, j₀)` from `flipTerm`
      have h_symm_v : ⟪a, β_star k₀ - β_star j₀⟫_ℝ = -⟪a, β_star j₀ - β_star k₀⟫_ℝ := by
        simp only [inner_sub_right]; ring
      have h_symm_vd : ⟪a, (β_star k₀ - β_star j₀) + (Δ k₀ - Δ j₀)⟫_ℝ =
          -⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫_ℝ := by
        simp only [inner_add_right, inner_sub_right]; ring
      have h_ind_one :
          flipInd ⟪a, β_star k₀ - β_star j₀⟫_ℝ ⟪a, (β_star k₀ - β_star j₀) + (Δ k₀ - Δ j₀)⟫_ℝ = 1 := by
        unfold flipInd
        rw [h_symm_v, h_symm_vd, neg_mul_neg]
        simp [h_prod_neg]
      have h_single_le :
          |⟪a, (β_star k₀ - β_star j₀) + (Δ k₀ - Δ j₀)⟫_ℝ| *
            flipInd ⟪a, β_star k₀ - β_star j₀⟫_ℝ ⟪a, (β_star k₀ - β_star j₀) + (Δ k₀ - Δ j₀)⟫_ℝ ≤
          flipTerm := by
        dsimp [flipTerm]
        calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin r => k₀ < k),
              |⟪a, (β_star k₀ - β_star k) + (Δ k₀ - Δ k)⟫_ℝ| *
                flipInd ⟪a, β_star k₀ - β_star k⟫_ℝ ⟪a, (β_star k₀ - β_star k) + (Δ k₀ - Δ k)⟫_ℝ :=
              Finset.single_le_sum (fun k _ => h_term_nonneg k₀ k)
                (Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hlt_kj⟩)
          _ ≤ ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
              |⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
                flipInd ⟪a, β_star j - β_star k⟫_ℝ ⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ :=
              Finset.single_le_sum
                (f := fun j : Fin r => ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
                  |⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
                    flipInd ⟪a, β_star j - β_star k⟫_ℝ ⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ)
                (fun j _ => Finset.sum_nonneg (fun k _ => h_term_nonneg j k))
                (Finset.mem_univ k₀)
      rw [h_ind_one, mul_one, h_symm_vd, abs_neg] at h_single_le
      exact le_trans h_lhs_le h_single_le
    · -- Case `j₀ < k₀`: extract term `(j₀, k₀)` from `flipTerm`
      have h_ind_one :
          flipInd ⟪a, β_star j₀ - β_star k₀⟫_ℝ ⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫_ℝ = 1 := by
        unfold flipInd
        simp [h_prod_neg]
      have h_single_le :
          |⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫_ℝ| *
            flipInd ⟪a, β_star j₀ - β_star k₀⟫_ℝ ⟪a, (β_star j₀ - β_star k₀) + (Δ j₀ - Δ k₀)⟫_ℝ ≤
          flipTerm := by
        dsimp [flipTerm]
        calc _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin r => j₀ < k),
              |⟪a, (β_star j₀ - β_star k) + (Δ j₀ - Δ k)⟫_ℝ| *
                flipInd ⟪a, β_star j₀ - β_star k⟫_ℝ ⟪a, (β_star j₀ - β_star k) + (Δ j₀ - Δ k)⟫_ℝ :=
              Finset.single_le_sum (fun k _ => h_term_nonneg j₀ k)
                (Finset.mem_filter.mpr ⟨Finset.mem_univ k₀, hlt_jk⟩)
          _ ≤ ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
              |⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
                flipInd ⟪a, β_star j - β_star k⟫_ℝ ⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ :=
              Finset.single_le_sum
                (f := fun j : Fin r => ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
                  |⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
                    flipInd ⟪a, β_star j - β_star k⟫_ℝ ⟪a, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ)
                (fun j _ => Finset.sum_nonneg (fun k _ => h_term_nonneg j k))
                (Finset.mem_univ j₀)
      rw [h_ind_one, mul_one] at h_single_le
      exact le_trans h_lhs_le h_single_le

/-! ### Stage A.2: Lemma 4.3(1) (Scale-Free Pointwise Domination by `φ_η`) -/

/-- **Lemma 4.3(1) (Scale-Free Pointwise Domination)**:
For any `η > 0`, `v ≠ 0`, `δ ≠ 0` with `‖δ‖ ≤ η * ‖v‖`, writing `v̂ = (‖v‖⁻¹) • v` and `u = (‖δ‖⁻¹) • δ`,
every `a : E` satisfies:
`(|⟪a, v + δ⟫| / ‖δ‖) * 1{⟪a, v⟫ * ⟪a, v + δ⟫ < 0} ≤ φ_η(⟪a, v̂⟫, ⟪a, u⟫)`,
and in particular `|⟪a, v + δ⟫| * 1{⟪a, v⟫ * ⟪a, v + δ⟫ < 0} ≤ ‖δ‖ * φ_η(⟪a, v̂⟫, ⟪a, u⟫)`. -/
theorem lemma43_part1_scale_free_domination
    {η : ℝ} (hη : 0 < η) {v δ : E} (hv : v ≠ 0) (hδ : δ ≠ 0)
    (h_small : ‖δ‖ ≤ η * ‖v‖) (a : E) :
    (|⟪a, v + δ⟫_ℝ| / ‖δ‖) * flipInd ⟪a, v⟫_ℝ ⟪a, v + δ⟫_ℝ ≤
      phiEta η ⟪a, (‖v‖⁻¹) • v⟫_ℝ ⟪a, (‖δ‖⁻¹) • δ⟫_ℝ := by
  have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hδ_pos : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  unfold flipInd phiEta
  split_ifs with hflip
  · rw [mul_one]
    have h_inner_u : ⟪a, (‖δ‖⁻¹) • δ⟫_ℝ = ‖δ‖⁻¹ * ⟪a, δ⟫_ℝ := inner_smul_right a δ (‖δ‖⁻¹)
    have h_inner_v : ⟪a, (‖v‖⁻¹) • v⟫_ℝ = ‖v‖⁻¹ * ⟪a, v⟫_ℝ := inner_smul_right a v (‖v‖⁻¹)
    rw [h_inner_u, h_inner_v, abs_mul, abs_mul,
        abs_of_pos (inv_pos.mpr hδ_pos), abs_of_pos (inv_pos.mpr hv_pos)]
    -- Since `⟪a, v⟫` and `⟪a, v + δ⟫ = ⟪a, v⟫ + ⟪a, δ⟫` have strictly opposite signs,
    -- `|⟪a, v + δ⟫| + |⟪a, v⟫| = |⟪a, δ⟫|`.
    have h_add : ⟪a, v + δ⟫_ℝ = ⟪a, v⟫_ℝ + ⟪a, δ⟫_ℝ := inner_add_right a v δ
    have h_sum_abs : |⟪a, v + δ⟫_ℝ| + |⟪a, v⟫_ℝ| = |⟪a, δ⟫_ℝ| := by
      rcases mul_neg_iff.mp hflip with ⟨hp, hn⟩ | ⟨hn, hp⟩
      · rw [abs_of_neg hn, abs_of_pos hp]
        have hδ_neg : ⟪a, δ⟫_ℝ < 0 := by linarith
        rw [abs_of_neg hδ_neg]; linarith
      · rw [abs_of_pos hp, abs_of_neg hn]
        have hδ_pos' : 0 < ⟪a, δ⟫_ℝ := by linarith
        rw [abs_of_pos hδ_pos']; linarith
    have h_le1 : |⟪a, v + δ⟫_ℝ| ≤ |⟪a, δ⟫_ℝ| := by linarith [abs_nonneg ⟪a, v⟫_ℝ]
    have h_le2 : |⟪a, v⟫_ℝ| ≤ |⟪a, δ⟫_ℝ| := by linarith [abs_nonneg ⟪a, v + δ⟫_ℝ]
    -- Show `|⟪a, v⟫| / (η * ‖v‖) ≤ |⟪a, δ⟫| / ‖δ‖`
    have h_ratio : ‖v‖⁻¹ * |⟪a, v⟫_ℝ| / η ≤ ‖δ‖⁻¹ * |⟪a, δ⟫_ℝ| := by
      rw [inv_mul_eq_div, inv_mul_eq_div, div_div, div_le_div_iff₀ (mul_pos hv_pos hη) hδ_pos]
      calc |⟪a, v⟫_ℝ| * ‖δ‖ ≤ |⟪a, δ⟫_ℝ| * ‖δ‖ :=
              mul_le_mul_of_nonneg_right h_le2 (le_of_lt hδ_pos)
        _ ≤ |⟪a, δ⟫_ℝ| * (η * ‖v‖) :=
              mul_le_mul_of_nonneg_left h_small (abs_nonneg _)
        _ = |⟪a, δ⟫_ℝ| * (‖v‖ * η) := by ring
    have h_target : |⟪a, v + δ⟫_ℝ| / ‖δ‖ ≤ 2 * (‖δ‖⁻¹ * |⟪a, δ⟫_ℝ|) - ‖v‖⁻¹ * |⟪a, v⟫_ℝ| / η := by
      have h1 : |⟪a, v + δ⟫_ℝ| / ‖δ‖ ≤ ‖δ‖⁻¹ * |⟪a, δ⟫_ℝ| := by
        rw [inv_mul_eq_div]
        exact div_le_div_of_nonneg_right h_le1 (le_of_lt hδ_pos)
      linarith
    exact le_trans h_target (le_max_right _ _)
  · rw [mul_zero]
    exact le_max_left _ _

/-- Scaled version of Lemma 4.3(1) that works uniformly even when `δ = 0`! -/
lemma lemma43_part1_scaled
    {η : ℝ} (hη : 0 < η) {v δ : E} (hv : v ≠ 0) (h_small : ‖δ‖ ≤ η * ‖v‖) (a : E)
    {u : E} (hu : δ = ‖δ‖ • u) :
    |⟪a, v + δ⟫_ℝ| * flipInd ⟪a, v⟫_ℝ ⟪a, v + δ⟫_ℝ ≤
      ‖δ‖ * phiEta η ⟪a, (‖v‖⁻¹) • v⟫_ℝ ⟪a, u⟫_ℝ := by
  by_cases hδ : δ = 0
  · subst hδ
    simp only [add_zero, norm_zero, zero_mul]
    unfold flipInd
    have hnn : ¬ (⟪a, v⟫_ℝ * ⟪a, v⟫_ℝ < 0) := not_lt.mpr (mul_self_nonneg _)
    simp [hnn]
  · have hδ_pos : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
    have hu_eq : u = (‖δ‖⁻¹) • δ := by
      calc u = (1 : ℝ) • u := (one_smul ℝ u).symm
        _ = ((‖δ‖⁻¹) * ‖δ‖) • u := by rw [inv_mul_cancel₀ (ne_of_gt hδ_pos)]
        _ = (‖δ‖⁻¹) • (‖δ‖ • u) := by rw [mul_smul]
        _ = (‖δ‖⁻¹) • δ := by rw [← hu]
    rw [hu_eq]
    have h := lemma43_part1_scale_free_domination hη hv hδ h_small a
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hδ_pos)
    have hsimp : ‖δ‖ * (|⟪a, v + δ⟫_ℝ| / ‖δ‖ * flipInd ⟪a, v⟫_ℝ ⟪a, v + δ⟫_ℝ) =
        |⟪a, v + δ⟫_ℝ| * flipInd ⟪a, v⟫_ℝ ⟪a, v + δ⟫_ℝ := by
      field_simp [ne_of_gt hδ_pos]
    linarith

/-! ### Stage A.3: Theorem 4 Deterministic Core, Global Lipschitz, and Noiseless Sharpness -/

/-- **Theorem 4 (Deterministic Core)**:
Given explicit deterministic regularity hypotheses:
- `(h_active)` every sample `a_i` lies in some strict active cone `C_j^*`,
- `(h_cone)` for every `j` and every unit vector `u`, the signed empirical cone L1 norm satisfies
  `T_j(u) ≥ γ / 2`,
- `(h_flip)` for every pair `j < k` and every unit vector `u`, the empirical flip surrogate satisfies
  `(1/m) ∑_i φ_η(⟪a_i, v̂_{jk}⟫, ⟪a_i, u⟫) ≤ C_flip * η`,
- `(h_budget)` `C_flip * η * (r - 1) ≤ γ / 4`,
- `(h_ball)` `frobNorm Δ ≤ (η / √2) * Δ_min`,
and arbitrary corruption values `ξ_i` supported on `{i | s_i = -1}` (with `s_i = 1` when `ξ_i = 0`),
we prove unconditionally:
  `f(β* + Δ) - f(β*) ≥ (γ / 4) * blockL1L2Norm Δ ≥ (γ / 4) * frobNorm Δ`. -/
theorem theorem4_deterministic_core
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (a : Fin m → E) (β_star Δ : Fin r → E)
    (s : Fin m → ℝ) (ξ : Fin m → ℝ)
    (γ η Δ_min C_flip : ℝ)
    (hγ : 0 ≤ γ) (hη : 0 < η) (hΔmin : 0 < Δ_min)
    (h_sep : ∀ j k : Fin r, j ≠ k → Δ_min ≤ ‖β_star j - β_star k‖)
    (h_signs : ∀ i : Fin m, (s i = 1 ∧ ξ i = 0) ∨ s i = -1)
    (h_active : ∀ i : Fin m, ∃ j₀ : Fin r, a i ∈ activeCone β_star j₀)
    (h_cone : ∀ (j : Fin r) (u : E), ‖u‖ = 1 → γ / 2 ≤ signedConeNorm a s β_star j u)
    (h_flip : ∀ (j k : Fin r), j < k → ∀ (u : E), ‖u‖ = 1 →
      (1 / (m : ℝ)) * ∑ i : Fin m,
        phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u⟫_ℝ ≤ C_flip * η)
    (h_budget : C_flip * η * ((r : ℝ) - 1) ≤ γ / 4)
    (h_ball : frobNorm Δ ≤ (η / Real.sqrt 2) * Δ_min) :
    let y := fun i => maxLinearPred hr (a i) β_star + ξ i
    let β := fun j => β_star j + Δ j
    (γ / 4) * frobNorm Δ ≤ l1EmpiricalLoss hr a y β - l1EmpiricalLoss hr a y β_star ∧
    (γ / 4) * blockL1L2Norm Δ ≤ l1EmpiricalLoss hr a y β - l1EmpiricalLoss hr a y β_star := by
  classical
  intro y β
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have inv_m_nonneg : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  -- Step 1: Pointwise lower bound for every sample `i` combining reverse triangle inequality and Lemma 3.1
  have h_pt : ∀ i : Fin m,
      (∑ j : Fin r, if a i ∈ activeCone β_star j then s i * |⟪a i, Δ j⟫_ℝ| else 0) -
      (∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
        |⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
          flipInd ⟪a i, β_star j - β_star k⟫_ℝ ⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ) ≤
      |y i - maxLinearPred hr (a i) β| - |y i - maxLinearPred hr (a i) β_star| := by
    intro i
    have h31 := lemma31_pointwise_flip_decomp hr β_star Δ (a i) (h_active i)
    have h31_lo := (abs_le.mp h31).1
    have h31_hi := (abs_le.mp h31).2
    rcases h_signs i with ⟨hs1, hξ0⟩ | hs_neg
    · -- Clean sample: `s i = 1`, `ξ i = 0`
      have hy_eq : y i = maxLinearPred hr (a i) β_star := by dsimp [y]; rw [hξ0, add_zero]
      rw [hy_eq, sub_self, abs_zero, sub_zero, abs_sub_comm]
      have h_lin_eq :
          (∑ j : Fin r, if a i ∈ activeCone β_star j then s i * |⟪a i, Δ j⟫_ℝ| else 0) =
          (∑ j : Fin r, if a i ∈ activeCone β_star j then |⟪a i, Δ j⟫_ℝ| else 0) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hs1, one_mul]
      rw [h_lin_eq]
      linarith
    · -- Corrupted sample: `s i = -1`, arbitrary `ξ i`
      have h_rev : -|maxLinearPred hr (a i) β - maxLinearPred hr (a i) β_star| ≤
          |y i - maxLinearPred hr (a i) β| - |y i - maxLinearPred hr (a i) β_star| := by
        have htri := abs_sub_abs_le_abs_sub (y i - maxLinearPred hr (a i) β_star)
                                            (y i - maxLinearPred hr (a i) β)
        have hsub : (y i - maxLinearPred hr (a i) β_star) - (y i - maxLinearPred hr (a i) β) =
            maxLinearPred hr (a i) β - maxLinearPred hr (a i) β_star := by ring
        rw [hsub] at htri
        linarith
      have h_lin_eq :
          (∑ j : Fin r, if a i ∈ activeCone β_star j then s i * |⟪a i, Δ j⟫_ℝ| else 0) =
          -(∑ j : Fin r, if a i ∈ activeCone β_star j then |⟪a i, Δ j⟫_ℝ| else 0) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        split_ifs <;> simp [hs_neg]
      rw [h_lin_eq]
      linarith
  -- Step 2: Average over `i ∈ Fin m` and swap finite sums
  have h_avg :
      (∑ j : Fin r, signedConeNorm a s β_star j (Δ j)) -
      (∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
        (1 / (m : ℝ)) * ∑ i : Fin m,
          |⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
            flipInd ⟪a i, β_star j - β_star k⟫_ℝ ⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ) ≤
      l1EmpiricalLoss hr a y β - l1EmpiricalLoss hr a y β_star := by
    unfold l1EmpiricalLoss signedConeNorm
    have h_rhs :
        (1 / (m : ℝ)) * ∑ i : Fin m, |y i - maxLinearPred hr (a i) β| -
        (1 / (m : ℝ)) * ∑ i : Fin m, |y i - maxLinearPred hr (a i) β_star| =
        (1 / (m : ℝ)) * ∑ i : Fin m,
          (|y i - maxLinearPred hr (a i) β| - |y i - maxLinearPred hr (a i) β_star|) := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
    rw [h_rhs]
    have hsum_pt := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h_pt i)
    have hmul_pt := mul_le_mul_of_nonneg_left hsum_pt inv_m_nonneg
    -- Rewrite the LHS of `hmul_pt` by swapping sums
    have h_swap1 :
        (1 / (m : ℝ)) * ∑ i : Fin m,
          (∑ j : Fin r, if a i ∈ activeCone β_star j then s i * |⟪a i, Δ j⟫_ℝ| else 0) =
        ∑ j : Fin r, (1 / (m : ℝ)) *
          ∑ i : Fin m, if a i ∈ activeCone β_star j then s i * |⟪a i, Δ j⟫_ℝ| else 0 := by
      rw [Finset.sum_comm, Finset.mul_sum]
    have h_swap2 :
        (1 / (m : ℝ)) * ∑ i : Fin m,
          (∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
            |⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
              flipInd ⟪a i, β_star j - β_star k⟫_ℝ ⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ) =
        ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
          (1 / (m : ℝ)) * ∑ i : Fin m,
            |⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
              flipInd ⟪a i, β_star j - β_star k⟫_ℝ ⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_comm, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, mul_sub, h_swap1, h_swap2] at hmul_pt
    exact hmul_pt
  -- Step 3: Bound Term 1 (signed cone norms) from below using `h_cone` and homogeneity
  have h_term1 : (γ / 2) * blockL1L2Norm Δ ≤ ∑ j : Fin r, signedConeNorm a s β_star j (Δ j) := by
    unfold blockL1L2Norm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun j _ => ?_)
    by_cases hΔj : Δ j = 0
    · rw [hΔj, norm_zero, mul_zero]
      unfold signedConeNorm
      simp
    · have hpos : 0 < ‖Δ j‖ := norm_pos_iff.mpr hΔj
      let u := (‖Δ j‖⁻¹) • Δ j
      have hu_norm : ‖u‖ = 1 := by
        dsimp [u]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
      have hhom : signedConeNorm a s β_star j (Δ j) = ‖Δ j‖ * signedConeNorm a s β_star j u := by
        unfold signedConeNorm
        have h_inner : ∀ i : Fin m, |⟪a i, Δ j⟫_ℝ| = ‖Δ j‖ * |⟪a i, u⟫_ℝ| := by
          intro i
          dsimp [u]
          rw [inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hpos), ← mul_assoc,
              mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
        have hsum : (∑ i : Fin m, if a i ∈ activeCone β_star j then s i * |⟪a i, Δ j⟫_ℝ| else 0) =
            ‖Δ j‖ * ∑ i : Fin m, if a i ∈ activeCone β_star j then s i * |⟪a i, u⟫_ℝ| else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          split_ifs
          · rw [h_inner i]; ring
          · ring
        rw [hsum]; ring
      rw [hhom]
      have hc := h_cone j u hu_norm
      nlinarith
  -- Step 4: Bound Term 2 (flip penalty) from above using Lemma 4.3(1) and `h_flip`
  have h_term2 :
      (∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
        (1 / (m : ℝ)) * ∑ i : Fin m,
          |⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
            flipInd ⟪a i, β_star j - β_star k⟫_ℝ ⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ) ≤
      (C_flip * η * ((r : ℝ) - 1)) * blockL1L2Norm Δ := by
    have h_pair : ∀ j : Fin r, ∀ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
        (1 / (m : ℝ)) * ∑ i : Fin m,
          |⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
            flipInd ⟪a i, β_star j - β_star k⟫_ℝ ⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ ≤
        (C_flip * η) * ‖Δ j - Δ k‖ := by
      intro j k hk
      have hjk_lt : j < k := (Finset.mem_filter.mp hk).2
      have hjk_ne : j ≠ k := ne_of_lt hjk_lt
      have hv_norm : Δ_min ≤ ‖β_star j - β_star k‖ := h_sep j k hjk_ne
      have hv_ne : β_star j - β_star k ≠ 0 := by
        intro h0
        have : ‖β_star j - β_star k‖ = 0 := by rw [h0, norm_zero]
        linarith
      have h_small : ‖Δ j - Δ k‖ ≤ η * ‖β_star j - β_star k‖ := by
        calc ‖Δ j - Δ k‖ ≤ Real.sqrt 2 * frobNorm Δ := norm_sub_le_sqrt_two_mul_frobNorm Δ hjk_ne
          _ ≤ Real.sqrt 2 * ((η / Real.sqrt 2) * Δ_min) :=
                mul_le_mul_of_nonneg_left h_ball (Real.sqrt_nonneg _)
          _ = η * Δ_min := by
                have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
                field_simp [hs2]
          _ ≤ η * ‖β_star j - β_star k‖ := mul_le_mul_of_nonneg_left hv_norm (le_of_lt hη)
      by_cases hδ0 : Δ j - Δ k = 0
      · rw [hδ0, norm_zero, mul_zero]
        have hzero : ∀ i : Fin m,
            |⟪a i, (β_star j - β_star k) + 0⟫_ℝ| *
              flipInd ⟪a i, β_star j - β_star k⟫_ℝ ⟪a i, (β_star j - β_star k) + 0⟫_ℝ = 0 := by
          intro i
          rw [add_zero]
          unfold flipInd
          have hnn : ¬ (⟪a i, β_star j - β_star k⟫_ℝ * ⟪a i, β_star j - β_star k⟫_ℝ < 0) :=
            not_lt.mpr (mul_self_nonneg _)
          simp [hnn]
        simp only [hzero, Finset.sum_const_zero, mul_zero, le_rfl]
      · have hδ_pos : 0 < ‖Δ j - Δ k‖ := norm_pos_iff.mpr hδ0
        let u := (‖Δ j - Δ k‖⁻¹) • (Δ j - Δ k)
        have hu_norm : ‖u‖ = 1 := by
          dsimp [u]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ_pos),
              inv_mul_cancel₀ (ne_of_gt hδ_pos)]
        have hu_eq : Δ j - Δ k = ‖Δ j - Δ k‖ • u := by
          dsimp [u]
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hδ_pos), one_smul]
        have h_each : ∀ i : Fin m,
            |⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
              flipInd ⟪a i, β_star j - β_star k⟫_ℝ ⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ ≤
            ‖Δ j - Δ k‖ * phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u⟫_ℝ :=
          fun i => lemma43_part1_scaled hη hv_ne h_small (a i) hu_eq
        calc (1 / (m : ℝ)) * ∑ i : Fin m,
              |⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ| *
                flipInd ⟪a i, β_star j - β_star k⟫_ℝ ⟪a i, (β_star j - β_star k) + (Δ j - Δ k)⟫_ℝ
            ≤ (1 / (m : ℝ)) * ∑ i : Fin m,
              (‖Δ j - Δ k‖ * phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u⟫_ℝ) :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => h_each i)) inv_m_nonneg
          _ = ‖Δ j - Δ k‖ * ((1 / (m : ℝ)) * ∑ i : Fin m,
              phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u⟫_ℝ) := by
              rw [← Finset.mul_sum]; ring
          _ ≤ ‖Δ j - Δ k‖ * (C_flip * η) :=
              mul_le_mul_of_nonneg_left (h_flip j k hjk_lt u hu_norm) (le_of_lt hδ_pos)
          _ = (C_flip * η) * ‖Δ j - Δ k‖ := by ring
    -- Check `0 ≤ C_flip * η` (follows from `0 ≤ phiEta` if `m > 0`, or directly from `h_flip`!)
    have h_Cη_nonneg : ∀ j k : Fin r, j < k → 0 ≤ C_flip * η := by
      intro j k hjk
      have hv_ne : β_star j - β_star k ≠ 0 := by
        intro h0
        have : ‖β_star j - β_star k‖ = 0 := by rw [h0, norm_zero]
        linarith [h_sep j k (ne_of_lt hjk)]
      let u := (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)
      have hu_norm : ‖u‖ = 1 := by
        dsimp [u]
        have hp : 0 < ‖β_star j - β_star k‖ := norm_pos_iff.mpr hv_ne
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ (ne_of_gt hp)]
      have h0 : 0 ≤ (1 / (m : ℝ)) * ∑ i : Fin m,
          phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u⟫_ℝ :=
        mul_nonneg inv_m_nonneg (Finset.sum_nonneg (fun i _ => le_max_left _ _))
      exact le_trans h0 (h_flip j k hjk u hu_norm)
    by_cases hr1 : r = 1
    · subst hr1
      have h_empty : ∀ j : Fin 1, Finset.univ.filter (fun k : Fin 1 => j < k) = ∅ := by
        intro j
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt]
        exact le_of_eq (Subsingleton.elim k j)
      simp [h_empty]
      ring_nf
      exact le_rfl
    · have hr2 : 2 ≤ r := by omega
      have hCη0 : 0 ≤ C_flip * η :=
        h_Cη_nonneg ⟨0, hr⟩ ⟨1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
      calc _ ≤ ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k),
            (C_flip * η) * ‖Δ j - Δ k‖ :=
            Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k hk => h_pair j k hk))
        _ = (C_flip * η) * ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k), ‖Δ j - Δ k‖ := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => (Finset.mul_sum _ _ _).symm)
        _ ≤ (C_flip * η) * (((r : ℝ) - 1) * blockL1L2Norm Δ) :=
            mul_le_mul_of_nonneg_left (sum_ordered_pairs_norm_sub_le Δ) hCη0
        _ = (C_flip * η * ((r : ℝ) - 1)) * blockL1L2Norm Δ := by ring
  -- Step 5: Combine Term 1, Term 2, and `h_budget`
  have h_l1l2 : (γ / 4) * blockL1L2Norm Δ ≤ l1EmpiricalLoss hr a y β - l1EmpiricalLoss hr a y β_star := by
    have h_sub : (γ / 4) * blockL1L2Norm Δ ≤
        (γ / 2) * blockL1L2Norm Δ - (C_flip * η * ((r : ℝ) - 1)) * blockL1L2Norm Δ := by
      nlinarith [blockL1L2Norm_nonneg Δ]
    linarith
  have h_frob : (γ / 4) * frobNorm Δ ≤ l1EmpiricalLoss hr a y β - l1EmpiricalLoss hr a y β_star := by
    have h1 := mul_le_mul_of_nonneg_left (frobNorm_le_blockL1L2Norm Δ) (by linarith : 0 ≤ γ / 4)
    linarith
  exact ⟨h_frob, h_l1l2⟩

/-- **Theorem 4, Part 2 (Global Lipschitz Constant from Operator Norm)**:
If `∑_i ⟪a_i, u⟫^2 ≤ (L^2 * m) * ‖u‖^2` for all `u : E` (i.e., `‖A‖_op / √m ≤ L`),
then `|f(β) - f(β')| ≤ L * frobNorm (β - β')` for all `β, β' : Fin r → E`. -/
theorem theorem4_part2_global_lipschitz
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (a : Fin m → E) (y : Fin m → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h_op : ∀ u : E, ∑ i : Fin m, ⟪a i, u⟫_ℝ ^ 2 ≤ (L ^ 2 * (m : ℝ)) * ‖u‖ ^ 2)
    (β β' : Fin r → E) :
    |l1EmpiricalLoss hr a y β - l1EmpiricalLoss hr a y β'| ≤
      L * frobNorm (fun j => β j - β' j) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have h_pred_diff : ∀ i : Fin m,
      |maxLinearPred hr (a i) β - maxLinearPred hr (a i) β'| ≤
      Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2) := by
    intro i
    have h_one_side : ∀ (b₁ b₂ : Fin r → E),
        maxLinearPred hr (a i) b₁ - maxLinearPred hr (a i) b₂ ≤
        Real.sqrt (∑ j : Fin r, ⟪a i, b₁ j - b₂ j⟫_ℝ ^ 2) := by
      intro b₁ b₂
      unfold maxLinearPred
      have hne : (Finset.univ : Finset (Fin r)).Nonempty :=
        Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩
      obtain ⟨j₁, _, hj₁⟩ := Finset.exists_mem_eq_sup' hne (fun j => ⟪a i, b₁ j⟫_ℝ)
      rw [hj₁]
      have hle2 : ⟪a i, b₂ j₁⟫_ℝ ≤ Finset.univ.sup' hne (fun j => ⟪a i, b₂ j⟫_ℝ) :=
        Finset.le_sup' (fun j => ⟪a i, b₂ j⟫_ℝ) (Finset.mem_univ j₁)
      have hdiff : ⟪a i, b₁ j₁⟫_ℝ - ⟪a i, b₂ j₁⟫_ℝ = ⟪a i, b₁ j₁ - b₂ j₁⟫_ℝ :=
        (inner_sub_right (a i) (b₁ j₁) (b₂ j₁)).symm
      have hsq_le : ⟪a i, b₁ j₁ - b₂ j₁⟫_ℝ ^ 2 ≤ ∑ j : Fin r, ⟪a i, b₁ j - b₂ j⟫_ℝ ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg ⟪a i, b₁ j - b₂ j⟫_ℝ) (Finset.mem_univ j₁)
      have habs : ⟪a i, b₁ j₁ - b₂ j₁⟫_ℝ ≤ Real.sqrt (∑ j : Fin r, ⟪a i, b₁ j - b₂ j⟫_ℝ ^ 2) := by
        calc ⟪a i, b₁ j₁ - b₂ j₁⟫_ℝ ≤ |⟪a i, b₁ j₁ - b₂ j₁⟫_ℝ| := le_abs_self _
          _ = Real.sqrt (⟪a i, b₁ j₁ - b₂ j₁⟫_ℝ ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt (∑ j : Fin r, ⟪a i, b₁ j - b₂ j⟫_ℝ ^ 2) := Real.sqrt_le_sqrt hsq_le
      linarith
    rw [abs_le]
    refine ⟨?_, h_one_side β β'⟩
    have hrev := h_one_side β' β
    have hsq_eq : ∑ j : Fin r, ⟪a i, β' j - β j⟫_ℝ ^ 2 = ∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have : β' j - β j = -(β j - β' j) := by abel
      rw [this, inner_neg_right, neg_sq]
    rw [hsq_eq] at hrev
    linarith
  -- Step 1: Bound `|f(β) - f(β')|` by `(1/m) ∑_i √(∑_j ⟪a_i, β_j - β'_j⟫^2)`
  have h_step1 :
      |l1EmpiricalLoss hr a y β - l1EmpiricalLoss hr a y β'| ≤
      (1 / (m : ℝ)) * ∑ i : Fin m, Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2) := by
    unfold l1EmpiricalLoss
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (m : ℝ)),
        ← Finset.sum_sub_distrib]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |∑ i : Fin m, (|y i - maxLinearPred hr (a i) β| - |y i - maxLinearPred hr (a i) β'|)|
        ≤ ∑ i : Fin m, abs (|y i - maxLinearPred hr (a i) β| - |y i - maxLinearPred hr (a i) β'|) :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m, |maxLinearPred hr (a i) β - maxLinearPred hr (a i) β'| := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have h1 := abs_abs_sub_abs_le_abs_sub (y i - maxLinearPred hr (a i) β)
                                                (y i - maxLinearPred hr (a i) β')
          have h2 : (y i - maxLinearPred hr (a i) β) - (y i - maxLinearPred hr (a i) β') =
              -(maxLinearPred hr (a i) β - maxLinearPred hr (a i) β') := by ring
          rw [h2, abs_neg] at h1
          exact h1
      _ ≤ ∑ i : Fin m, Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2) :=
          Finset.sum_le_sum (fun i _ => h_pred_diff i)
  -- Step 2: Cauchy-Schwarz over `i ∈ Fin m` and `h_op`
  have h_cs :
      (∑ i : Fin m, Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2)) ^ 2 ≤
      (m : ℝ) * ∑ i : Fin m, ∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2 := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun _ => (1 : ℝ)) (fun i => Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one] at h1
    have hsq : ∑ i : Fin m, (Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2)) ^ 2 =
        ∑ i : Fin m, ∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2 := by
      refine Finset.sum_congr rfl (fun i _ => Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _)))
    rw [hsq] at h1
    exact h1
  have h_op_sum :
      ∑ i : Fin m, ∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2 ≤
      (L ^ 2 * (m : ℝ)) * ∑ j : Fin r, ‖β j - β' j‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => h_op (β j - β' j))
  have h_sq_bound :
      ((1 / (m : ℝ)) * ∑ i : Fin m, Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2)) ^ 2 ≤
      (L * frobNorm (fun j => β j - β' j)) ^ 2 := by
    rw [mul_pow, mul_pow]
    unfold frobNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
    have hcomb : (∑ i : Fin m, Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2)) ^ 2 ≤
        (m : ℝ) ^ 2 * (L ^ 2 * ∑ j : Fin r, ‖β j - β' j‖ ^ 2) := by
      calc _ ≤ (m : ℝ) * ((L ^ 2 * (m : ℝ)) * ∑ j : Fin r, ‖β j - β' j‖ ^ 2) :=
              le_trans h_cs (mul_le_mul_of_nonneg_left h_op_sum (le_of_lt hm_pos))
        _ = (m : ℝ) ^ 2 * (L ^ 2 * ∑ j : Fin r, ‖β j - β' j‖ ^ 2) := by ring
    have hmul := mul_le_mul_of_nonneg_left hcomb (by positivity : (0 : ℝ) ≤ (1 / (m : ℝ)) ^ 2)
    have hsimp : (1 / (m : ℝ)) ^ 2 * ((m : ℝ) ^ 2 * (L ^ 2 * ∑ j : Fin r, ‖β j - β' j‖ ^ 2)) =
        L ^ 2 * ∑ j : Fin r, ‖β j - β' j‖ ^ 2 := by
      field_simp [hm_ne]
    linarith
  have h_nonneg_lhs : 0 ≤ (1 / (m : ℝ)) * ∑ i : Fin m, Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _))
  have h_nonneg_rhs : 0 ≤ L * frobNorm (fun j => β j - β' j) :=
    mul_nonneg hL (frobNorm_nonneg _)
  have h_step2 :
      (1 / (m : ℝ)) * ∑ i : Fin m, Real.sqrt (∑ j : Fin r, ⟪a i, β j - β' j⟫_ℝ ^ 2) ≤
      L * frobNorm (fun j => β j - β' j) := by
    nlinarith
  exact le_trans h_step1 h_step2

/-- **Theorem 4, Part 3 (Noiseless Global-Minimizer Isolation & Half-Radius Distance Identity)**:
If `f(β) ≥ μ * frobNorm (β - β*)` on `B(β*, ρ)` with `μ > 0` and `f(β*) = 0`, then:
1. Every `z ∈ B(β*, ρ)` with `f(z) = 0` equals `β*` (so `X* ∩ B(β*, ρ) = {β*}`);
2. For every `β ∈ B(β*, ρ/2)` and every global minimizer `z` (`f z = 0`),
   `frobNorm (β - β*) ≤ frobNorm (β - z)` (hence `dist(β, X*) = frobNorm (β - β*)`),
   so `f(β) ≥ μ * frobNorm (β - β*)`. -/
theorem theorem4_part3_half_radius_distance
    {r : ℕ} (f : (Fin r → E) → ℝ) (β_star : Fin r → E) {μ ρ : ℝ}
    (hμ : 0 < μ) (hρ : 0 < ρ)
    (h_sharp : ∀ Δ : Fin r → E, frobNorm Δ ≤ ρ → μ * frobNorm Δ ≤ f (fun j => β_star j + Δ j))
    {β z : Fin r → E}
    (hβ : frobNorm (fun j => β j - β_star j) ≤ ρ / 2)
    (hz : f z = 0) :
    frobNorm (fun j => β j - β_star j) ≤ frobNorm (fun j => β j - z j) := by
  by_cases hz_eq : frobNorm (fun j => z j - β_star j) = 0
  · -- If `frobNorm (z - β*) = 0`, then `z = β*`
    have hz_pt : ∀ j : Fin r, z j = β_star j := by
      intro j
      unfold frobNorm at hz_eq
      have hsum0 : ∑ k : Fin r, ‖z k - β_star k‖ ^ 2 = 0 := by
        have hsq := congrArg (fun t => t ^ 2) hz_eq
        simp only [zero_pow (by norm_num : 2 ≠ 0)] at hsq
        rwa [Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))] at hsq
      have hterm0 : ‖z j - β_star j‖ ^ 2 = 0 := by
        have hle := Finset.single_le_sum (fun k _ => sq_nonneg ‖z k - β_star k‖) (Finset.mem_univ j)
        linarith [sq_nonneg ‖z j - β_star j‖]
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hterm0))
    have hfun : z = β_star := funext hz_pt
    rw [hfun]
  · -- Otherwise `frobNorm (z - β*) > 0`, so `z` must lie strictly outside `B(β*, ρ)`
    have hz_pos : 0 < frobNorm (fun j => z j - β_star j) :=
      lt_of_le_of_ne (frobNorm_nonneg _) (Ne.symm hz_eq)
    have hz_out : ρ < frobNorm (fun j => z j - β_star j) := by
      by_contra hle
      push_neg at hle
      have h_sh := h_sharp (fun j => z j - β_star j) hle
      have heq : (fun j => β_star j + (z j - β_star j)) = z := by
        funext j; abel
      rw [heq, hz] at h_sh
      have hpos_prod : 0 < μ * frobNorm (fun j => z j - β_star j) := mul_pos hμ hz_pos
      linarith
    -- Reverse triangle inequality: `‖z - β*‖ ≤ ‖z - β‖ + ‖β - β*‖`
    have htri := frobNorm_triangle (fun j => z j - β j) (fun j => β j - β_star j)
    have hadd : (fun j => (z j - β j) + (β j - β_star j)) = (fun j => z j - β_star j) := by
      funext j; abel
    rw [hadd] at htri
    have hsymm : frobNorm (fun j => z j - β j) = frobNorm (fun j => β j - z j) := by
      have : (fun j => z j - β j) = (fun j => -(β j - z j)) := by funext j; abel
      rw [this, frobNorm_neg]
    rw [hsymm] at htri
    linarith

/-! ### Stage A.4: Machine-Checked Counterexample & Corrected Witness for Theorem 1(b) -/

/-- **Counterexample to Phase I Theorem 1(b) (Formally Verified)**:
For `d = 1, r = 2, m = 2`, `a = ![1, 1]`, `y = ![1, -1]`, at any `β = ![b₁, b₂]` with `|b₁| < 1` and `|b₂| < 1`,
the L1 max-linear objective is identically constant `f(β) = 1` (hence locally convex and 0-weakly convex),
even though at `β = (0, 0)` sample 0 has `ŷ_0 = 0 < 1 = y_0`, `a_0 = 1 ≠ 0`, and both blocks tied! -/
theorem theorem1b_counterexample_constant
    (b₁ b₂ : ℝ) (hb₁ : |b₁| < 1) (hb₂ : |b₂| < 1) :
    let a : Fin 2 → ℝ := ![1, 1]
    let y : Fin 2 → ℝ := ![1, -1]
    let β : Fin 2 → ℝ := ![b₁, b₂]
    l1EmpiricalLoss (by norm_num : 0 < 2) a y β = 1 := by
  intro a y β
  unfold l1EmpiricalLoss maxLinearPred
  have hsup : ∀ x : ℝ,
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, by norm_num⟩⟩)
        (fun j : Fin 2 => ⟪x, β j⟫_ℝ) = max (x * b₁) (x * b₂) := by
    intro x
    apply le_antisymm
    · refine Finset.sup'_le _ _ (fun j _ => ?_)
      fin_cases j <;> simp [β, mul_comm]
    · refine max_le ?_ ?_
      · have h0 := Finset.le_sup' (fun j : Fin 2 => ⟪x, β j⟫_ℝ) (Finset.mem_univ (0 : Fin 2))
        simpa [β, mul_comm] using h0
      · have h1 := Finset.le_sup' (fun j : Fin 2 => ⟪x, β j⟫_ℝ) (Finset.mem_univ (1 : Fin 2))
        simpa [β, mul_comm] using h1
  rw [Fin.sum_univ_two]
  simp only [a, y, Matrix.cons_val_zero, Matrix.cons_val_one, hsup, one_mul]
  have hM_lt : max b₁ b₂ < 1 := max_lt (lt_of_abs_lt hb₁) (lt_of_abs_lt hb₂)
  have hM_gt : -1 < max b₁ b₂ := lt_of_lt_of_le (neg_lt_of_abs_lt hb₁) (le_max_left b₁ b₂)
  rw [abs_of_pos (by linarith : 0 < 1 - max b₁ b₂),
      abs_of_neg (by linarith : -1 - max b₁ b₂ < 0)]
  ring

/-- **Witness that the L1 max-linear function class is NOT weakly convex in general**:
For `d = 1, r = 2, m = 1`, `a = ![1]`, `y = ![1]`, along `β(t) = ![t, -t]`, `f(β(t)) = 1 - |t|` for `|t| ≤ 1`.
Hence for EVERY `ρ ≥ 0` and EVERY `ε > 0`, there exists `t ∈ (0, ε)` violating midpoint convexity of
`β ↦ f(β) + (ρ/2) * (frobNorm β)^2` around `(0, 0)`. -/
theorem theorem1b_class_not_weakly_convex (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hε : 0 < ε) :
    let a : Fin 1 → ℝ := ![1]
    let y : Fin 1 → ℝ := ![1]
    let g := fun (β : Fin 2 → ℝ) =>
      l1EmpiricalLoss (by norm_num : 0 < 2) a y β + (ρ / 2) * (frobNorm β) ^ 2
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ g ![t, -t] + g ![-t, t] < 2 * g ![0, 0] := by
  intro a y g
  let t : ℝ := min (min (ε / 2) (1 / 2)) (1 / (2 * (ρ + 1)))
  have ht_pos : 0 < t := by
    dsimp [t]
    refine lt_min (lt_min (by linarith) (by norm_num)) (by positivity)
  have ht_lt_ε : t < ε := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have ht_le_half : t ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have ht_le_rho : t ≤ 1 / (2 * (ρ + 1)) := min_le_right _ _
  refine ⟨t, ht_pos, ht_lt_ε, ?_⟩
  have hloss : ∀ u v : ℝ,
      l1EmpiricalLoss (by norm_num : 0 < 2) a y ![u, v] = |1 - max u v| := by
    intro u v
    unfold l1EmpiricalLoss maxLinearPred
    rw [Fin.sum_univ_one]
    simp only [a, y, Matrix.cons_val_zero, Nat.cast_one, div_one, one_mul]
    have hsup : Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, by norm_num⟩⟩)
        (fun j : Fin 2 => ⟪(1 : ℝ), (![u, v] : Fin 2 → ℝ) j⟫_ℝ) = max u v := by
      apply le_antisymm
      · refine Finset.sup'_le _ _ (fun j _ => ?_)
        fin_cases j <;> simp
      · refine max_le ?_ ?_
        · have h0 := Finset.le_sup' (fun j : Fin 2 => ⟪(1 : ℝ), (![u, v] : Fin 2 → ℝ) j⟫_ℝ) (Finset.mem_univ (0 : Fin 2))
          simpa using h0
        · have h1 := Finset.le_sup' (fun j : Fin 2 => ⟪(1 : ℝ), (![u, v] : Fin 2 → ℝ) j⟫_ℝ) (Finset.mem_univ (1 : Fin 2))
          simpa using h1
    rw [hsup]
  have hfrob : ∀ u v : ℝ, (frobNorm (![u, v] : Fin 2 → ℝ)) ^ 2 = u ^ 2 + v ^ 2 := by
    intro u v
    unfold frobNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _)), Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  dsimp only [g]
  rw [hloss t (-t), hloss (-t) t, hloss 0 0, hfrob t (-t), hfrob (-t) t, hfrob 0 0]
  have hmax1 : max t (-t) = t := max_eq_left (by linarith)
  have hmax2 : max (-t) t = t := max_eq_right (by linarith)
  rw [hmax1, hmax2, max_self, sub_zero, abs_of_pos (by norm_num : (0 : ℝ) < 1),
      abs_of_pos (by linarith : 0 < 1 - t)]
  have hρt : ρ * t < 1 / 2 := by
    have h1 : t * (2 * (ρ + 1)) ≤ 1 := by
      have hp : 0 < 2 * (ρ + 1) := by linarith
      exact (le_div_iff₀ hp).mp ht_le_rho
    nlinarith
  nlinarith

end Research107
