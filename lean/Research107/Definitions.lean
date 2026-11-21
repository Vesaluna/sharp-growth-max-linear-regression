import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

open scoped BigOperators InnerProductSpace

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Max-linear prediction `max_{j ∈ Fin r} ⟪a, β j⟫_ℝ`. -/
noncomputable def maxLinearPred {r : ℕ} (hr : 0 < r) (a : E) (β : Fin r → E) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩) (fun j => ⟪a, β j⟫_ℝ)

/-- Empirical L1 (absolute) loss `f(β) = (1/m) ∑_i |y_i - max_j ⟪a_i, β_j⟫|`. -/
noncomputable def l1EmpiricalLoss {m r : ℕ} (hr : 0 < r)
    (a : Fin m → E) (y : Fin m → ℝ) (β : Fin r → E) : ℝ :=
  (1 / (m : ℝ)) * ∑ i : Fin m, |y i - maxLinearPred hr (a i) β|

/-- Open strict active cone `C_j^*` for component `j` at parameter `β_star`. -/
def activeCone {r : ℕ} (β_star : Fin r → E) (j : Fin r) : Set E :=
  {a : E | ∀ k : Fin r, k ≠ j → ⟪a, β_star k⟫_ℝ < ⟪a, β_star j⟫_ℝ}

/-- Euclidean (Frobenius) norm on parameter tuples `Fin r → E`. -/
noncomputable def frobNorm {r : ℕ} (Δ : Fin r → E) : ℝ :=
  Real.sqrt (∑ j : Fin r, ‖Δ j‖ ^ 2)

/-- Block `ℓ₁–ℓ₂` norm `∑_j ‖Δ_j‖`. -/
noncomputable def blockL1L2Norm {r : ℕ} (Δ : Fin r → E) : ℝ :=
  ∑ j : Fin r, ‖Δ j‖

/-- Scale-free continuous piecewise-linear flip surrogate `φ_η(z₁, z₂) = max(0, 2|z₂| - |z₁|/η)`. -/
noncomputable def phiEta (η z₁ z₂ : ℝ) : ℝ :=
  max 0 (2 * |z₂| - |z₁| / η)

/-- Indicator `1{x * y < 0}` as a real number in `{0, 1}`. -/
noncomputable def flipInd (x y : ℝ) : ℝ :=
  if x * y < 0 then 1 else 0

/-- Signed empirical cone L1 norm `T_j(u) = (1/m) ∑_i s_i 1_{C_j^*}(a_i) |⟪a_i, u⟫|`. -/
noncomputable def signedConeNorm {m r : ℕ} (a : Fin m → E) (s : Fin m → ℝ)
    (β_star : Fin r → E) (j : Fin r) (u : E) : ℝ :=
  open scoped Classical in
  (1 / (m : ℝ)) * ∑ i : Fin m, if a i ∈ activeCone β_star j then s i * |⟪a i, u⟫_ℝ| else 0

lemma frobNorm_nonneg {r : ℕ} (Δ : Fin r → E) : 0 ≤ frobNorm Δ :=
  Real.sqrt_nonneg _

lemma blockL1L2Norm_nonneg {r : ℕ} (Δ : Fin r → E) : 0 ≤ blockL1L2Norm Δ :=
  Finset.sum_nonneg (fun j _ => norm_nonneg (Δ j))

lemma sum_sq_le_sq_sum_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∑ i ∈ s, f i :=
      Finset.sum_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hih : ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    nlinarith

lemma frobNorm_le_blockL1L2Norm {r : ℕ} (Δ : Fin r → E) :
    frobNorm Δ ≤ blockL1L2Norm Δ := by
  unfold frobNorm blockL1L2Norm
  rw [Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg (fun j _ => norm_nonneg _), ?_⟩
  exact sum_sq_le_sq_sum_nonneg Finset.univ (fun j => ‖Δ j‖) (fun j _ => norm_nonneg _)

lemma norm_sub_le_sqrt_two_mul_frobNorm {r : ℕ} (Δ : Fin r → E) {j k : Fin r} (hjk : j ≠ k) :
    ‖Δ j - Δ k‖ ≤ Real.sqrt 2 * frobNorm Δ := by
  have htri : ‖Δ j - Δ k‖ ≤ ‖Δ j‖ + ‖Δ k‖ := norm_sub_le (Δ j) (Δ k)
  have hsum_two : ‖Δ j‖ ^ 2 + ‖Δ k‖ ^ 2 ≤ ∑ l : Fin r, ‖Δ l‖ ^ 2 := by
    have hsub : ({j, k} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
    calc ‖Δ j‖ ^ 2 + ‖Δ k‖ ^ 2
        = ∑ l ∈ ({j, k} : Finset (Fin r)), ‖Δ l‖ ^ 2 := by
          rw [Finset.sum_pair hjk]
      _ ≤ ∑ l : Fin r, ‖Δ l‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => sq_nonneg _)
  have hsq : (‖Δ j‖ + ‖Δ k‖) ^ 2 ≤ (Real.sqrt 2 * frobNorm Δ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    unfold frobNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun l _ => sq_nonneg _))]
    nlinarith [sq_nonneg (‖Δ j‖ - ‖Δ k‖)]
  have hrhs : 0 ≤ Real.sqrt 2 * frobNorm Δ := mul_nonneg (Real.sqrt_nonneg _) (frobNorm_nonneg _)
  have h1 : ‖Δ j‖ + ‖Δ k‖ ≤ Real.sqrt 2 * frobNorm Δ := by
    nlinarith [norm_nonneg (Δ j), norm_nonneg (Δ k)]
  linarith

lemma frobNorm_triangle {r : ℕ} (x y : Fin r → E) :
    frobNorm (fun j => x j + y j) ≤ frobNorm x + frobNorm y := by
  unfold frobNorm
  have hsum_nonneg : ∀ f : Fin r → E, 0 ≤ ∑ j : Fin r, ‖f j‖ ^ 2 :=
    fun f => Finset.sum_nonneg (fun j _ => sq_nonneg _)
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have hcs : ∑ j : Fin r, ‖x j‖ * ‖y j‖ ≤
      Real.sqrt (∑ j : Fin r, ‖x j‖ ^ 2) * Real.sqrt (∑ j : Fin r, ‖y j‖ ^ 2) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖x j‖) (fun j => ‖y j‖)
    have hnonneg : 0 ≤ ∑ j : Fin r, ‖x j‖ * ‖y j‖ :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [← Real.sqrt_mul (hsum_nonneg x)]
    rw [Real.le_sqrt hnonneg (mul_nonneg (hsum_nonneg x) (hsum_nonneg y))]
    exact h1
  have hpt : ∑ j : Fin r, ‖x j + y j‖ ^ 2 ≤
      ∑ j : Fin r, ‖x j‖ ^ 2 + 2 * (∑ j : Fin r, ‖x j‖ * ‖y j‖) + ∑ j : Fin r, ‖y j‖ ^ 2 := by
    have h2 : ∑ j : Fin r, (‖x j‖ ^ 2 + 2 * (‖x j‖ * ‖y j‖) + ‖y j‖ ^ 2) =
        ∑ j : Fin r, ‖x j‖ ^ 2 + 2 * (∑ j : Fin r, ‖x j‖ * ‖y j‖) + ∑ j : Fin r, ‖y j‖ ^ 2 := by
      simp [Finset.sum_add_distrib, Finset.mul_sum]
    rw [← h2]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have htri : ‖x j + y j‖ ≤ ‖x j‖ + ‖y j‖ := norm_add_le (x j) (y j)
    nlinarith [norm_nonneg (x j + y j), norm_nonneg (x j), norm_nonneg (y j)]
  calc ∑ j : Fin r, ‖x j + y j‖ ^ 2
      ≤ ∑ j : Fin r, ‖x j‖ ^ 2 + 2 * (∑ j : Fin r, ‖x j‖ * ‖y j‖) + ∑ j : Fin r, ‖y j‖ ^ 2 := hpt
    _ ≤ ∑ j : Fin r, ‖x j‖ ^ 2 +
        2 * (Real.sqrt (∑ j : Fin r, ‖x j‖ ^ 2) * Real.sqrt (∑ j : Fin r, ‖y j‖ ^ 2)) +
        ∑ j : Fin r, ‖y j‖ ^ 2 := by linarith
    _ = (Real.sqrt (∑ j : Fin r, ‖x j‖ ^ 2) + Real.sqrt (∑ j : Fin r, ‖y j‖ ^ 2)) ^ 2 := by
        ring_nf
        rw [Real.sq_sqrt (hsum_nonneg x), Real.sq_sqrt (hsum_nonneg y)]
        ring

lemma frobNorm_neg {r : ℕ} (x : Fin r → E) :
    frobNorm (fun j => -x j) = frobNorm x := by
  unfold frobNorm
  simp [norm_neg]

lemma sum_ordered_pairs_norm_sub_le {r : ℕ} (Δ : Fin r → E) :
    ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k), ‖Δ j - Δ k‖
      ≤ ((r : ℝ) - 1) * blockL1L2Norm Δ := by
  have h1 :
      ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k), ‖Δ j - Δ k‖ ≤
      ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k), (‖Δ j‖ + ‖Δ k‖) := by
    refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => norm_sub_le (Δ j) (Δ k)))
  have h2 :
      ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k), (‖Δ j‖ + ‖Δ k‖) =
      ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => k ≠ j), ‖Δ j‖ := by
    -- Split the sum of `‖Δ j‖ + ‖Δ k‖` over `j < k` into `j < k` part and swapped `k < j` part
    simp_rw [Finset.sum_add_distrib]
    have hswap :
        ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => j < k), ‖Δ k‖ =
        ∑ k : Fin r, ∑ j ∈ Finset.univ.filter (fun j : Fin r => j < k), ‖Δ k‖ := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    rw [hswap]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hdisj : Disjoint (Finset.univ.filter (fun k : Fin r => j < k))
                          (Finset.univ.filter (fun k : Fin r => k < j)) := by
      rw [Finset.disjoint_filter]
      intro k _ h1 h2
      exact lt_asymm h1 h2
    have hunion :
        Finset.univ.filter (fun k : Fin r => j < k) ∪ Finset.univ.filter (fun k : Fin r => k < j) =
        Finset.univ.filter (fun k : Fin r => k ≠ j) := by
      ext k
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.elim ne_of_gt ne_of_lt, fun h => (lt_or_gt_of_ne h).symm⟩
    rw [← Finset.sum_union hdisj, hunion]
  have h3 :
      ∑ j : Fin r, ∑ k ∈ Finset.univ.filter (fun k : Fin r => k ≠ j), ‖Δ j‖ =
      ((r : ℝ) - 1) * blockL1L2Norm Δ := by
    unfold blockL1L2Norm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun k : Fin r => k ≠ j)).card = r - 1 := by
      have : Finset.univ.filter (fun k : Fin r => k ≠ j) = Finset.univ.erase j := by
        ext k; simp
      rw [this, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
    rw [hcard]
    have hr1 : 1 ≤ r := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt)
    rw [Nat.cast_sub hr1, Nat.cast_one]
  linarith

end Research107
