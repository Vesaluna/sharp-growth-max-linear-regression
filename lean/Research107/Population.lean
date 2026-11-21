import Research107.Definitions
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped BigOperators InnerProductSpace

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Stage B.1: Theorem 2 Antipodal Symmetry Identity & Sharp Pointwise Bounds -/

/-- The scalar ramp function `ψ_u(s) = |s + u| - |s|`. -/
def psiU (u s : ℝ) : ℝ := |s + u| - |s|

lemma psiU_eq_clamp {u : ℝ} (hu : 0 < u) (s : ℝ) :
    psiU u s = max (-u) (min u (2 * s + u)) := by
  unfold psiU
  by_cases h0 : 0 ≤ s
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg h0]
    have hmin : min u (2 * s + u) = u := min_eq_left (by linarith)
    rw [hmin, max_eq_right (by linarith)]
    ring
  · push_neg at h0
    by_cases h1 : 0 ≤ s + u
    · rw [abs_of_nonneg h1, abs_of_neg h0]
      have hmin : min u (2 * s + u) = 2 * s + u := min_eq_right (by linarith)
      rw [hmin, max_eq_right (by linarith)]
      ring
    · push_neg at h1
      rw [abs_of_neg h1, abs_of_neg h0]
      have hmin : min u (2 * s + u) = 2 * s + u := min_eq_right (by linarith)
      rw [hmin, max_eq_left (by linarith)]
      ring

/-- Exact monotonicity, 2-Lipschitz, and oscillation bounds on `ψ_u`:
for `u > 0`, `X > 0`, and any `D₁ : ℝ`,
`-2 * min X u ≤ ψ_u(D₁) - ψ_u(D₁ + X) ≤ 0`. -/
lemma psiU_diff_bounds {u X : ℝ} (hu : 0 < u) (hX : 0 < X) (D₁ : ℝ) :
    -2 * min X u ≤ psiU u D₁ - psiU u (D₁ + X) ∧ psiU u D₁ - psiU u (D₁ + X) ≤ 0 := by
  rw [psiU_eq_clamp hu D₁, psiU_eq_clamp hu (D₁ + X)]
  have hmono : max (-u) (min u (2 * D₁ + u)) ≤ max (-u) (min u (2 * (D₁ + X) + u)) :=
    max_le_max_left (-u) (min_le_min_left u (by linarith))
  have hbound_u : max (-u) (min u (2 * (D₁ + X) + u)) - max (-u) (min u (2 * D₁ + u)) ≤ 2 * u := by
    have hhi : max (-u) (min u (2 * (D₁ + X) + u)) ≤ u :=
      max_le (by linarith) (min_le_left _ _)
    have hlo : -u ≤ max (-u) (min u (2 * D₁ + u)) := le_max_left _ _
    linarith
  have hbound_X : max (-u) (min u (2 * (D₁ + X) + u)) - max (-u) (min u (2 * D₁ + u)) ≤ 2 * X := by
    have hmin_le : min u (2 * (D₁ + X) + u) ≤ min u (2 * D₁ + u) + 2 * X := by
      rcases le_total u (2 * D₁ + u) with h | h
      · rw [min_eq_left h]; linarith [min_le_left u (2 * (D₁ + X) + u)]
      · rw [min_eq_right h]; linarith [min_le_right u (2 * (D₁ + X) + u)]
    have hmax_le : max (-u) (min u (2 * (D₁ + X) + u)) ≤ max (-u) (min u (2 * D₁ + u)) + 2 * X := by
      apply max_le
      · linarith [le_max_left (-u) (min u (2 * D₁ + u))]
      · linarith [le_max_right (-u) (min u (2 * D₁ + u))]
    linarith
  constructor
  · rcases le_total X u with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  · linarith

/-- Residual error `R(a) = |max(⟪a, β₁⟫, ⟪a, β₂⟫) - max(⟪a, β₁*⟫, ⟪a, β₂*⟫)| - L(a)` for `r = 2`. -/
noncomputable def r2Remainder (β₁s β₂s Δ₁ Δ₂ a : E) : ℝ :=
  |max ⟪a, β₁s + Δ₁⟫_ℝ ⟪a, β₂s + Δ₂⟫_ℝ - max ⟪a, β₁s⟫_ℝ ⟪a, β₂s⟫_ℝ| -
    (if 0 ≤ ⟪a, β₁s - β₂s⟫_ℝ then |⟪a, Δ₁⟫_ℝ| else |⟪a, Δ₂⟫_ℝ|)

/-- **Theorem 2, Step 1 (Exact Antipodal Pairing Identity)**:
On the flip cone `E_+ = {a | ⟪a, v⟫ > 0 ∧ ⟪a, v + δ⟫ < 0}` (where `v = β₁* - β₂*`, `δ = Δ₁ - Δ₂`),
pairing `a` with `-a` yields the exact identity
`R(a) + R(-a) = ψ_u(D₁) - ψ_u(D₁ + X)` with `X = ⟪a, v⟫ > 0`, `u = -⟪a, v + δ⟫ > 0`, `D₁ = ⟪a, Δ₁⟫`,
and consequently `-2 * min ⟪a, v⟫ (-⟪a, v + δ⟫) ≤ R(a) + R(-a) ≤ 0`. -/
theorem theorem2_antipodal_pairing (β₁s β₂s Δ₁ Δ₂ a : E)
    (hX : 0 < ⟪a, β₁s - β₂s⟫_ℝ)
    (hu : ⟪a, (β₁s - β₂s) + (Δ₁ - Δ₂)⟫_ℝ < 0) :
    let X := ⟪a, β₁s - β₂s⟫_ℝ
    let u := -⟪a, (β₁s - β₂s) + (Δ₁ - Δ₂)⟫_ℝ
    r2Remainder β₁s β₂s Δ₁ Δ₂ a + r2Remainder β₁s β₂s Δ₁ Δ₂ (-a) =
      psiU u ⟪a, Δ₁⟫_ℝ - psiU u (⟪a, Δ₁⟫_ℝ + X) ∧
    -2 * min X u ≤ r2Remainder β₁s β₂s Δ₁ Δ₂ a + r2Remainder β₁s β₂s Δ₁ Δ₂ (-a) ∧
    r2Remainder β₁s β₂s Δ₁ Δ₂ a + r2Remainder β₁s β₂s Δ₁ Δ₂ (-a) ≤ 0 := by
  intro X u
  have hu_pos : 0 < u := by dsimp [u]; linarith
  have h1 : ⟪a, β₂s⟫_ℝ < ⟪a, β₁s⟫_ℝ := by
    rw [inner_sub_right] at hX; linarith
  have h2 : ⟪a, β₁s + Δ₁⟫_ℝ < ⟪a, β₂s + Δ₂⟫_ℝ := by
    simp only [inner_add_right, inner_sub_right] at hu ⊢; linarith
  have hneg_v : ⟪-a, β₁s - β₂s⟫_ℝ < 0 := by rw [inner_neg_left]; linarith
  have h3 : ⟪-a, β₁s⟫_ℝ < ⟪-a, β₂s⟫_ℝ := by
    simp only [inner_neg_left]; linarith
  have h4 : ⟪-a, β₂s + Δ₂⟫_ℝ < ⟪-a, β₁s + Δ₁⟫_ℝ := by
    simp only [inner_neg_left]; linarith
  have hRa : r2Remainder β₁s β₂s Δ₁ Δ₂ a = |⟪a, Δ₁⟫_ℝ + u| - |⟪a, Δ₁⟫_ℝ| := by
    unfold r2Remainder
    rw [if_pos (le_of_lt hX), max_eq_right (le_of_lt h2), max_eq_left (le_of_lt h1)]
    have hdiff : ⟪a, β₂s + Δ₂⟫_ℝ - ⟪a, β₁s⟫_ℝ = ⟪a, Δ₁⟫_ℝ + u := by
      dsimp [u]
      simp only [inner_add_right, inner_sub_right]
      ring
    rw [hdiff]
  have hRna : r2Remainder β₁s β₂s Δ₁ Δ₂ (-a) = |⟪a, Δ₁⟫_ℝ + X| - |⟪a, Δ₁⟫_ℝ + X + u| := by
    unfold r2Remainder
    rw [if_neg (not_le.mpr hneg_v), max_eq_left (le_of_lt h4), max_eq_right (le_of_lt h3)]
    have hdiff1 : ⟪-a, β₁s + Δ₁⟫_ℝ - ⟪-a, β₂s⟫_ℝ = -(⟪a, Δ₁⟫_ℝ + X) := by
      dsimp [X]
      simp only [inner_neg_left, inner_add_right, inner_sub_right]
      ring
    have hdiff2 : ⟪-a, Δ₂⟫_ℝ = -(⟪a, Δ₁⟫_ℝ + X + u) := by
      dsimp [X, u]
      simp only [inner_neg_left, inner_add_right, inner_sub_right]
      ring
    rw [hdiff1, hdiff2, abs_neg, abs_neg]
  have hid : r2Remainder β₁s β₂s Δ₁ Δ₂ a + r2Remainder β₁s β₂s Δ₁ Δ₂ (-a) =
      psiU u ⟪a, Δ₁⟫_ℝ - psiU u (⟪a, Δ₁⟫_ℝ + X) := by
    rw [hRa, hRna]
    unfold psiU
    have hassoc : ⟪a, Δ₁⟫_ℝ + X + u = ⟪a, Δ₁⟫_ℝ + X + u := rfl
    ring
  refine ⟨hid, ?_, ?_⟩
  · rw [hid]; exact (psiU_diff_bounds hu_pos hX ⟪a, Δ₁⟫_ℝ).1
  · rw [hid]; exact (psiU_diff_bounds hu_pos hX ⟪a, Δ₁⟫_ℝ).2

/-! ### Stage B.2: Voronoi Cell Characterization and Exact Norm Inequalities -/

/-- **Theorem 2, Voronoi Cell Equivalence**:
For `r = 2`, `β* = (β₁*, β₂*)` is closer to `β = (β₁* + Δ₁, β₂* + Δ₂)` than `swap(β*) = (β₂*, β₁*)`
if and only if `⟪v, v + δ⟫_ℝ ≥ 0`, where `v = β₁* - β₂*` and `δ = Δ₁ - Δ₂`. -/
theorem theorem2_voronoi_iff (β₁s β₂s Δ₁ Δ₂ : E) :
    let β₁ := β₁s + Δ₁
    let β₂ := β₂s + Δ₂
    let v := β₁s - β₂s
    let δ := Δ₁ - Δ₂
    ‖β₁ - β₁s‖ ^ 2 + ‖β₂ - β₂s‖ ^ 2 ≤ ‖β₁ - β₂s‖ ^ 2 + ‖β₂ - β₁s‖ ^ 2 ↔
      0 ≤ ⟪v, v + δ⟫_ℝ := by
  intro β₁ β₂ v δ
  have h1 : β₁ - β₁s = Δ₁ := by dsimp [β₁]; abel
  have h2 : β₂ - β₂s = Δ₂ := by dsimp [β₂]; abel
  have h3 : β₁ - β₂s = Δ₁ + v := by dsimp [β₁, v]; abel
  have h4 : β₂ - β₁s = Δ₂ - v := by dsimp [β₂, v]; abel
  rw [h1, h2, h3, h4, norm_add_sq_real Δ₁ v, norm_sub_sq_real Δ₂ v]
  have h_inner : ⟪v, v + δ⟫_ℝ = ‖v‖ ^ 2 + (⟪Δ₁, v⟫_ℝ - ⟪Δ₂, v⟫_ℝ) := by
    rw [inner_add_right, real_inner_self_eq_norm_sq]
    dsimp [δ]
    rw [inner_sub_right, real_inner_comm Δ₁ v, real_inner_comm Δ₂ v]
  constructor <;> intro h <;> linarith

/-- **Theorem 2, Step 3 (Unconditional Global Quadratic Norm Bound)**:
For any `w₁, w₂ : E` with `w₁ ≠ 0`:
`0 ≤ ‖w₁‖ + ‖w₂‖ - ‖w₁ + w₂‖ ≤ ‖w₂ - w₁‖^2 / (2 * ‖w₁‖)`. -/
theorem theorem2_global_quadratic_norm_bound {w₁ w₂ : E} (hw₁ : w₁ ≠ 0) :
    0 ≤ ‖w₁‖ + ‖w₂‖ - ‖w₁ + w₂‖ ∧
    ‖w₁‖ + ‖w₂‖ - ‖w₁ + w₂‖ ≤ ‖w₂ - w₁‖ ^ 2 / (2 * ‖w₁‖) := by
  have ha_pos : 0 < ‖w₁‖ := norm_pos_iff.mpr hw₁
  have h_nonneg : 0 ≤ ‖w₁‖ + ‖w₂‖ - ‖w₁ + w₂‖ := by linarith [norm_add_le w₁ w₂]
  refine ⟨h_nonneg, ?_⟩
  -- Parallelogram law: `‖w₁ + w₂‖^2 + ‖w₂ - w₁‖^2 = 2 * (‖w₁‖^2 + ‖w₂‖^2)`
  have hpara : ‖w₁ + w₂‖ ^ 2 + ‖w₂ - w₁‖ ^ 2 = 2 * (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2) := by
    have h1 := norm_add_sq_real w₁ w₂
    have h2 := norm_sub_sq_real w₂ w₁
    rw [real_inner_comm w₁ w₂] at h2
    linarith
  -- Triangle inequality: `‖w₁‖ ≤ ‖w₂‖ + ‖w₁ + w₂‖`, so `2 * ‖w₁‖ ≤ ‖w₁‖ + ‖w₂‖ + ‖w₁ + w₂‖`
  have hdenom : 2 * ‖w₁‖ ≤ ‖w₁‖ + ‖w₂‖ + ‖w₁ + w₂‖ := by
    have htri : ‖w₁‖ ≤ ‖w₁ + w₂‖ + ‖-w₂‖ := by
      have : w₁ = (w₁ + w₂) + (-w₂) := by abel
      calc ‖w₁‖ = ‖(w₁ + w₂) + (-w₂)‖ := by rw [← this]
        _ ≤ ‖w₁ + w₂‖ + ‖-w₂‖ := norm_add_le _ _
    rw [norm_neg] at htri
    linarith
  have hprod : (‖w₁‖ + ‖w₂‖ - ‖w₁ + w₂‖) * (‖w₁‖ + ‖w₂‖ + ‖w₁ + w₂‖) ≤ ‖w₂ - w₁‖ ^ 2 := by
    have hsq : (‖w₁‖ + ‖w₂‖ - ‖w₁ + w₂‖) * (‖w₁‖ + ‖w₂‖ + ‖w₁ + w₂‖) =
        ‖w₂ - w₁‖ ^ 2 - (‖w₁‖ - ‖w₂‖) ^ 2 := by
      nlinarith [hpara]
    nlinarith [sq_nonneg (‖w₁‖ - ‖w₂‖)]
  rw [le_div_iff₀ (by linarith : 0 < 2 * ‖w₁‖)]
  nlinarith

/-- **Theorem 2, Step 4 (Parallelogram-Law Bound on the Voronoi Cell)**:
For any `w₁, w₂ : E` with `0 ≤ ⟪w₁, w₂⟫_ℝ`:
`‖w₁‖ + ‖w₂‖ - ‖w₁ + w₂‖ ≤ (√2 - 1) * ‖w₂ - w₁‖`. -/
theorem theorem2_voronoi_parallelogram_bound {w₁ w₂ : E} (h_inner : 0 ≤ ⟪w₁, w₂⟫_ℝ) :
    ‖w₁‖ + ‖w₂‖ - ‖w₁ + w₂‖ ≤ (Real.sqrt 2 - 1) * ‖w₂ - w₁‖ := by
  set s := ‖w₁ + w₂‖
  set c := ‖w₂ - w₁‖
  have hs0 : 0 ≤ s := norm_nonneg _
  have hc0 : 0 ≤ c := norm_nonneg _
  have hpara : s ^ 2 + c ^ 2 = 2 * (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2) := by
    have h1 := norm_add_sq_real w₁ w₂
    have h2 := norm_sub_sq_real w₂ w₁
    rw [real_inner_comm w₁ w₂] at h2
    linarith
  have hab_sq : (‖w₁‖ + ‖w₂‖) ^ 2 ≤ s ^ 2 + c ^ 2 := by
    nlinarith [sq_nonneg (‖w₁‖ - ‖w₂‖)]
  have hs_ge_c : c ≤ s := by
    have hsq : c ^ 2 ≤ s ^ 2 := by
      have h1 := norm_add_sq_real w₁ w₂
      have h2 := norm_sub_sq_real w₂ w₁
      rw [real_inner_comm w₁ w₂] at h2
      linarith
    nlinarith
  -- Show `‖w₁‖ + ‖w₂‖ ≤ s + (√2 - 1) * c` by squaring both sides!
  have hs2_pos : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hrhs0 : 0 ≤ s + (Real.sqrt 2 - 1) * c := by
    nlinarith
  have hsq_goal : (‖w₁‖ + ‖w₂‖) ^ 2 ≤ (s + (Real.sqrt 2 - 1) * c) ^ 2 := by
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    -- Expand `(s + (√2 - 1) c)^2 - (s^2 + c^2) = 2(√2 - 1) c (s - c) ≥ 0`!
    have hexpand : (s + (Real.sqrt 2 - 1) * c) ^ 2 - (s ^ 2 + c ^ 2) =
        2 * (Real.sqrt 2 - 1) * c * (s - c) := by
      calc (s + (Real.sqrt 2 - 1) * c) ^ 2 - (s ^ 2 + c ^ 2)
          = 2 * (Real.sqrt 2 - 1) * c * s + ((Real.sqrt 2) ^ 2 - 2 * Real.sqrt 2) * c ^ 2 := by ring
        _ = 2 * (Real.sqrt 2 - 1) * c * s + (2 - 2 * Real.sqrt 2) * c ^ 2 := by rw [hsq2]
        _ = 2 * (Real.sqrt 2 - 1) * c * (s - c) := by ring
    have hnonneg : 0 ≤ 2 * (Real.sqrt 2 - 1) * c * (s - c) := by
      have : 0 ≤ Real.sqrt 2 - 1 := by linarith
      have : 0 ≤ s - c := by linarith
      positivity
    linarith
  have hab0 : 0 ≤ ‖w₁‖ + ‖w₂‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith

/-- **Theorem 2, Global Scale-Free Sharp Growth (Conditional on the 2D Gaussian Remainder Bound)**:
Any swap-invariant functional `F : (Fin 2 → E) → ℝ` satisfying the one-sided remainder inequality
`(‖Δ₁‖ + ‖Δ₂‖) / √(2π) - F(β* + Δ) ≤ (‖v‖ + ‖v + δ‖ - ‖2v + δ‖) / √(2π)`
automatically satisfies **global** sharp growth on all of `E × E`:
`F(β) ≥ ((√2 - 1) / √π) * min(frobNorm(β - β*), frobNorm(β - swap β*))`. -/
theorem theorem2_global_sharpness_from_remainder
    (F : (Fin 2 → E) → ℝ) (β₁s β₂s : E)
    (h_swap : ∀ b₁ b₂ : E, F ![b₂, b₁] = F ![b₁, b₂])
    (h_rem : ∀ (Δ₁ Δ₂ : E),
      (‖Δ₁‖ + ‖Δ₂‖) / Real.sqrt (2 * Real.pi) - F ![β₁s + Δ₁, β₂s + Δ₂] ≤
      (‖β₁s - β₂s‖ + ‖(β₁s - β₂s) + (Δ₁ - Δ₂)‖ - ‖(β₁s - β₂s) + ((β₁s - β₂s) + (Δ₁ - Δ₂))‖) /
        Real.sqrt (2 * Real.pi))
    (b₁ b₂ : E) :
    let d_id := Real.sqrt (‖b₁ - β₁s‖ ^ 2 + ‖b₂ - β₂s‖ ^ 2)
    let d_sw := Real.sqrt (‖b₁ - β₂s‖ ^ 2 + ‖b₂ - β₁s‖ ^ 2)
    ((Real.sqrt 2 - 1) / Real.sqrt Real.pi) * min d_id d_sw ≤ F ![b₁, b₂] := by
  intro d_id d_sw
  -- Helper proving the bound on the Voronoi cell `d_id ≤ d_sw`
  have h_voronoi : ∀ x₁ x₂ : E,
      ‖x₁ - β₁s‖ ^ 2 + ‖x₂ - β₂s‖ ^ 2 ≤ ‖x₁ - β₂s‖ ^ 2 + ‖x₂ - β₁s‖ ^ 2 →
      ((Real.sqrt 2 - 1) / Real.sqrt Real.pi) * Real.sqrt (‖x₁ - β₁s‖ ^ 2 + ‖x₂ - β₂s‖ ^ 2) ≤
        F ![x₁, x₂] := by
    intro x₁ x₂ hle
    let Δ₁ := x₁ - β₁s
    let Δ₂ := x₂ - β₂s
    have hx₁ : β₁s + Δ₁ = x₁ := by dsimp [Δ₁]; abel
    have hx₂ : β₂s + Δ₂ = x₂ := by dsimp [Δ₂]; abel
    have h_inner : 0 ≤ ⟪β₁s - β₂s, (β₁s - β₂s) + (Δ₁ - Δ₂)⟫_ℝ := by
      have hiff := theorem2_voronoi_iff β₁s β₂s Δ₁ Δ₂
      dsimp only at hiff
      rw [hx₁, hx₂] at hiff
      exact hiff.mp hle
    have hpara := theorem2_voronoi_parallelogram_bound h_inner
    have hdiff_eq : ((β₁s - β₂s) + (Δ₁ - Δ₂)) - (β₁s - β₂s) = Δ₁ - Δ₂ := by abel
    rw [hdiff_eq] at hpara
    have htri : ‖Δ₁ - Δ₂‖ ≤ ‖Δ₁‖ + ‖Δ₂‖ := norm_sub_le Δ₁ Δ₂
    have hs2_ge1 : 0 ≤ Real.sqrt 2 - 1 := by
      have : (1 : ℝ) ≤ Real.sqrt 2 := by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      linarith
    have h_num : ‖β₁s - β₂s‖ + ‖(β₁s - β₂s) + (Δ₁ - Δ₂)‖ -
        ‖(β₁s - β₂s) + ((β₁s - β₂s) + (Δ₁ - Δ₂))‖ ≤ (Real.sqrt 2 - 1) * (‖Δ₁‖ + ‖Δ₂‖) :=
      le_trans hpara (mul_le_mul_of_nonneg_left htri hs2_ge1)
    have hrem_pt := h_rem Δ₁ Δ₂
    rw [hx₁, hx₂] at hrem_pt
    have hs2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hdiv :
        (‖β₁s - β₂s‖ + ‖(β₁s - β₂s) + (Δ₁ - Δ₂)‖ -
          ‖(β₁s - β₂s) + ((β₁s - β₂s) + (Δ₁ - Δ₂))‖) / Real.sqrt (2 * Real.pi) ≤
        ((Real.sqrt 2 - 1) * (‖Δ₁‖ + ‖Δ₂‖)) / Real.sqrt (2 * Real.pi) :=
      div_le_div_of_nonneg_right h_num (le_of_lt hs2pi_pos)
    have hF_ge : ((2 - Real.sqrt 2) / Real.sqrt (2 * Real.pi)) * (‖Δ₁‖ + ‖Δ₂‖) ≤ F ![x₁, x₂] := by
      have h1 : (‖Δ₁‖ + ‖Δ₂‖) / Real.sqrt (2 * Real.pi) -
          ((Real.sqrt 2 - 1) * (‖Δ₁‖ + ‖Δ₂‖)) / Real.sqrt (2 * Real.pi) ≤ F ![x₁, x₂] := by
        linarith
      have h2 : (‖Δ₁‖ + ‖Δ₂‖) / Real.sqrt (2 * Real.pi) -
          ((Real.sqrt 2 - 1) * (‖Δ₁‖ + ‖Δ₂‖)) / Real.sqrt (2 * Real.pi) =
          ((2 - Real.sqrt 2) / Real.sqrt (2 * Real.pi)) * (‖Δ₁‖ + ‖Δ₂‖) := by ring
      linarith
    -- Identify `(2 - √2) / √(2π) = (√2 - 1) / √π`
    have hconst_eq : (2 - Real.sqrt 2) / Real.sqrt (2 * Real.pi) =
        (Real.sqrt 2 - 1) / Real.sqrt Real.pi := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hs2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      have hspi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      field_simp [hs2_ne, hspi_ne]
      nlinarith [hsq2]
    rw [hconst_eq] at hF_ge
    -- Finally use `√(‖Δ₁‖^2 + ‖Δ₂‖^2) ≤ ‖Δ₁‖ + ‖Δ₂‖`
    have hnorm_le : Real.sqrt (‖Δ₁‖ ^ 2 + ‖Δ₂‖ ^ 2) ≤ ‖Δ₁‖ + ‖Δ₂‖ := by
      rw [Real.sqrt_le_iff]
      exact ⟨add_nonneg (norm_nonneg _) (norm_nonneg _),
             by nlinarith [norm_nonneg Δ₁, norm_nonneg Δ₂]⟩
    have hc_nonneg : 0 ≤ (Real.sqrt 2 - 1) / Real.sqrt Real.pi :=
      div_nonneg hs2_ge1 (Real.sqrt_nonneg _)
    exact le_trans (mul_le_mul_of_nonneg_left hnorm_le hc_nonneg) hF_ge
  -- Split into `d_id ≤ d_sw` vs `d_sw < d_id` (using swap invariance!)
  rcases le_or_gt (‖b₁ - β₁s‖ ^ 2 + ‖b₂ - β₂s‖ ^ 2) (‖b₁ - β₂s‖ ^ 2 + ‖b₂ - β₁s‖ ^ 2) with h | h
  · have hmin : min d_id d_sw = d_id := min_eq_left (Real.sqrt_le_sqrt h)
    rw [hmin]
    exact h_voronoi b₁ b₂ h
  · have hmin : min d_id d_sw = d_sw := min_eq_right (Real.sqrt_le_sqrt (le_of_lt h))
    rw [hmin, ← h_swap b₁ b₂]
    have hle' : ‖b₂ - β₁s‖ ^ 2 + ‖b₁ - β₂s‖ ^ 2 ≤ ‖b₂ - β₂s‖ ^ 2 + ‖b₁ - β₁s‖ ^ 2 := by linarith
    have hres := h_voronoi b₂ b₁ hle'
    have hcomm : Real.sqrt (‖b₂ - β₁s‖ ^ 2 + ‖b₁ - β₂s‖ ^ 2) = d_sw := by
      dsimp [d_sw]; rw [add_comm]
    rwa [hcomm] at hres

/-! ### Stage B.3: Exact 1D Trigonometric Integral of Theorem 2 Step 2 -/

/-- **Theorem 2, Step 2 (Exact Trigonometric Wedge Integral)**:
For any `c₁ > 0, c₂ > 0` and `θ ∈ (0, π)`,
`∫ ψ in (0 : ℝ)..θ, min (c₁ * sin ψ) (c₂ * sin (θ - ψ)) = c₁ + c₂ - √(c₁^2 + c₂^2 + 2 c₁ c₂ cos θ)`. -/
theorem theorem2_wedge_trig_integral {c₁ c₂ θ : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hθ0 : 0 < θ) (hθπ : θ < Real.pi) :
    ∫ ψ in (0 : ℝ)..θ, min (c₁ * Real.sin ψ) (c₂ * Real.sin (θ - ψ)) =
      c₁ + c₂ - Real.sqrt (c₁ ^ 2 + c₂ ^ 2 + 2 * c₁ * c₂ * Real.cos θ) := by
  -- Define the crossover angle `ψ* ∈ (0, θ)` via `arctan`
  -- Wait: use `R := √(c₁^2 + c₂^2 + 2 c₁ c₂ cos θ) > 0` and write `ψ* = arccos ((c₁ + c₂ cos θ) / R)`!
  -- Even cleaner: let `A := c₁ + c₂ * cos θ`, `B := c₂ * sin θ > 0`.
  -- Then `R = √(A^2 + B^2) > 0`, and `ψ* := Real.arccos (A / R)` satisfies:
  --   `cos ψ* = A / R`, `sin ψ* = B / R > 0`, `ψ* ∈ (0, π)`!
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  set A := c₁ + c₂ * Real.cos θ
  set B := c₂ * Real.sin θ
  have hB_pos : 0 < B := mul_pos hc₂ hsinθ
  have hAB_sq : A ^ 2 + B ^ 2 = c₁ ^ 2 + c₂ ^ 2 + 2 * c₁ * c₂ * Real.cos θ := by
    dsimp [A, B]
    have hsc := Real.sin_sq_add_cos_sq θ
    nlinarith
  set R := Real.sqrt (c₁ ^ 2 + c₂ ^ 2 + 2 * c₁ * c₂ * Real.cos θ)
  have hR_pos : 0 < R := by
    dsimp [R]
    rw [← hAB_sq]
    exact Real.sqrt_pos.mpr (by positivity)
  have hR_sq : R ^ 2 = A ^ 2 + B ^ 2 := by
    dsimp [R]; rw [← hAB_sq, Real.sq_sqrt (by positivity)]
  have hAR_le : |A / R| ≤ 1 := by
    rw [abs_div, abs_of_pos hR_pos, div_le_one hR_pos]
    have : A ^ 2 ≤ R ^ 2 := by nlinarith [sq_nonneg B]
    nlinarith [abs_nonneg A, sq_abs A]
  set ψs := Real.arccos (A / R)
  have hcos_ψs : Real.cos ψs = A / R :=
    Real.cos_arccos (neg_le_of_abs_le hAR_le) (le_of_abs_le hAR_le)
  have hsin_ψs : Real.sin ψs = B / R := by
    rw [Real.sin_arccos]
    have h1 : 1 - (A / R) ^ 2 = (B / R) ^ 2 := by
      have hR_ne : R ≠ 0 := ne_of_gt hR_pos
      field_simp [hR_ne]
      linarith
    rw [h1, Real.sqrt_sq (le_of_lt (div_pos hB_pos hR_pos))]
  have hψs_pos : 0 < ψs := by
    have hge : 0 ≤ ψs := Real.arccos_nonneg (A / R)
    rcases eq_or_lt_of_le hge with h0 | hpos
    · exfalso
      have : Real.sin ψs = 0 := by rw [← h0, Real.sin_zero]
      rw [hsin_ψs] at this
      exact ne_of_gt (div_pos hB_pos hR_pos) this
    · exact hpos
  have hψs_lt_θ : ψs < θ := by
    have hcos_lt : Real.cos θ < A / R := by
      have hsin_diff : Real.sin (θ - ψs) = c₁ * Real.sin θ / R := by
        rw [Real.sin_sub, hcos_ψs, hsin_ψs]
        dsimp [A, B]
        field_simp [ne_of_gt hR_pos]
        ring
      by_contra hle
      push_neg at hle
      have hle_diff : θ - ψs ≤ 0 := by
        have hψs_le_π : ψs ≤ Real.pi := Real.arccos_le_pi _
        have h1 : Real.cos ψs ≤ Real.cos θ := by rwa [hcos_ψs]
        have h2 : θ ≤ ψs := (Real.strictAntiOn_cos.le_iff_ge
          ⟨le_of_lt hψs_pos, hψs_le_π⟩ ⟨le_of_lt hθ0, le_of_lt hθπ⟩).mp h1
        linarith
      have hgt_neg_π : -Real.pi < θ - ψs := by linarith [Real.arccos_le_pi (A / R)]
      have hsin_nonpos : Real.sin (θ - ψs) ≤ 0 := by
        have hpos_neg : 0 ≤ -(θ - ψs) := by linarith
        have hlt_pi : -(θ - ψs) < Real.pi := by linarith
        rcases eq_or_lt_of_le hpos_neg with h0 | hp
        · have : θ - ψs = 0 := by linarith
          rw [this, Real.sin_zero]
        · have := Real.sin_pos_of_pos_of_lt_pi hp hlt_pi
          rw [Real.sin_neg] at this
          linarith
      have hsin_pos : 0 < c₁ * Real.sin θ / R := div_pos (mul_pos hc₁ hsinθ) hR_pos
      linarith
    have hψs_le_π : ψs ≤ Real.pi := Real.arccos_le_pi _
    exact (Real.strictAntiOn_cos.lt_iff_gt
      ⟨le_of_lt hθ0, le_of_lt hθπ⟩ ⟨le_of_lt hψs_pos, hψs_le_π⟩).mp (by rwa [hcos_ψs])
  -- Check that `min (c₁ sin ψ) (c₂ sin(θ - ψ))` equals `c₁ sin ψ` on `[0, ψs]` and `c₂ sin(θ - ψ)` on `[ψs, θ]`!
  -- Key identity: `c₂ sin(θ - ψ) - c₁ sin ψ = B cos ψ - A sin ψ = R * sin(ψs - ψ)`!
  have hdiff_id : ∀ ψ : ℝ, c₂ * Real.sin (θ - ψ) - c₁ * Real.sin ψ = R * Real.sin (ψs - ψ) := by
    intro ψ
    rw [Real.sin_sub θ ψ, Real.sin_sub ψs ψ, hsin_ψs, hcos_ψs]
    dsimp [A, B]
    field_simp [ne_of_gt hR_pos]
    ring
  have hmin_left : ∀ ψ ∈ Set.Icc (0 : ℝ) ψs,
      min (c₁ * Real.sin ψ) (c₂ * Real.sin (θ - ψ)) = c₁ * Real.sin ψ := by
    intro ψ hψ
    apply min_eq_left
    have h0 : 0 ≤ ψs - ψ := by linarith [hψ.2]
    have hπ : ψs - ψ ≤ Real.pi := by linarith [hψ.1, hψs_lt_θ, hθπ]
    have hsin_nn : 0 ≤ Real.sin (ψs - ψ) := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
    have hdif := hdiff_id ψ
    nlinarith [mul_nonneg (le_of_lt hR_pos) hsin_nn]
  have hmin_right : ∀ ψ ∈ Set.Icc ψs θ,
      min (c₁ * Real.sin ψ) (c₂ * Real.sin (θ - ψ)) = c₂ * Real.sin (θ - ψ) := by
    intro ψ hψ
    apply min_eq_right
    have h0 : 0 ≤ ψ - ψs := by linarith [hψ.1]
    have hπ : ψ - ψs ≤ Real.pi := by linarith [hψ.2, hψs_pos, hθπ]
    have hsin_nn : 0 ≤ Real.sin (ψ - ψs) := Real.sin_nonneg_of_nonneg_of_le_pi h0 hπ
    have hdif := hdiff_id ψ
    have hneg : Real.sin (ψs - ψ) = -Real.sin (ψ - ψs) := by
      rw [← Real.sin_neg]; ring_nf
    rw [hneg] at hdif
    nlinarith [mul_nonneg (le_of_lt hR_pos) hsin_nn]
  -- Split the integral at `ψs`
  have hint_cont : Continuous (fun ψ : ℝ => min (c₁ * Real.sin ψ) (c₂ * Real.sin (θ - ψ))) :=
    (continuous_const.mul Real.continuous_sin).min
      (continuous_const.mul (Real.continuous_sin.comp (continuous_const.sub continuous_id)))
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hint_cont.intervalIntegrable 0 ψs) (hint_cont.intervalIntegrable ψs θ)]
  -- Evaluate left integral: `∫_0^{ψs} c₁ sin ψ dψ = c₁ (1 - cos ψs)`
  have hI1 : ∫ ψ in (0 : ℝ)..ψs, min (c₁ * Real.sin ψ) (c₂ * Real.sin (θ - ψ)) =
      c₁ * (1 - Real.cos ψs) := by
    calc ∫ ψ in (0 : ℝ)..ψs, min (c₁ * Real.sin ψ) (c₂ * Real.sin (θ - ψ))
        = ∫ ψ in (0 : ℝ)..ψs, c₁ * Real.sin ψ :=
          intervalIntegral.integral_congr (fun ψ hψ =>
            hmin_left ψ (by rwa [Set.uIcc_of_le (le_of_lt hψs_pos)] at hψ))
      _ = c₁ * (1 - Real.cos ψs) := by
          rw [intervalIntegral.integral_const_mul, integral_sin, Real.cos_zero]
  -- Evaluate right integral: `∫_{ψs}^θ c₂ sin(θ - ψ) dψ = c₂ (1 - cos(θ - ψs))`
  have hI2 : ∫ ψ in ψs..θ, min (c₁ * Real.sin ψ) (c₂ * Real.sin (θ - ψ)) =
      c₂ * (1 - Real.cos (θ - ψs)) := by
    calc ∫ ψ in ψs..θ, min (c₁ * Real.sin ψ) (c₂ * Real.sin (θ - ψ))
        = ∫ ψ in ψs..θ, c₂ * Real.sin (θ - ψ) :=
          intervalIntegral.integral_congr (fun ψ hψ =>
            hmin_right ψ (by rwa [Set.uIcc_of_le (le_of_lt hψs_lt_θ)] at hψ))
      _ = c₂ * ∫ ψ in ψs..θ, Real.sin (θ - ψ) := intervalIntegral.integral_const_mul _ _
      _ = c₂ * (1 - Real.cos (θ - ψs)) := by
          have hcomp := intervalIntegral.integral_comp_sub_left (fun t => Real.sin t) θ (a := ψs) (b := θ)
          rw [sub_self] at hcomp
          rw [hcomp, integral_sin, Real.cos_zero]
  rw [hI1, hI2]
  -- Simplify `c₁(1 - cos ψs) + c₂(1 - cos(θ - ψs)) = c₁ + c₂ - R`!
  have hcos_diff : Real.cos (θ - ψs) = (c₂ + c₁ * Real.cos θ) / R := by
    rw [Real.cos_sub, hcos_ψs, hsin_ψs]
    dsimp [A, B]
    have hsc := Real.sin_sq_add_cos_sq θ
    field_simp [ne_of_gt hR_pos]
    nlinarith
  rw [hcos_ψs, hcos_diff]
  dsimp [A]
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hR_sq' : R ^ 2 = c₁ ^ 2 + c₂ ^ 2 + 2 * c₁ * c₂ * Real.cos θ := by
    dsimp [R]; exact Real.sq_sqrt (by rw [← hAB_sq]; positivity)
  field_simp [hR_ne]
  nlinarith [hR_sq']

/-! ### Stage B.4: Lemma 3.3 (Bathtub Pointwise Identity & Analytic Lower Bound) -/

/-- **Lemma 3.3 (Pointwise Bathtub Inequality)**:
For any indicator `indC ∈ {0, 1}`, any `z : ℝ`, and any threshold `z_p ≥ 0`,
`(indC - 1{|z| ≤ z_p}) * (|z| - z_p) ≥ 0`. -/
lemma lemma33_bathtub_pointwise (indC : ℝ) (h0 : 0 ≤ indC) (h1 : indC ≤ 1) (z z_p : ℝ) :
    0 ≤ (indC - (if |z| ≤ z_p then (1 : ℝ) else 0)) * (|z| - z_p) := by
  split_ifs with h
  · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · push_neg at h
    exact mul_nonneg (by linarith) (by linarith)

/-- **Lemma 3.3 (Analytic Lower Bound)**:
For all `p ∈ [0, 1]`,
`√(2/π) * (1 - exp(-π p^2 / 4)) ≥ (√(2π) / 6) * p^2`.
Proof uses `exp(-x) ≤ 1 - x + x^2/2` (standard Taylor bound on `x ≥ 0`!) — note on `x = π p^2 / 4 ≤ π/4 < 0.8`,
`1 - x + x^2/2 ≤ 1 - (2/3) x ↔ x/2 ≤ 1/3 ↔ x ≤ 2/3`! Wait: `π/4 ≈ 0.7854 > 2/3 ≈ 0.6667`, so
use the 3rd-order Taylor bound `exp(-x) ≤ 1 - x + x^2/2 - x^3/6 + x^4/24` OR check `x ≤ 0.8`:
at `x = π/4 < 0.8`, `1 - x + x^2/2 - x^3/6 + x^4/24 ≤ 1 - (2/3) x ↔ x/2 - x^2/6 + x^3/24 ≤ 1/3`!
Check at `x = 0.8`: `0.4 - 0.1067 + 0.0213 = 0.3147 < 0.3333`!!
Wait: even simpler in Mathlib: `Real.exp_le_one_add_of_nonpos` or `Real.add_one_le_exp`:
`e^x ≥ 1 + x + x^2/2` for `x ≥ 0`!!
CHECK `1 / (1 + x + x^2/2) ≤ 1 - (2/3) x` for `x ∈ [0, π/4]`!!
Multiply by `1 + x + x^2/2 > 0`:
`1 ≤ (1 - (2/3) x) (1 + x + x^2/2) = 1 + (1/3) x - (1/6) x^2 - (1/3) x^3`
`↔ (1/3) x ≥ (1/6) x^2 + (1/3) x^3 ↔ 2 ≥ x + 2 x^2`!
Check at `x = 0.8`: `0.8 + 2*(0.64) = 2.08 > 2` (barely misses!).
Now use `e^x ≥ 1 + x + x^2/2 + x^3/6` (just 1 more term, 3-line derivative proof in Lean!):
`1 ≤ (1 - (2/3) x)(1 + x + x^2/2 + x^3/6) = 1 + (1/3) x - (1/6) x^2 - (1/6) x^3 - (1/9) x^4`
Wait: `(1 - 2x/3)(1 + x + x^2/2 + x^3/6) - 1 = x(1/3 - x/6 - x^2/6 - x^3/9)` — at `x = 0.8`: `0.3333 - 0.1333 - 0.1067 - 0.0569 = +0.0364 > 0`!!
OH!! HOW CLEAN IS THAT?! -/
lemma exp_ge_cubic {x : ℝ} (hx : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
  have hsum := Real.sum_le_exp_of_nonneg hx 4
  simp [Finset.sum_range_succ, Nat.factorial] at hsum
  linarith

theorem lemma33_analytic_lower_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (Real.sqrt (2 * Real.pi) / 6) * p ^ 2 ≤
      Real.sqrt (2 / Real.pi) * (1 - Real.exp (-Real.pi * p ^ 2 / 4)) := by
  set x := Real.pi * p ^ 2 / 4
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hx_le : x ≤ 4 / 5 := by
    dsimp [x]
    have hp2 : p ^ 2 ≤ 1 := by nlinarith
    nlinarith [Real.pi_pos]
  -- From `exp x ≥ 1 + x + x^2/2 + x^3/6`, deduce `1 - exp(-x) ≥ (2/3) * x`!
  have hexp : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := exp_ge_cubic hx0
  have hpoly : 1 ≤ (1 - 2 / 3 * x) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6) := by
    -- `(1 - 2/3 x)(1 + x + x^2/2 + x^3/6) - 1 = x * (1/3 - x/6 - x^2/6 - x^3/9)`
    have hfac : (1 - 2 / 3 * x) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6) - 1 =
        x * (1 / 3 - x / 6 - x ^ 2 / 6 - x ^ 3 / 9) := by ring
    have hinner : 0 ≤ 1 / 3 - x / 6 - x ^ 2 / 6 - x ^ 3 / 9 := by
      have hx2 : x ^ 2 ≤ (4 / 5 : ℝ) ^ 2 := by nlinarith
      have hx3 : x ^ 3 ≤ (4 / 5 : ℝ) ^ 3 := by nlinarith
      linarith
    nlinarith
  have h1m : 2 / 3 * x ≤ 1 - Real.exp (-x) := by
    have hpos_exp : 0 < Real.exp x := Real.exp_pos x
    have h1m_pos : 0 ≤ 1 - 2 / 3 * x := by linarith
    have hmul : 1 ≤ (1 - 2 / 3 * x) * Real.exp x :=
      le_trans hpoly (mul_le_mul_of_nonneg_left hexp h1m_pos)
    have hinv : Real.exp (-x) ≤ 1 - 2 / 3 * x := by
      rw [Real.exp_neg, inv_le_iff_one_le_mul₀' hpos_exp]
      linarith
    linarith
  -- Multiply by `√(2/π)` and identify `√(2/π) * (2/3) * (π p^2 / 4) = (√(2π) / 6) * p^2`
  have hneg : -Real.pi * p ^ 2 / 4 = -x := by dsimp [x]; ring
  rw [hneg]
  have hstep := mul_le_mul_of_nonneg_left h1m (Real.sqrt_nonneg (2 / Real.pi))
  have hid : Real.sqrt (2 / Real.pi) * (2 / 3 * x) = (Real.sqrt (2 * Real.pi) / 6) * p ^ 2 := by
    dsimp [x]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hspi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have hspi_sq : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt (le_of_lt Real.pi_pos)
    field_simp [ne_of_gt hspi_pos]
    nlinarith [hspi_sq]
  linarith

end Research107
