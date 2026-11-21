import Research107.Population
import Research107.GaussianModel
import Research107.FlipConcentration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators InnerProductSpace ENNReal NNReal Classical

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Priority 2: Unconditional Gaussian Population Theorem 2 (Zero `h_rem` Hypothesis!) -/

/-- The actual Gaussian population L1 loss for `r = 2` max-linear regression:
`F(β) = E_{a ~ N(0, I_d)} [ |max(⟪a, β 0⟫, ⟪a, β 1⟫) - max(⟪a, β₁*⟫, ⟪a, β₂*⟫)| ]`. -/
noncomputable def popLossR2 (β₁s β₂s : E) (β : Fin 2 → E) : ℝ :=
  ∫ a : E, |max ⟪a, β 0⟫_ℝ ⟪a, β 1⟫_ℝ - max ⟪a, β₁s⟫_ℝ ⟪a, β₂s⟫_ℝ| ∂(stdGaussian E)

/-- Swap invariance of the actual Gaussian population loss `popLossR2`. -/
theorem popLossR2_swap (β₁s β₂s x₁ x₂ : E) :
    popLossR2 β₁s β₂s ![x₂, x₁] = popLossR2 β₁s β₂s ![x₁, x₂] := by
  unfold popLossR2
  congr 1; ext a
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, max_comm]

/-- Helper: `|⟪a, v⟫|` is integrable under `stdGaussian E` for any `v : E`. -/
private lemma integrable_abs_inner_stdGaussian (v : E) :
    Integrable (fun a : E => |⟪a, v⟫_ℝ|) (stdGaussian E) := by
  by_cases hv : v = 0
  · subst hv; simp
  · have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u := (‖v‖⁻¹) • v
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
    have heq : (fun a : E => |⟪a, v⟫_ℝ|) = (fun a : E => ‖v‖ * |⟪a, u⟫_ℝ|) := by
      ext a; dsimp [u]
      rw [real_inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hpos), ← mul_assoc,
          mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
    rw [heq]
    have hinner : Measurable (fun a : E => ⟪a, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    have hg : Integrable (fun z : ℝ => |z|) ((stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ)) := by
      rw [stdGaussian_map_inner_unit hu]
      exact ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).abs
    have hu_int : Integrable (fun a : E => |⟪a, u⟫_ℝ|) (stdGaussian E) :=
      (integrable_map_measure (g := fun z : ℝ => |z|)
        continuous_abs.aestronglyMeasurable hinner.aemeasurable).mp hg
    exact hu_int.const_mul ‖v‖

/-- Integrability of the `r = 2` loss integrand under `stdGaussian E`. -/
lemma integrable_r2_loss (β₁s β₂s β₁ β₂ : E) :
    Integrable (fun a : E => |max ⟪a, β₁⟫_ℝ ⟪a, β₂⟫_ℝ - max ⟪a, β₁s⟫_ℝ ⟪a, β₂s⟫_ℝ|) (stdGaussian E) := by
  have hcont : Continuous (fun a : E => |max ⟪a, β₁⟫_ℝ ⟪a, β₂⟫_ℝ - max ⟪a, β₁s⟫_ℝ ⟪a, β₂s⟫_ℝ|) := by
    refine Continuous.abs (Continuous.sub ?_ ?_)
    · exact (continuous_id.inner continuous_const).max (continuous_id.inner continuous_const)
    · exact (continuous_id.inner continuous_const).max (continuous_id.inner continuous_const)
  have hdom : Integrable (fun a : E => |⟪a, β₁ - β₁s⟫_ℝ| + |⟪a, β₂ - β₂s⟫_ℝ|) (stdGaussian E) :=
    (integrable_abs_inner_stdGaussian _).add (integrable_abs_inner_stdGaussian _)
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_abs]
  have h1 : |max ⟪a, β₁⟫_ℝ ⟪a, β₂⟫_ℝ - max ⟪a, β₁s⟫_ℝ ⟪a, β₂s⟫_ℝ| ≤
      max |⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ| |⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ| := by
    rw [abs_le]
    constructor
    · have h1a : ⟪a, β₁s⟫_ℝ - ⟪a, β₁⟫_ℝ ≤ max |⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ| |⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ| := by
        have : ⟪a, β₁s⟫_ℝ - ⟪a, β₁⟫_ℝ = -(⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ) := by ring
        rw [this]; exact le_trans (neg_le_abs _) (le_max_left _ _)
      have h2a : ⟪a, β₂s⟫_ℝ - ⟪a, β₂⟫_ℝ ≤ max |⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ| |⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ| := by
        have : ⟪a, β₂s⟫_ℝ - ⟪a, β₂⟫_ℝ = -(⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ) := by ring
        rw [this]; exact le_trans (neg_le_abs _) (le_max_right _ _)
      have : max ⟪a, β₁s⟫_ℝ ⟪a, β₂s⟫_ℝ ≤ max ⟪a, β₁⟫_ℝ ⟪a, β₂⟫_ℝ +
          max |⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ| |⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ| :=
        max_le (by linarith [le_max_left ⟪a, β₁⟫_ℝ ⟪a, β₂⟫_ℝ])
               (by linarith [le_max_right ⟪a, β₁⟫_ℝ ⟪a, β₂⟫_ℝ])
      linarith
    · have h1b : ⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ ≤ max |⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ| |⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ| :=
        le_trans (le_abs_self _) (le_max_left _ _)
      have h2b : ⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ ≤ max |⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ| |⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ| :=
        le_trans (le_abs_self _) (le_max_right _ _)
      have : max ⟪a, β₁⟫_ℝ ⟪a, β₂⟫_ℝ ≤ max ⟪a, β₁s⟫_ℝ ⟪a, β₂s⟫_ℝ +
          max |⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ| |⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ| :=
        max_le (by linarith [le_max_left ⟪a, β₁s⟫_ℝ ⟪a, β₂s⟫_ℝ])
               (by linarith [le_max_right ⟪a, β₁s⟫_ℝ ⟪a, β₂s⟫_ℝ])
      linarith
  have h2 : max |⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ| |⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ| ≤
      |⟪a, β₁ - β₁s⟫_ℝ| + |⟪a, β₂ - β₂s⟫_ℝ| := by
    rw [inner_sub_right, inner_sub_right]
    exact max_le (by linarith [abs_nonneg (⟪a, β₂⟫_ℝ - ⟪a, β₂s⟫_ℝ)])
                 (by linarith [abs_nonneg (⟪a, β₁⟫_ℝ - ⟪a, β₁s⟫_ℝ)])
  exact le_trans h1 h2

/-- Exact Gaussian wedge integral for any two vectors `v, w : E`:
`∫ a, (if ⟪a, v⟫ * ⟪a, w⟫ < 0 then min |⟪a, v⟫| |⟪a, w⟫| else 0) ∂(stdGaussian E)`
`= (‖v‖ + ‖w‖ - ‖v + w‖) / √(2 π)`.
Handles ALL cases uniformly: `v = 0`, `w = 0`, collinear `v, w` (including `d = 1`), and linearly independent `v, w`. -/
theorem integral_gaussian_min_wedge (v w : E) :
    ∫ a : E, (if ⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0 then min |⟪a, v⟫_ℝ| |⟪a, w⟫_ℝ| else 0) ∂(stdGaussian E) =
      (‖v‖ + ‖w‖ - ‖v + w‖) / Real.sqrt (2 * Real.pi) := by
  by_cases hv : v = 0
  · subst hv; simp
  · by_cases hw : w = 0
    · subst hw; simp
    · have hv_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
      set e₁ : E := (‖v‖⁻¹) • v
      have he₁ : ‖e₁‖ = 1 := by
        dsimp [e₁]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv_pos), inv_mul_cancel₀ (ne_of_gt hv_pos)]
      set c_proj : ℝ := ⟪e₁, w⟫_ℝ
      set u_orth : E := w - c_proj • e₁
      have hu_orth_ip : ⟪e₁, u_orth⟫_ℝ = 0 := by
        dsimp [u_orth, c_proj]
        rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he₁]; ring
      by_cases hu : u_orth = 0
      · -- Collinear case `w = c_proj • e₁ = (c_proj / ‖v‖) • v` (covers all `d = 1` cases!)
        have hw_eq : w = (c_proj / ‖v‖) • v := by
          have h1 : w = c_proj • e₁ := sub_eq_zero.mp hu
          rw [h1]; dsimp [e₁]; rw [smul_smul, div_eq_mul_inv]
        set lam : ℝ := c_proj / ‖v‖
        rcases lt_trichotomy lam 0 with hneg | hzero | hpos
        · -- Opposite directions `lam < 0`: `⟪a, v⟫ * ⟪a, w⟫ < 0` a.e. (`⟪a, v⟫ ≠ 0`)!
          have h_ae : (fun a : E => if ⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0 then min |⟪a, v⟫_ℝ| |⟪a, w⟫_ℝ| else 0) =ᵐ[stdGaussian E]
              (fun a : E => min 1 (-lam) * |⟪a, v⟫_ℝ|) := by
            have hne : ∀ᵐ a ∂(stdGaussian E), ⟪a, v⟫_ℝ ≠ 0 := by
              rw [ae_iff]
              have : {a : E | ¬ ⟪a, v⟫_ℝ ≠ 0} = {a : E | ⟪a, v⟫_ℝ = 0} := by ext a; simp
              rw [this]; exact stdGaussian_hyperplane_zero hv
            filter_upwards [hne] with a ha
            have hprod : ⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0 := by
              rw [hw_eq, real_inner_smul_right]
              have hsq : 0 < ⟪a, v⟫_ℝ ^ 2 := sq_pos_of_ne_zero ha
              nlinarith
            rw [if_pos hprod, hw_eq, real_inner_smul_right, abs_mul, abs_of_neg hneg]
            calc min |⟪a, v⟫_ℝ| ((-lam) * |⟪a, v⟫_ℝ|)
                = min (1 * |⟪a, v⟫_ℝ|) ((-lam) * |⟪a, v⟫_ℝ|) := by rw [one_mul]
              _ = min 1 (-lam) * |⟪a, v⟫_ℝ| := (min_mul_of_nonneg 1 (-lam) (abs_nonneg _)).symm
          rw [integral_congr_ae h_ae, integral_const_mul, integral_abs_inner_stdGaussian]
          -- Check `min 1 (-lam) * ‖v‖ * √(2 / π) = (‖v‖ + ‖lam • v‖ - ‖v + lam • v‖) / √(2 π)`!
          have hnorm_w : ‖w‖ = (-lam) * ‖v‖ := by
            rw [hw_eq, norm_smul, Real.norm_eq_abs, abs_of_neg hneg]
          have hnorm_sum : ‖v + w‖ = |1 + lam| * ‖v‖ := by
            have h1 : v + w = (1 + lam) • v := by rw [hw_eq, add_smul, one_smul]
            rw [h1, norm_smul, Real.norm_eq_abs]
          have hmin_eq : 2 * min 1 (-lam) = 1 + (-lam) - |1 + lam| := by
            rcases le_or_gt (-1) lam with h1 | h1
            · rw [abs_of_nonneg (by linarith), min_eq_right (by linarith)]; ring
            · rw [abs_of_neg (by linarith), min_eq_left (by linarith)]; ring
          rw [hnorm_w, hnorm_sum]
          have hsqrt : Real.sqrt (2 / Real.pi) = 2 / Real.sqrt (2 * Real.pi) := by
            rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
            have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
            have hspi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
            have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
            field_simp [hs2, hspi]; linarith
          rw [hsqrt]
          have hnum : min 1 (-lam) * ‖v‖ * 2 = ‖v‖ + -lam * ‖v‖ - |1 + lam| * ‖v‖ := by nlinarith
          have hs2pi : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
          field_simp [hs2pi]; linarith
        · exfalso; rw [hzero, zero_smul] at hw_eq; exact hw hw_eq
        · -- Same direction `lam > 0`: `⟪a, v⟫ * ⟪a, w⟫ ≥ 0` everywhere, AND `‖v‖ + ‖w‖ - ‖v + w‖ = 0`!
          have h0 : ∀ a : E, (if ⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0 then min |⟪a, v⟫_ℝ| |⟪a, w⟫_ℝ| else 0) = 0 := by
            intro a
            apply if_neg
            rw [hw_eq, real_inner_smul_right]
            push Not
            nlinarith [sq_nonneg ⟪a, v⟫_ℝ]
          simp only [h0, integral_zero]
          have hnorm_w : ‖w‖ = lam * ‖v‖ := by
            rw [hw_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
          have hnorm_sum : ‖v + w‖ = (1 + lam) * ‖v‖ := by
            have h1 : v + w = (1 + lam) • v := by rw [hw_eq, add_smul, one_smul]
            rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
          rw [hnorm_w, hnorm_sum]; ring
      · -- Linearly independent 2D case!
        -- Orient orthonormal basis `b₁ := -e₂`, `b₂ := e₁` so that
        -- `⟪a, v⟫ = c₁ * z₂` and `⟪a, w⟫ = -c₂ * sin θ * z₁ + c₂ * cos θ * z₂`!
        -- In polar coordinates `(r cos φ, r sin φ)`:
        -- `⟪a, v⟫ = r c₁ sin φ` and `⟪a, w⟫ = r c₂ sin (φ - θ)` — ZERO wrap-around at `±π`!
        have hu_pos : 0 < ‖u_orth‖ := norm_pos_iff.mpr hu
        set e₂ : E := (‖u_orth‖⁻¹) • u_orth
        have he₂ : ‖e₂‖ = 1 := by
          dsimp [e₂]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu_pos), inv_mul_cancel₀ (ne_of_gt hu_pos)]
        have he₁₂ : ⟪e₁, e₂⟫_ℝ = 0 := by dsimp [e₂]; rw [real_inner_smul_right, hu_orth_ip, mul_zero]
        set b₁ : E := -e₂
        set b₂ : E := e₁
        have hb₁ : ‖b₁‖ = 1 := by dsimp [b₁]; rw [norm_neg, he₂]
        have hb₂ : ‖b₂‖ = 1 := he₁
        have hb₁₂ : ⟪b₁, b₂⟫_ℝ = 0 := by dsimp [b₁, b₂]; rw [inner_neg_left, real_inner_comm, he₁₂, neg_zero]
        set c₁ : ℝ := ‖v‖
        set c₂ : ℝ := ‖w‖
        have hpyth : c_proj ^ 2 + ‖u_orth‖ ^ 2 = c₂ ^ 2 := by
          have hw_dec : w = c_proj • e₁ + u_orth := by dsimp [u_orth]; abel
          have h1 : ‖w‖ ^ 2 = ‖c_proj • e₁‖ ^ 2 + 2 * ⟪c_proj • e₁, u_orth⟫_ℝ + ‖u_orth‖ ^ 2 := by
            conv_lhs => rw [hw_dec]; exact norm_add_sq_real _ _
          rw [norm_smul, Real.norm_eq_abs, he₁, mul_one, sq_abs, real_inner_smul_left, hu_orth_ip] at h1
          dsimp [c₂]; linarith
        have hcos_le : |c_proj / c₂| ≤ 1 := by
          rw [abs_div, abs_of_pos hw_pos, div_le_one hw_pos]
          have : c_proj ^ 2 ≤ c₂ ^ 2 := by nlinarith [sq_nonneg ‖u_orth‖]
          nlinarith [abs_nonneg c_proj, sq_abs c_proj]
        set θ : ℝ := Real.arccos (c_proj / c₂)
        have hcos_θ : Real.cos θ = c_proj / c₂ :=
          Real.cos_arccos (neg_le_of_abs_le hcos_le) (le_of_abs_le hcos_le)
        have hsin_θ : Real.sin θ = ‖u_orth‖ / c₂ := by
          rw [Real.sin_arccos]
          have h1 : 1 - (c_proj / c₂) ^ 2 = (‖u_orth‖ / c₂) ^ 2 := by
            field_simp [ne_of_gt hw_pos]; linarith
          rw [h1, Real.sqrt_sq (le_of_lt (div_pos hu_pos hw_pos))]
        have hθ0 : 0 < θ := by
          have hge : 0 ≤ θ := Real.arccos_nonneg _
          rcases eq_or_lt_of_le hge with h0 | hp
          · exfalso
            have : Real.sin θ = 0 := by rw [← h0, Real.sin_zero]
            rw [hsin_θ] at this
            exact ne_of_gt (div_pos hu_pos hw_pos) this
          · exact hp
        have hθπ : θ < Real.pi := by
          have hle : θ ≤ Real.pi := Real.arccos_le_pi _
          rcases eq_or_lt_of_le hle with hπ | hlt
          · exfalso
            have : Real.sin θ = 0 := by rw [hπ, Real.sin_pi]
            rw [hsin_θ] at this
            exact ne_of_gt (div_pos hu_pos hw_pos) this
          · exact hlt
        -- Express `⟪a, v⟫` and `⟪a, w⟫` in terms of `(z₁, z₂) = (⟪a, b₁⟫, ⟪a, b₂⟫)`
        have hv_coord : ∀ a : E, ⟪a, v⟫_ℝ = c₁ * ⟪a, b₂⟫_ℝ := by
          intro a; dsimp [b₂, e₁, c₁]
          rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hv_pos), one_mul]
        have hw_coord : ∀ a : E, ⟪a, w⟫_ℝ = -c₂ * Real.sin θ * ⟪a, b₁⟫_ℝ + c₂ * Real.cos θ * ⟪a, b₂⟫_ℝ := by
          intro a
          have hw_dec : w = (-‖u_orth‖) • b₁ + c_proj • b₂ := by
            dsimp [b₁, b₂, e₂, u_orth]
            rw [smul_neg, neg_smul, neg_neg, smul_smul, mul_inv_cancel₀ (ne_of_gt hu_pos), one_smul]; abel
          conv_lhs => rw [hw_dec]
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hsin_θ, hcos_θ]
          field_simp [ne_of_gt hw_pos]
        -- Define 2D integrand `G : ℝ × ℝ → ℝ`
        let G : ℝ × ℝ → ℝ := fun z =>
          let xv := c₁ * z.2
          let xw := -c₂ * Real.sin θ * z.1 + c₂ * Real.cos θ * z.2
          if xv * xw < 0 then min |xv| |xw| else 0
        have hG_meas : Measurable G := by
          dsimp [G]
          have hxv : Measurable (fun z : ℝ × ℝ => c₁ * z.2) := by fun_prop
          have hxw : Measurable (fun z : ℝ × ℝ => -c₂ * Real.sin θ * z.1 + c₂ * Real.cos θ * z.2) := by fun_prop
          exact Measurable.ite (measurableSet_lt (hxv.mul hxw) measurable_const)
            ((continuous_abs.measurable.comp hxv).min (continuous_abs.measurable.comp hxw)) measurable_const
        have hG_int : Integrable G ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
          have h_z2 : Integrable (fun z : ℝ × ℝ => c₁ * |z.2|) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
            have h1 : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) :=
              ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).abs
            exact (h1.comp_snd (gaussianReal 0 1)).const_mul c₁
          refine h_z2.mono' hG_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
          have hnn : 0 ≤ G z := by dsimp [G]; split_ifs <;> [exact le_min (abs_nonneg _) (abs_nonneg _); exact le_rfl]
          rw [Real.norm_eq_abs, abs_of_nonneg hnn]
          dsimp [G]
          split_ifs
          · calc min |c₁ * z.2| |-c₂ * Real.sin θ * z.1 + c₂ * Real.cos θ * z.2|
                ≤ |c₁ * z.2| := min_le_left _ _
              _ = c₁ * |z.2| := by rw [abs_mul, abs_of_pos hv_pos]
          · exact mul_nonneg (le_of_lt hv_pos) (abs_nonneg _)
        -- Push forward from `stdGaussian E` to `N(0,1) × N(0,1)`
        have hpair_meas : Measurable (fun a : E => (⟪a, b₁⟫_ℝ, ⟪a, b₂⟫_ℝ)) :=
          ((continuous_id.inner continuous_const).measurable).prodMk
            ((continuous_id.inner continuous_const).measurable)
        have hpush : ∫ a : E, (if ⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0 then min |⟪a, v⟫_ℝ| |⟪a, w⟫_ℝ| else 0) ∂(stdGaussian E) =
            ∫ z : ℝ × ℝ, G z ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
          have hcomp : (fun a : E => if ⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0 then min |⟪a, v⟫_ℝ| |⟪a, w⟫_ℝ| else 0) =
              fun a => G (⟪a, b₁⟫_ℝ, ⟪a, b₂⟫_ℝ) := by
            ext a; dsimp [G]; rw [hv_coord a, hw_coord a]
          rw [hcomp, ← stdGaussian_map_inner_pair hb₁ hb₂ hb₁₂]
          exact (integral_map (φ := fun a : E => (⟪a, b₁⟫_ℝ, ⟪a, b₂⟫_ℝ)) (f := G)
            hpair_meas.aemeasurable hG_meas.aestronglyMeasurable).symm
        rw [hpush, integral_stdGaussian2D_polar hG_int]
        -- Separate radial and angular parts in polar coordinates!
        let ang : ℝ → ℝ := fun φ =>
          if Real.sin φ * Real.sin (φ - θ) < 0 then
            min (c₁ * |Real.sin φ|) (c₂ * |Real.sin (φ - θ)|)
          else 0
        have hcongr : ∫ p in polarCoord.target, (p.1 * Real.exp (-p.1 ^ 2 / 2)) * G (polarCoord.symm p) =
            ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
              (p.1 ^ 2 * Real.exp (-p.1 ^ 2 / 2)) * ang p.2 := by
          refine setIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
          have hr_pos : 0 < p.1 := hp.1
          simp only [polarCoord_symm_apply, G, ang]
          have hsin_sub : -c₂ * Real.sin θ * (p.1 * Real.cos p.2) + c₂ * Real.cos θ * (p.1 * Real.sin p.2) =
              p.1 * c₂ * Real.sin (p.2 - θ) := by
            rw [Real.sin_sub]; ring
          have hxv : c₁ * (p.1 * Real.sin p.2) = p.1 * c₁ * Real.sin p.2 := by ring
          rw [hxv, hsin_sub]
          have hprod_iff : (p.1 * c₁ * Real.sin p.2) * (p.1 * c₂ * Real.sin (p.2 - θ)) < 0 ↔
              Real.sin p.2 * Real.sin (p.2 - θ) < 0 := by
            have hpos_coeff : 0 < p.1 * c₁ * (p.1 * c₂) := by positivity
            have hfac : (p.1 * c₁ * Real.sin p.2) * (p.1 * c₂ * Real.sin (p.2 - θ)) =
                (p.1 * c₁ * (p.1 * c₂)) * (Real.sin p.2 * Real.sin (p.2 - θ)) := by ring
            rw [hfac]
            exact mul_neg_iff.trans ⟨fun h => h.elim (fun h1 => h1.2) (fun h2 => absurd h2.1 (not_lt.mpr (le_of_lt hpos_coeff))),
              fun h => Or.inl ⟨hpos_coeff, h⟩⟩
          by_cases hneg : Real.sin p.2 * Real.sin (p.2 - θ) < 0
          · rw [if_pos (hprod_iff.mpr hneg), if_pos hneg, abs_mul, abs_mul, abs_mul, abs_mul,
                abs_of_pos hr_pos, abs_of_pos hv_pos, abs_of_pos hw_pos]
            have hmin_fac : min (p.1 * c₁ * |Real.sin p.2|) (p.1 * c₂ * |Real.sin (p.2 - θ)|) =
                p.1 * min (c₁ * |Real.sin p.2|) (c₂ * |Real.sin (p.2 - θ)|) := by
              rw [mul_assoc, mul_assoc, ← mul_min_of_nonneg _ _ (le_of_lt hr_pos)]
            rw [hmin_fac]; ring
          · rw [if_neg (fun h => hneg (hprod_iff.mp h)), if_neg hneg, mul_zero, mul_zero]
        rw [hcongr,
            show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
            setIntegral_prod_mul (f := fun r => r ^ 2 * Real.exp (-r ^ 2 / 2)) (g := ang)]
        -- Evaluate radial integral `∫_0^∞ r^2 e^{-r^2/2} dr = √(π / 2)`
        have hrad : ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * Real.exp (-r ^ 2 / 2) = Real.sqrt (Real.pi / 2) := by
          have h1 := integral_pow_mul_exp_neg_sq_div_two 1
          simp only [Nat.cast_one] at h1
          rw [h1]
          have harg : (1 : ℝ) + (1 : ℝ) / 2 = (1 / 2 : ℝ) + 1 := by norm_num
          rw [harg, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq,
              ← Real.sqrt_eq_rpow, Real.sqrt_div (le_of_lt Real.pi_pos)]
          have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
          have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          field_simp [hs2]; nlinarith [hsq2]
        -- Evaluate angular integral `∫_{-π}^π ang φ dφ = 2 * (c₁ + c₂ - √(c₁^2 + c₂^2 + 2 c₁ c₂ cos θ))`!
        have hang_val : ∫ φ in Set.Ioo (-Real.pi) Real.pi, ang φ =
            2 * (c₁ + c₂ - Real.sqrt (c₁ ^ 2 + c₂ ^ 2 + 2 * c₁ * c₂ * Real.cos θ)) := by
          -- Split `∫_{-π}^π = ∫_{-π}^{-π+θ} + ∫_{-π+θ}^0 + ∫_0^θ + ∫_θ^π` using interval integrals!
          have hang_eq_int : ∫ φ in Set.Ioo (-Real.pi) Real.pi, ang φ = ∫ φ in (-Real.pi)..Real.pi, ang φ := by
            rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
                integral_Ioc_eq_integral_Ioo]
          rw [hang_eq_int]
          have hang_int : ∀ a b : ℝ, IntervalIntegrable ang volume a b := by
            intro a b
            have hmeas : Measurable ang := by
              dsimp [ang]
              have h1 : Measurable (fun φ : ℝ => Real.sin φ) := Real.continuous_sin.measurable
              have h2 : Measurable (fun φ : ℝ => Real.sin (φ - θ)) :=
                Real.continuous_sin.measurable.comp (measurable_id.sub measurable_const)
              exact Measurable.ite (measurableSet_lt (h1.mul h2) measurable_const)
                (((continuous_abs.measurable.comp h1).const_mul c₁).min
                  ((continuous_abs.measurable.comp h2).const_mul c₂)) measurable_const
            refine (intervalIntegrable_const (c := c₁)).mono_fun' hmeas.aestronglyMeasurable
              (Filter.Eventually.of_forall fun φ => ?_)
            have hnn : 0 ≤ ang φ := by dsimp [ang]; split_ifs <;> [exact le_min (by positivity) (by positivity); exact le_rfl]
            dsimp only
            rw [Real.norm_eq_abs, abs_of_nonneg hnn]
            dsimp [ang]; split_ifs
            · calc min (c₁ * |Real.sin φ|) (c₂ * |Real.sin (φ - θ)|)
                  ≤ c₁ * |Real.sin φ| := min_le_left _ _
                _ ≤ c₁ * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one φ) (le_of_lt hv_pos)
                _ = c₁ := mul_one _
            · exact le_of_lt hv_pos
          have hsplit : ∫ φ in (-Real.pi)..Real.pi, ang φ =
              (∫ φ in (-Real.pi)..(-Real.pi + θ), ang φ) +
              (∫ φ in (-Real.pi + θ)..(0 : ℝ), ang φ) +
              (∫ φ in (0 : ℝ)..θ, ang φ) +
              (∫ φ in θ..Real.pi, ang φ) := by
            have h1 := intervalIntegral.integral_add_adjacent_intervals (hang_int (-Real.pi) (-Real.pi + θ))
              (hang_int (-Real.pi + θ) 0)
            have h2 := intervalIntegral.integral_add_adjacent_intervals (hang_int (-Real.pi) 0)
              (hang_int 0 θ)
            have h3 := intervalIntegral.integral_add_adjacent_intervals (hang_int (-Real.pi) θ)
              (hang_int θ Real.pi)
            linarith
          rw [hsplit]
          -- (a) On `(0, θ)`: `ang φ = min (c₁ sin φ) (c₂ sin (θ - φ))`
          have hI3 : ∫ φ in (0 : ℝ)..θ, ang φ =
              ∫ φ in (0 : ℝ)..θ, min (c₁ * Real.sin φ) (c₂ * Real.sin (θ - φ)) := by
            rw [intervalIntegral.integral_of_le (le_of_lt hθ0),
                intervalIntegral.integral_of_le (le_of_lt hθ0),
                integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
            refine setIntegral_congr_fun measurableSet_Ioo (fun φ hφ => ?_)
            have hsp : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 (lt_trans hφ.2 hθπ)
            have hst : 0 < Real.sin (θ - φ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.2]) (by linarith [hφ.1])
            have hneg_sin : Real.sin (φ - θ) = -Real.sin (θ - φ) := by rw [← Real.sin_neg]; congr 1; ring
            dsimp [ang]
            rw [hneg_sin, if_pos (by nlinarith), abs_of_pos hsp, abs_neg, abs_of_pos hst]
          -- (b) On `(-π, -π + θ)`: shift by `+π`, exact same integral as `(0, θ)`!
          have hI1 : ∫ φ in (-Real.pi)..(-Real.pi + θ), ang φ = ∫ φ in (0 : ℝ)..θ, ang φ := by
            have hcomp := intervalIntegral.integral_comp_add_left ang (-Real.pi) (a := (0 : ℝ)) (b := θ)
            rw [add_zero] at hcomp
            rw [← hcomp]
            refine intervalIntegral.integral_congr (fun ψ _ => ?_)
            dsimp [ang]
            have hs1 : Real.sin (-Real.pi + ψ) = -Real.sin ψ := by
              rw [show -Real.pi + ψ = -(Real.pi - ψ) by ring, Real.sin_neg, Real.sin_pi_sub]
            have hs2 : Real.sin (-Real.pi + ψ - θ) = -Real.sin (ψ - θ) := by
              rw [show -Real.pi + ψ - θ = -(Real.pi - (ψ - θ)) by ring, Real.sin_neg, Real.sin_pi_sub]
            rw [hs1, hs2, neg_mul_neg, abs_neg, abs_neg]
          -- (c) On `(-π + θ, 0)`: `ang φ = 0`
          have hI2 : ∫ φ in (-Real.pi + θ)..(0 : ℝ), ang φ = 0 := by
            rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
            have h0 : ∀ φ ∈ Set.Ioo (-Real.pi + θ) (0 : ℝ), ang φ = 0 := by
              intro φ hφ
              dsimp [ang]
              apply if_neg
              have hs1 : Real.sin φ < 0 := by
                have h := Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.2] : 0 < -φ) (by linarith [hφ.1, hθ0] : -φ < Real.pi)
                rw [Real.sin_neg] at h; linarith
              have hs2 : Real.sin (φ - θ) < 0 := by
                have h := Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.2, hθ0] : 0 < -(φ - θ))
                  (by linarith [hφ.1] : -(φ - θ) < Real.pi)
                rw [Real.sin_neg] at h; linarith
              push Not; nlinarith
            rw [setIntegral_congr_fun measurableSet_Ioo h0, integral_zero]
          -- (d) On `(θ, π)`: `ang φ = 0`
          have hI4 : ∫ φ in θ..Real.pi, ang φ = 0 := by
            rw [intervalIntegral.integral_of_le (le_of_lt hθπ), integral_Ioc_eq_integral_Ioo]
            have h0 : ∀ φ ∈ Set.Ioo θ Real.pi, ang φ = 0 := by
              intro φ hφ
              dsimp [ang]
              apply if_neg
              have hs1 : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (lt_trans hθ0 hφ.1) hφ.2
              have hs2 : 0 < Real.sin (φ - θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.1]) (by linarith [hφ.2, hθ0])
              push Not; nlinarith
            rw [setIntegral_congr_fun measurableSet_Ioo h0, integral_zero]
          rw [hI1, hI2, hI4, hI3, theorem2_wedge_trig_integral hv_pos hw_pos hθ0 hθπ]
          ring
        rw [hrad, hang_val]
        -- Identify `√(c₁^2 + c₂^2 + 2 c₁ c₂ cos θ) = ‖v + w‖`!
        have hnorm_sum : Real.sqrt (c₁ ^ 2 + c₂ ^ 2 + 2 * c₁ * c₂ * Real.cos θ) = ‖v + w‖ := by
          have hinner_vw : ⟪v, w⟫_ℝ = c₁ * c₂ * Real.cos θ := by
            rw [hcos_θ]
            have hv_eq : v = c₁ • e₁ := by
              dsimp [e₁, c₁]; rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hv_pos), one_smul]
            conv_lhs => rw [hv_eq]
            rw [real_inner_smul_left]
            dsimp [c_proj]
            field_simp [ne_of_gt hw_pos]
          have hsq : c₁ ^ 2 + c₂ ^ 2 + 2 * c₁ * c₂ * Real.cos θ = ‖v + w‖ ^ 2 := by
            rw [norm_add_sq_real, hinner_vw]; dsimp [c₁, c₂]; ring
          rw [hsq, Real.sqrt_sq (norm_nonneg _)]
        rw [hnorm_sum]
        -- Simplify `(2π)⁻¹ * (√(π/2) * (2 * (‖v‖ + ‖w‖ - ‖v + w‖))) = (‖v‖ + ‖w‖ - ‖v + w‖) / √(2π)`
        have hconst : (2 * Real.pi)⁻¹ * (Real.sqrt (Real.pi / 2) * (2 * (‖v‖ + ‖w‖ - ‖v + w‖))) =
            (‖v‖ + ‖w‖ - ‖v + w‖) / Real.sqrt (2 * Real.pi) := by
          have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
          have hspi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
          have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
          have hsq_pi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt (le_of_lt Real.pi_pos)
          rw [Real.sqrt_div (le_of_lt Real.pi_pos), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          field_simp [hs2, hspi, hpi_ne]
          rw [hsq_pi]
        exact hconst

/-- **Theorem 2, Unconditional Gaussian Remainder Bounds (Eliminates `h_rem`!)**:
For ANY finite-dimensional real inner product space `E` (including `d = 1`) and ANY `β₁s β₂s Δ₁ Δ₂ : E`
(including `β₁s = β₂s`, `v + δ = 0`, and collinear directions), setting `v = β₁s - β₂s` and `δ = Δ₁ - Δ₂`:
`(‖Δ₁‖ + ‖Δ₂‖) / √(2π) - (‖v‖ + ‖v + δ‖ - ‖2v + δ‖) / √(2π) ≤ popLossR2 β₁s β₂s ![β₁s + Δ₁, β₂s + Δ₂]`
and `popLossR2 β₁s β₂s ![β₁s + Δ₁, β₂s + Δ₂] ≤ (‖Δ₁‖ + ‖Δ₂‖) / √(2π)`. -/
theorem theorem2_gaussian_remainder_bounds (β₁s β₂s Δ₁ Δ₂ : E) :
    let v := β₁s - β₂s
    let δ := Δ₁ - Δ₂
    (‖Δ₁‖ + ‖Δ₂‖) / Real.sqrt (2 * Real.pi) -
      (‖v‖ + ‖v + δ‖ - ‖v + (v + δ)‖) / Real.sqrt (2 * Real.pi) ≤
      popLossR2 β₁s β₂s ![β₁s + Δ₁, β₂s + Δ₂] ∧
    popLossR2 β₁s β₂s ![β₁s + Δ₁, β₂s + Δ₂] ≤
      (‖Δ₁‖ + ‖Δ₂‖) / Real.sqrt (2 * Real.pi) := by
  intro v δ
  have hsqrt_eq : ∀ x : ℝ, x * Real.sqrt (2 / Real.pi) / 2 = x / Real.sqrt (2 * Real.pi) := by
    intro x
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hspi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hs2, hspi]; rw [hsq2]
  by_cases hv : v = 0
  · -- Degenerate case `β₁s = β₂s`: exact equality `popLossR2 = (‖Δ₁‖ + ‖Δ₂‖) / √(2π)` and remainder = 0!
    have hβeq : β₁s = β₂s := sub_eq_zero.mp hv
    have hloss_eq : popLossR2 β₁s β₂s ![β₁s + Δ₁, β₂s + Δ₂] = (‖Δ₁‖ + ‖Δ₂‖) / Real.sqrt (2 * Real.pi) := by
      unfold popLossR2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hβeq]
      let g : E → ℝ := fun a => |max ⟪a, Δ₁⟫_ℝ ⟪a, Δ₂⟫_ℝ|
      have hrewrite : (fun a : E => |max ⟪a, β₂s + Δ₁⟫_ℝ ⟪a, β₂s + Δ₂⟫_ℝ - max ⟪a, β₂s⟫_ℝ ⟪a, β₂s⟫_ℝ|) = g := by
        ext a; dsimp [g]
        rw [inner_add_right, inner_add_right, max_self, max_add_add_left, add_sub_cancel_left]
      rw [hrewrite]
      have hg_int : Integrable g (stdGaussian E) := by
        have := integrable_r2_loss β₂s β₂s (β₂s + Δ₁) (β₂s + Δ₂)
        rwa [hrewrite] at this
      have hneg_eq : ∫ a : E, g a ∂(stdGaussian E) = ∫ a : E, g (-a) ∂(stdGaussian E) := by
        have hsym := stdGaussian_neg_invariant (E := E)
        have haesm : AEStronglyMeasurable g ((stdGaussian E).map (fun a : E => -a)) := by
          rw [hsym]; exact hg_int.aestronglyMeasurable
        conv_lhs => rw [← hsym]
        exact integral_map (φ := fun a : E => -a) (f := g) continuous_neg.measurable.aemeasurable haesm
      have hg_neg_int : Integrable (fun a : E => g (-a)) (stdGaussian E) := by
        have hsym := stdGaussian_neg_invariant (E := E)
        have haesm : AEStronglyMeasurable g ((stdGaussian E).map (fun a : E => -a)) := by
          rw [hsym]; exact hg_int.aestronglyMeasurable
        exact (integrable_map_measure (g := g) haesm continuous_neg.measurable.aemeasurable).mp (by rwa [hsym])
      have hsum_pt : ∀ a : E, g a + g (-a) = |⟪a, Δ₁⟫_ℝ| + |⟪a, Δ₂⟫_ℝ| := by
        intro a; dsimp [g]
        rw [inner_neg_left, inner_neg_left]
        rcases le_total ⟪a, Δ₁⟫_ℝ ⟪a, Δ₂⟫_ℝ with h | h
        · rw [max_eq_right h, max_eq_left (by linarith), abs_neg]; ring
        · rw [max_eq_left h, max_eq_right (by linarith), abs_neg]
      have h2 : 2 * ∫ a : E, g a ∂(stdGaussian E) =
          (‖Δ₁‖ + ‖Δ₂‖) * Real.sqrt (2 / Real.pi) := by
        calc 2 * ∫ a : E, g a ∂(stdGaussian E)
            = (∫ a : E, g a ∂(stdGaussian E)) + (∫ a : E, g (-a) ∂(stdGaussian E)) := by linarith
          _ = ∫ a : E, (g a + g (-a)) ∂(stdGaussian E) := (integral_add hg_int hg_neg_int).symm
          _ = ∫ a : E, (|⟪a, Δ₁⟫_ℝ| + |⟪a, Δ₂⟫_ℝ|) ∂(stdGaussian E) := by simp_rw [hsum_pt]
          _ = (∫ a : E, |⟪a, Δ₁⟫_ℝ| ∂(stdGaussian E)) + (∫ a : E, |⟪a, Δ₂⟫_ℝ| ∂(stdGaussian E)) :=
              integral_add (integrable_abs_inner_stdGaussian Δ₁) (integrable_abs_inner_stdGaussian Δ₂)
          _ = (‖Δ₁‖ + ‖Δ₂‖) * Real.sqrt (2 / Real.pi) := by
              rw [integral_abs_inner_stdGaussian, integral_abs_inner_stdGaussian]; ring
      have hdiv : ∫ a : E, g a ∂(stdGaussian E) = ((‖Δ₁‖ + ‖Δ₂‖) * Real.sqrt (2 / Real.pi)) / 2 := by linarith
      rw [hdiv, hsqrt_eq]
    rw [hloss_eq, hv, norm_zero, zero_add, zero_add, zero_add, sub_self, zero_div, sub_zero]
    exact ⟨le_rfl, le_rfl⟩
  · -- Non-degenerate case `v ≠ 0`: antipodal pairing + `integral_gaussian_min_wedge`!
    let L : E → ℝ := fun a => if 0 ≤ ⟪a, v⟫_ℝ then |⟪a, Δ₁⟫_ℝ| else |⟪a, Δ₂⟫_ℝ|
    have hL_meas : Measurable L :=
      Measurable.ite (measurableSet_le measurable_const (continuous_id.inner continuous_const).measurable)
        (continuous_abs.measurable.comp (continuous_id.inner continuous_const).measurable)
        (continuous_abs.measurable.comp (continuous_id.inner continuous_const).measurable)
    have hL_int : Integrable L (stdGaussian E) := by
      refine ((integrable_abs_inner_stdGaussian Δ₁).add (integrable_abs_inner_stdGaussian Δ₂)).mono'
        hL_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun a => ?_)
      have hnn : 0 ≤ L a := by dsimp [L]; split_ifs <;> exact abs_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      dsimp [L]; split_ifs <;> linarith [abs_nonneg ⟪a, Δ₁⟫_ℝ, abs_nonneg ⟪a, Δ₂⟫_ℝ]
    -- Compute `∫ L = (‖Δ₁‖ + ‖Δ₂‖) / √(2π)` via antipodal symmetry
    have hL_val : ∫ a : E, L a ∂(stdGaussian E) = (‖Δ₁‖ + ‖Δ₂‖) / Real.sqrt (2 * Real.pi) := by
      have hsym := stdGaussian_neg_invariant (E := E)
      have haesm : AEStronglyMeasurable L ((stdGaussian E).map (fun a : E => -a)) := by
        rw [hsym]; exact hL_int.aestronglyMeasurable
      have hL_neg_eq : ∫ a : E, L a ∂(stdGaussian E) = ∫ a : E, L (-a) ∂(stdGaussian E) := by
        conv_lhs => rw [← hsym]
        exact integral_map (φ := fun a : E => -a) (f := L) continuous_neg.measurable.aemeasurable haesm
      have hL_neg_int : Integrable (fun a : E => L (-a)) (stdGaussian E) :=
        (integrable_map_measure (g := L) haesm continuous_neg.measurable.aemeasurable).mp (by rwa [hsym])
      have hL_ae : (fun a : E => L a + L (-a)) =ᵐ[stdGaussian E] (fun a : E => |⟪a, Δ₁⟫_ℝ| + |⟪a, Δ₂⟫_ℝ|) := by
        have hne : ∀ᵐ a ∂(stdGaussian E), ⟪a, v⟫_ℝ ≠ 0 := by
          rw [ae_iff]
          have : {a : E | ¬ ⟪a, v⟫_ℝ ≠ 0} = {a : E | ⟪a, v⟫_ℝ = 0} := by ext a; simp
          rw [this]; exact stdGaussian_hyperplane_zero hv
        filter_upwards [hne] with a ha
        dsimp [L]
        rw [inner_neg_left, inner_neg_left, inner_neg_left, abs_neg, abs_neg]
        rcases lt_or_gt_of_ne ha with hlt | hgt
        · rw [if_neg (not_le.mpr hlt), if_pos (by linarith)]; ring
        · rw [if_pos (le_of_lt hgt), if_neg (by linarith)]
      have h2 : 2 * ∫ a : E, L a ∂(stdGaussian E) = (‖Δ₁‖ + ‖Δ₂‖) * Real.sqrt (2 / Real.pi) := by
        calc 2 * ∫ a : E, L a ∂(stdGaussian E)
            = (∫ a : E, L a ∂(stdGaussian E)) + (∫ a : E, L (-a) ∂(stdGaussian E)) := by linarith
          _ = ∫ a : E, (L a + L (-a)) ∂(stdGaussian E) := (integral_add hL_int hL_neg_int).symm
          _ = ∫ a : E, (|⟪a, Δ₁⟫_ℝ| + |⟪a, Δ₂⟫_ℝ|) ∂(stdGaussian E) := integral_congr_ae hL_ae
          _ = (∫ a : E, |⟪a, Δ₁⟫_ℝ| ∂(stdGaussian E)) + (∫ a : E, |⟪a, Δ₂⟫_ℝ| ∂(stdGaussian E)) :=
              integral_add (integrable_abs_inner_stdGaussian Δ₁) (integrable_abs_inner_stdGaussian Δ₂)
          _ = (‖Δ₁‖ + ‖Δ₂‖) * Real.sqrt (2 / Real.pi) := by
              rw [integral_abs_inner_stdGaussian, integral_abs_inner_stdGaussian]; ring
      have hdiv : ∫ a : E, L a ∂(stdGaussian E) = ((‖Δ₁‖ + ‖Δ₂‖) * Real.sqrt (2 / Real.pi)) / 2 := by linarith
      rw [hdiv, hsqrt_eq]
    -- Relate `popLossR2 - (‖Δ₁‖ + ‖Δ₂‖) / √(2π)` to `(1/2) * ∫ (R(a) + R(-a))`
    let R : E → ℝ := r2Remainder β₁s β₂s Δ₁ Δ₂
    have hR_int : Integrable R (stdGaussian E) := by
      have h1 := integrable_r2_loss β₁s β₂s (β₁s + Δ₁) (β₂s + Δ₂)
      exact h1.sub hL_int
    have hR_diff : popLossR2 β₁s β₂s ![β₁s + Δ₁, β₂s + Δ₂] - (‖Δ₁‖ + ‖Δ₂‖) / Real.sqrt (2 * Real.pi) =
        ∫ a : E, R a ∂(stdGaussian E) := by
      rw [← hL_val]
      unfold popLossR2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [← integral_sub (integrable_r2_loss β₁s β₂s (β₁s + Δ₁) (β₂s + Δ₂)) hL_int]
      rfl
    have hsym := stdGaussian_neg_invariant (E := E)
    have haesm_R : AEStronglyMeasurable R ((stdGaussian E).map (fun a : E => -a)) := by
      rw [hsym]; exact hR_int.aestronglyMeasurable
    have hR_neg_eq : ∫ a : E, R a ∂(stdGaussian E) = ∫ a : E, R (-a) ∂(stdGaussian E) := by
      conv_lhs => rw [← hsym]
      exact integral_map (φ := fun a : E => -a) (f := R) continuous_neg.measurable.aemeasurable haesm_R
    have hR_neg_int : Integrable (fun a : E => R (-a)) (stdGaussian E) :=
      (integrable_map_measure (g := R) haesm_R continuous_neg.measurable.aemeasurable).mp (by rwa [hsym])
    have hR_pair_eq : 2 * ∫ a : E, R a ∂(stdGaussian E) = ∫ a : E, (R a + R (-a)) ∂(stdGaussian E) := by
      rw [integral_add hR_int hR_neg_int]; linarith
    -- Pointwise sandwich `-2 * M(a) ≤ R(a) + R(-a) ≤ 0` for a.e. `a` (whenever `⟪a, v⟫ ≠ 0`)!
    let w : E := v + δ
    let M : E → ℝ := fun a => if ⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0 then min |⟪a, v⟫_ℝ| |⟪a, w⟫_ℝ| else 0
    have hM_meas : Measurable M :=
      Measurable.ite (measurableSet_lt
        (((continuous_id.inner continuous_const).measurable).mul ((continuous_id.inner continuous_const).measurable))
        measurable_const)
        ((continuous_abs.measurable.comp (continuous_id.inner continuous_const).measurable).min
          (continuous_abs.measurable.comp (continuous_id.inner continuous_const).measurable))
        measurable_const
    have hM_int : Integrable M (stdGaussian E) := by
      refine (integrable_abs_inner_stdGaussian v).mono' hM_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun a => ?_)
      have hnn : 0 ≤ M a := by dsimp [M]; split_ifs <;> [exact le_min (abs_nonneg _) (abs_nonneg _); exact le_rfl]
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      dsimp [M]; split_ifs <;> [exact min_le_left _ _; exact abs_nonneg _]
    have h_ae_bounds : ∀ᵐ a ∂(stdGaussian E), -2 * M a ≤ R a + R (-a) ∧ R a + R (-a) ≤ 0 := by
      have hne : ∀ᵐ a ∂(stdGaussian E), ⟪a, v⟫_ℝ ≠ 0 := by
        rw [ae_iff]
        have : {a : E | ¬ ⟪a, v⟫_ℝ ≠ 0} = {a : E | ⟪a, v⟫_ℝ = 0} := by ext a; simp
        rw [this]; exact stdGaussian_hyperplane_zero hv
      filter_upwards [hne] with a ha
      rcases lt_or_gt_of_ne ha with hv_neg | hv_pos
      · -- Case `⟪a, v⟫ < 0`
        rcases le_or_gt ⟪a, w⟫_ℝ 0 with hw_le | hw_pos
        · -- No flip: `R a = 0` and `R (-a) = 0`, `M a = 0`
          have hprod : ¬ (⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0) := not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos (le_of_lt hv_neg) hw_le)
          have hRa : R a = 0 := by
            dsimp [R, r2Remainder]
            rw [if_neg (not_le.mpr hv_neg)]
            have h1 : ⟪a, β₁s⟫_ℝ ≤ ⟪a, β₂s⟫_ℝ := by rw [inner_sub_right] at hv_neg; linarith
            have h2 : ⟪a, β₁s + Δ₁⟫_ℝ ≤ ⟪a, β₂s + Δ₂⟫_ℝ := by
              dsimp [w, v, δ] at hw_le; simp only [inner_add_right, inner_sub_right] at hw_le ⊢; linarith
            rw [max_eq_right h1, max_eq_right h2]
            have h3 : ⟪a, β₂s + Δ₂⟫_ℝ - ⟪a, β₂s⟫_ℝ = ⟪a, Δ₂⟫_ℝ := by rw [inner_add_right]; ring
            rw [h3, sub_self]
          have hRna : R (-a) = 0 := by
            dsimp [R, r2Remainder]
            have hnv : 0 ≤ ⟪-a, v⟫_ℝ := by rw [inner_neg_left]; linarith
            rw [if_pos hnv]
            have h1 : ⟪-a, β₂s⟫_ℝ ≤ ⟪-a, β₁s⟫_ℝ := by rw [inner_sub_right] at hv_neg; simp only [inner_neg_left]; linarith
            have h2 : ⟪-a, β₂s + Δ₂⟫_ℝ ≤ ⟪-a, β₁s + Δ₁⟫_ℝ := by
              dsimp [w, v, δ] at hw_le; simp only [inner_neg_left, inner_add_right, inner_sub_right] at hw_le ⊢; linarith
            rw [max_eq_left h1, max_eq_left h2]
            have h3 : ⟪-a, β₁s + Δ₁⟫_ℝ - ⟪-a, β₁s⟫_ℝ = ⟪-a, Δ₁⟫_ℝ := by rw [inner_add_right]; ring
            rw [h3, sub_self]
          dsimp [M]; rw [if_neg hprod, hRa, hRna]; norm_num
        · -- Flip in `-E_+`: apply `theorem2_antipodal_pairing` at `-a`!
          have hnv : 0 < ⟪-a, β₁s - β₂s⟫_ℝ := by rw [inner_neg_left]; linarith
          have hnw : ⟪-a, (β₁s - β₂s) + (Δ₁ - Δ₂)⟫_ℝ < 0 := by rw [inner_neg_left]; linarith
          have hp := theorem2_antipodal_pairing β₁s β₂s Δ₁ Δ₂ (-a) hnv hnw
          rw [neg_neg, add_comm (r2Remainder β₁s β₂s Δ₁ Δ₂ (-a))] at hp
          have hprod : ⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0 := mul_neg_of_neg_of_pos hv_neg hw_pos
          have hM_eq : M a = min ⟪-a, β₁s - β₂s⟫_ℝ (-⟪-a, (β₁s - β₂s) + (Δ₁ - Δ₂)⟫_ℝ) := by
            dsimp [M, w, v, δ]
            rw [if_pos hprod, inner_neg_left, inner_neg_left, abs_of_neg hv_neg, abs_of_pos hw_pos]
            congr 1; ring
          rw [hM_eq]
          exact ⟨hp.2.1, hp.2.2⟩
      · -- Case `⟪a, v⟫ > 0`
        rcases le_or_gt 0 ⟪a, w⟫_ℝ with hw_ge | hw_neg
        · -- No flip: `R a = 0` and `R (-a) = 0`, `M a = 0`
          have hprod : ¬ (⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0) := not_lt.mpr (mul_nonneg (le_of_lt hv_pos) hw_ge)
          have hRa : R a = 0 := by
            dsimp [R, r2Remainder]
            rw [if_pos (le_of_lt hv_pos)]
            have h1 : ⟪a, β₂s⟫_ℝ ≤ ⟪a, β₁s⟫_ℝ := by rw [inner_sub_right] at hv_pos; linarith
            have h2 : ⟪a, β₂s + Δ₂⟫_ℝ ≤ ⟪a, β₁s + Δ₁⟫_ℝ := by
              dsimp [w, v, δ] at hw_ge; simp only [inner_add_right, inner_sub_right] at hw_ge ⊢; linarith
            rw [max_eq_left h1, max_eq_left h2]
            have h3 : ⟪a, β₁s + Δ₁⟫_ℝ - ⟪a, β₁s⟫_ℝ = ⟪a, Δ₁⟫_ℝ := by rw [inner_add_right]; ring
            rw [h3, sub_self]
          have hRna : R (-a) = 0 := by
            dsimp [R, r2Remainder]
            have hnv : ¬ (0 ≤ ⟪-a, v⟫_ℝ) := by rw [inner_neg_left]; linarith
            rw [if_neg hnv]
            have h1 : ⟪-a, β₁s⟫_ℝ ≤ ⟪-a, β₂s⟫_ℝ := by rw [inner_sub_right] at hv_pos; simp only [inner_neg_left]; linarith
            have h2 : ⟪-a, β₁s + Δ₁⟫_ℝ ≤ ⟪-a, β₂s + Δ₂⟫_ℝ := by
              dsimp [w, v, δ] at hw_ge; simp only [inner_neg_left, inner_add_right, inner_sub_right] at hw_ge ⊢; linarith
            rw [max_eq_right h1, max_eq_right h2]
            have h3 : ⟪-a, β₂s + Δ₂⟫_ℝ - ⟪-a, β₂s⟫_ℝ = ⟪-a, Δ₂⟫_ℝ := by rw [inner_add_right]; ring
            rw [h3, sub_self]
          dsimp [M]; rw [if_neg hprod, hRa, hRna]; norm_num
        · -- Flip in `E_+`: apply `theorem2_antipodal_pairing` at `a`!
          have hp := theorem2_antipodal_pairing β₁s β₂s Δ₁ Δ₂ a hv_pos hw_neg
          have hprod : ⟪a, v⟫_ℝ * ⟪a, w⟫_ℝ < 0 := mul_neg_of_pos_of_neg hv_pos hw_neg
          have hM_eq : M a = min ⟪a, β₁s - β₂s⟫_ℝ (-⟪a, (β₁s - β₂s) + (Δ₁ - Δ₂)⟫_ℝ) := by
            dsimp [M, w, v, δ]
            rw [if_pos hprod, abs_of_pos hv_pos, abs_of_neg hw_neg]
          rw [hM_eq]
          exact ⟨hp.2.1, hp.2.2⟩
    -- Integrate the a.e. sandwich `-2 M ≤ R + R(-·) ≤ 0` and apply `integral_gaussian_min_wedge`!
    have hlo : -2 * ∫ a : E, M a ∂(stdGaussian E) ≤ ∫ a : E, (R a + R (-a)) ∂(stdGaussian E) := by
      rw [← integral_const_mul]
      exact integral_mono_ae (hM_int.const_mul (-2)) (hR_int.add hR_neg_int) (h_ae_bounds.mono fun _ h => h.1)
    have hhi : ∫ a : E, (R a + R (-a)) ∂(stdGaussian E) ≤ 0 := by
      have := integral_mono_ae (hR_int.add hR_neg_int) (integrable_const (0 : ℝ)) (h_ae_bounds.mono fun _ h => h.2)
      simpa using this
    have hM_val : ∫ a : E, M a ∂(stdGaussian E) = (‖v‖ + ‖v + δ‖ - ‖v + (v + δ)‖) / Real.sqrt (2 * Real.pi) :=
      integral_gaussian_min_wedge v w
    rw [hM_val, ← hR_pair_eq] at hlo
    rw [← hR_pair_eq] at hhi
    constructor <;> linarith

/-- **THEOREM 2 (Unconditional Global Scale-Free Sharpness — Zero `h_rem` Hypothesis!)**:
For ANY finite-dimensional real inner product space `E` (including `d = 1`), ANY `β₁s β₂s : E`
(including `β₁s = β₂s`), and ANY `b₁ b₂ : E`:
`((√2 - 1) / √π) * dist((b₁, b₂), {(β₁*, β₂*), (β₂*, β₁*)}) ≤ popLossR2 β₁s β₂s ![b₁, b₂]`.
Zero hypotheses beyond finite-dimensionality of `E`! -/
theorem theorem2_unconditional_global_sharpness (β₁s β₂s b₁ b₂ : E) :
    let d_id := Real.sqrt (‖b₁ - β₁s‖ ^ 2 + ‖b₂ - β₂s‖ ^ 2)
    let d_sw := Real.sqrt (‖b₁ - β₂s‖ ^ 2 + ‖b₂ - β₁s‖ ^ 2)
    ((Real.sqrt 2 - 1) / Real.sqrt Real.pi) * min d_id d_sw ≤
      popLossR2 β₁s β₂s ![b₁, b₂] :=
  theorem2_global_sharpness_from_remainder (popLossR2 β₁s β₂s) β₁s β₂s
    (popLossR2_swap β₁s β₂s)
    (fun Δ₁ Δ₂ => sub_le_comm.mp (theorem2_gaussian_remainder_bounds β₁s β₂s Δ₁ Δ₂).1)
    b₁ b₂

/-! ### Phase III Unconditional Axiom Audits (Priority 2: Theorem 2) -/
#print axioms popLossR2_swap
#print axioms integral_gaussian_min_wedge
#print axioms theorem2_gaussian_remainder_bounds
#print axioms theorem2_unconditional_global_sharpness

end Research107
