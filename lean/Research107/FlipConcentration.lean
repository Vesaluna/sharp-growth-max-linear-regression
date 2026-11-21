import Research107.GaussianModel
import Research107.Concentration
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators InnerProductSpace ENNReal NNReal Classical

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Stage 4.1: 2D Standard Gaussian Polar Integration & Exact Radial Moments -/

/-- Exact 2D standard Gaussian integral in polar coordinates:
for any integrable `f : ℝ × ℝ → ℝ` under `N(0,1) × N(0,1)`,
`∫ z, f z ∂(N(0,1) × N(0,1)) = (2π)⁻¹ * ∫ p in polarCoord.target, (p.1 * exp (-p.1^2 / 2)) * f (polarCoord.symm p)`. -/
theorem integral_stdGaussian2D_polar {f : ℝ × ℝ → ℝ}
    (hf : Integrable f ((gaussianReal 0 1).prod (gaussianReal 0 1))) :
    ∫ z : ℝ × ℝ, f z ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      (2 * Real.pi)⁻¹ *
        ∫ p in polarCoord.target,
          (p.1 * Real.exp (-p.1 ^ 2 / 2)) * f (polarCoord.symm p) := by
  -- Step 1: Rewrite product Gaussian integral as Lebesgue integral on `ℝ × ℝ`
  have h1 : ∫ z : ℝ × ℝ, f z ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
      ∫ z : ℝ × ℝ, ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)) * f z := by
    rw [integral_prod f hf]
    have hinner : ∀ x : ℝ, ∫ y : ℝ, f (x, y) ∂(gaussianReal 0 1) =
        ∫ y : ℝ, gaussianPDFReal 0 1 y * f (x, y) := by
      intro x
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
      rfl
    simp_rw [hinner]
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    simp_rw [smul_eq_mul, ← integral_const_mul]
    have hpdf_prod : ∀ x y : ℝ,
        gaussianPDFReal 0 1 x * (gaussianPDFReal 0 1 y * f (x, y)) =
        ((2 * Real.pi)⁻¹ * Real.exp (-(x ^ 2 + y ^ 2) / 2)) * f (x, y) := by
      intro x y
      rw [gaussianPDFReal_std, gaussianPDFReal_std]
      have hsq : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
      calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) * f (x, y))
          = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
            (Real.exp (-x ^ 2 / 2) * Real.exp (-y ^ 2 / 2)) * f (x, y) := by ring
        _ = (2 * Real.pi)⁻¹ * Real.exp (-(x ^ 2 + y ^ 2) / 2) * f (x, y) := by
            rw [hsq, ← Real.exp_add]; congr 3; ring
    simp_rw [hpdf_prod]
    -- Apply Fubini (`integral_prod`) in reverse on Lebesgue measure `volume.prod volume = volume`
    have hint_leb : Integrable
        (fun z : ℝ × ℝ => ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)) * f z) := by
      -- Prove integrability via `Measure.prod_withDensity` / direct equivalence with `hf`
      have hmeas_g : Measurable (fun z : ℝ × ℝ => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) :=
        ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
          ((measurable_gaussianPDF 0 1).comp measurable_snd)
      have hprod_eq : (gaussianReal 0 1).prod (gaussianReal 0 1) =
          (volume : Measure (ℝ × ℝ)).withDensity (fun z : ℝ × ℝ => gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2) := by
        rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
        have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) := rfl
        rw [hvol, prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
      rw [hprod_eq, integrable_withDensity_iff hmeas_g
            (Filter.Eventually.of_forall fun z => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top)] at hf
      have heq : (fun z : ℝ × ℝ => ((2 * Real.pi)⁻¹ * Real.exp (-(z.1 ^ 2 + z.2 ^ 2) / 2)) * f z) =
          (fun z : ℝ × ℝ => f z * (gaussianPDF 0 1 z.1 * gaussianPDF 0 1 z.2).toReal) := by
        ext ⟨x, y⟩
        rw [ENNReal.toReal_mul, toReal_gaussianPDF, toReal_gaussianPDF, mul_comm (f (x, y))]
        have := hpdf_prod x y
        linarith [show gaussianPDFReal 0 1 x * (gaussianPDFReal 0 1 y * f (x, y)) =
            gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 y * f (x, y) by ring]
      rwa [heq]
    exact (integral_prod _ hint_leb).symm
  -- Step 2: Change of variables to polar coordinates via `integral_comp_polarCoord_symm`
  rw [h1]
  simp_rw [mul_assoc]
  rw [integral_const_mul, ← integral_comp_polarCoord_symm]
  congr 1
  refine setIntegral_congr_fun polarCoord.open_target.measurableSet (fun p _ => ?_)
  simp only [polarCoord_symm_apply, smul_eq_mul]
  have hsq : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
    have hsc := Real.cos_sq_add_sin_sq p.2
    nlinarith
  rw [hsq]

/-- Integrability of `r^k * exp (-r^2 / 2)` on `(0, ∞)` for every `k : ℕ`. -/
lemma integrableOn_pow_mul_exp_neg_sq_div_two (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * Real.exp (-r ^ 2 / 2)) (Set.Ioi 0) := by
  -- Dominate `r^k * exp (-r^2 / 2) ≤ C_k * exp (-r^2 / 4)` using `r^k ≤ k! * 2^k * exp (r^2 / 4)`?
  -- Even cleaner: `r ≤ 1 + r^2 / 4` isn't enough for arbitrary `k`, use `r^2 / (4k) ≤ exp (r^2 / (4k))`!
  -- Wait: for `k = 0`, `exp (-r^2 / 2)` is directly `integrable_exp_neg_mul_sq`.
  -- For `k ≥ 1`, `r^2 ≤ 4 * k * exp (r^2 / (4 * k))` (by `add_one_le_exp`), so
  -- `(r^2)^k ≤ (4k)^k * exp (r^2 / 4)`, hence `r^k ≤ 1 + r^(2k) ≤ (1 + (4k)^k) * exp (r^2 / 4)`!!
  have hdom : IntegrableOn (fun r : ℝ => (1 + (4 * ((k : ℝ) + 1)) ^ k) * Real.exp (-(1 / 4 : ℝ) * r ^ 2))
      (Set.Ioi 0) :=
    ((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul _).integrableOn
  refine hdom.mono' (by fun_prop) ((ae_restrict_mem measurableSet_Ioi).mono fun r hr => ?_)
  have hr0 : 0 ≤ r := le_of_lt hr
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hr0 k) (le_of_lt (Real.exp_pos _)))]
  have hbound_rk : r ^ k ≤ (1 + (4 * ((k : ℝ) + 1)) ^ k) * Real.exp (r ^ 2 / 4) := by
    have hk1 : (0 : ℝ) < 4 * ((k : ℝ) + 1) := by positivity
    have h1 : r ^ 2 / (4 * ((k : ℝ) + 1)) ≤ Real.exp (r ^ 2 / (4 * ((k : ℝ) + 1))) := by
      linarith [Real.add_one_le_exp (r ^ 2 / (4 * ((k : ℝ) + 1)))]
    have h2 : r ^ 2 ≤ (4 * ((k : ℝ) + 1)) * Real.exp (r ^ 2 / (4 * ((k : ℝ) + 1))) := by
      rwa [div_le_iff₀ hk1, mul_comm] at h1
    have h3 : (r ^ 2) ^ k ≤ ((4 * ((k : ℝ) + 1)) * Real.exp (r ^ 2 / (4 * ((k : ℝ) + 1)))) ^ k :=
      pow_le_pow_left₀ (sq_nonneg r) h2 k
    rw [mul_pow, ← Real.exp_nat_mul] at h3
    have hexp_le : Real.exp ((k : ℝ) * (r ^ 2 / (4 * ((k : ℝ) + 1)))) ≤ Real.exp (r ^ 2 / 4) := by
      refine Real.exp_le_exp.mpr ?_
      have hfrac : (k : ℝ) / (4 * ((k : ℝ) + 1)) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ hk1 (by norm_num : (0 : ℝ) < 4)]
        linarith
      have hrew : (k : ℝ) * (r ^ 2 / (4 * ((k : ℝ) + 1))) = ((k : ℝ) / (4 * ((k : ℝ) + 1))) * r ^ 2 := by ring
      rw [hrew]
      nlinarith [sq_nonneg r]
    have h3' : r ^ (2 * k) ≤ (4 * ((k : ℝ) + 1)) ^ k * Real.exp (r ^ 2 / 4) := by
      rw [pow_mul]
      exact le_trans h3 (mul_le_mul_of_nonneg_left hexp_le (by positivity))
    have h4 : r ^ k ≤ 1 + r ^ (2 * k) := by
      rcases le_or_gt r 1 with hr1 | hr1
      · have : r ^ k ≤ 1 := pow_le_one₀ hr0 hr1
        linarith [pow_nonneg hr0 (2 * k)]
      · have : r ^ k ≤ r ^ (2 * k) := pow_le_pow_right₀ (le_of_lt hr1) (by omega)
        linarith
    have h1_le_exp : 1 ≤ Real.exp (r ^ 2 / 4) := Real.one_le_exp (by positivity)
    nlinarith
  calc r ^ k * Real.exp (-r ^ 2 / 2)
      ≤ ((1 + (4 * ((k : ℝ) + 1)) ^ k) * Real.exp (r ^ 2 / 4)) * Real.exp (-r ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hbound_rk (le_of_lt (Real.exp_pos _))
    _ = (1 + (4 * ((k : ℝ) + 1)) ^ k) * Real.exp (-(1 / 4 : ℝ) * r ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Helper: `r^k * exp (-r^2 / 2) → 0` as `r → +∞` for every `k : ℕ`. -/
private lemma tendsto_pow_mul_exp_neg_sq_div_two_atTop (k : ℕ) :
    Filter.Tendsto (fun r : ℝ => -(r ^ k * Real.exp (-r ^ 2 / 2))) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun r : ℝ => r ^ k * Real.exp (-r ^ 2 / 2)) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun r : ℝ => r ^ 2 / 2) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.mpr (fun b => ?_)
      refine Filter.eventually_atTop.mpr ⟨max 1 (2 * max 0 b), fun r hr => ?_⟩
      have hr1 : 1 ≤ r := le_trans (le_max_left _ _) hr
      have hr2 : 2 * max 0 b ≤ r := le_trans (le_max_right _ _) hr
      have : r ≤ r ^ 2 := by nlinarith
      linarith [le_max_right 0 b]
    have hexp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp hsq
    have hlim : Filter.Tendsto (fun r : ℝ => (2 : ℝ) ^ k * (((fun x : ℝ => x ^ k * Real.exp (-x)) ∘ (fun r => r ^ 2 / 2)) r))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ) ^ k)).mul hexp
    refine squeeze_zero_norm' (Filter.eventually_atTop.mpr ⟨2, fun r hr => ?_⟩) hlim
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (by linarith) k) (le_of_lt (Real.exp_pos _)))]
    have hle : r ≤ r ^ 2 / 2 := by nlinarith
    have hpow : r ^ k ≤ (r ^ 2 / 2) ^ k := pow_le_pow_left₀ (by linarith) hle k
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    simp only [Function.comp_apply, neg_div]
    calc r ^ k * Real.exp (-(r ^ 2 / 2))
        ≤ (r ^ 2 / 2) ^ k * Real.exp (-(r ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right hpow (le_of_lt (Real.exp_pos _))
      _ ≤ (2 : ℝ) ^ k * ((r ^ 2 / 2) ^ k * Real.exp (-(r ^ 2 / 2))) :=
          le_mul_of_one_le_left (mul_nonneg (by positivity) (le_of_lt (Real.exp_pos _))) h2
  simpa using h1.neg

/-- **Exact Radial Gaussian Moments**:
For every `p : ℕ`, `∫ r in Ioi 0, r^(p+1) * exp (-r^2 / 2) = 2^(p/2) * Γ(1 + p/2)`.
In particular:
- `p = 0`: `∫_0^∞ r e^{-r^2/2} dr = 1`
- `p = 1`: `∫_0^∞ r^2 e^{-r^2/2} dr = √(π / 2)` (also used in Theorem 2!). -/
theorem integral_pow_mul_exp_neg_sq_div_two : ∀ p : ℕ,
    ∫ r in Set.Ioi (0 : ℝ), r ^ (p + 1) * Real.exp (-r ^ 2 / 2) =
      (2 : ℝ) ^ ((p : ℝ) / 2) * Real.Gamma (1 + (p : ℝ) / 2) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    match p with
    | 0 =>
      -- `∫_0^∞ r exp (-r^2 / 2) = 1 = 2^0 * Γ(1)`
      have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
          HasDerivAt (fun r : ℝ => -(r ^ 0 * Real.exp (-r ^ 2 / 2)))
            (x ^ 1 * Real.exp (-x ^ 2 / 2)) x := by
        intro x _
        have h1 : HasDerivAt (fun r : ℝ => -r ^ 2 / 2) (-x) x := by
          convert ((hasDerivAt_pow 2 x).neg.div_const (2 : ℝ)) using 1; ring
        have h2 : HasDerivAt (fun r : ℝ => -Real.exp (-r ^ 2 / 2)) (x * Real.exp (-x ^ 2 / 2)) x := by
          convert (h1.exp).fun_neg using 1; ring
        simpa [pow_zero, pow_one, one_mul] using h2
      have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
        (integrableOn_pow_mul_exp_neg_sq_div_two 1)
        (tendsto_pow_mul_exp_neg_sq_div_two_atTop 0)
      simp only [pow_zero, one_mul, zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div,
        Real.exp_zero, sub_neg_eq_add, zero_add, Nat.cast_zero, Real.rpow_zero, add_zero,
        Real.Gamma_one] at hftc ⊢
      exact hftc
    | 1 =>
      -- `∫_0^∞ r^2 exp (-r^2 / 2) = ∫_0^∞ exp (-r^2 / 2) = √(π / 2) = 2^(1/2) * Γ(3/2)`
      have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
          HasDerivAt (fun r : ℝ => -(r ^ 1 * Real.exp (-r ^ 2 / 2)))
            (x ^ 2 * Real.exp (-x ^ 2 / 2) - x ^ 0 * Real.exp (-x ^ 2 / 2)) x := by
        intro x _
        have h1 : HasDerivAt (fun r : ℝ => -r ^ 2 / 2) (-x) x := by
          convert ((hasDerivAt_pow 2 x).neg.div_const (2 : ℝ)) using 1; ring
        have hmul := (hasDerivAt_id x).mul h1.exp
        convert hmul.fun_neg using 1
        · ext r; simp
        · simp only [pow_zero, one_mul, id_eq]; ring
      have hint_diff : IntegrableOn (fun r : ℝ => r ^ 2 * Real.exp (-r ^ 2 / 2) - r ^ 0 * Real.exp (-r ^ 2 / 2))
          (Set.Ioi 0) :=
        (integrableOn_pow_mul_exp_neg_sq_div_two 2).sub (integrableOn_pow_mul_exp_neg_sq_div_two 0)
      have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_diff
        (tendsto_pow_mul_exp_neg_sq_div_two_atTop 1)
      simp only [pow_one, zero_mul, neg_zero, sub_self] at hftc
      rw [integral_sub (integrableOn_pow_mul_exp_neg_sq_div_two 2)
          (integrableOn_pow_mul_exp_neg_sq_div_two 0)] at hftc
      have h0 : ∫ r in Set.Ioi (0 : ℝ), r ^ 0 * Real.exp (-r ^ 2 / 2) = Real.sqrt (Real.pi / 2) := by
        have h1 : (fun r : ℝ => r ^ 0 * Real.exp (-r ^ 2 / 2)) =
            (fun r : ℝ => Real.exp (-(1 / 2 : ℝ) * r ^ 2)) := by
          ext r; simp only [pow_zero, one_mul]; congr 1; ring
        rw [h1, integral_gaussian_Ioi (1 / 2 : ℝ)]
        have hdiv : Real.pi / (1 / 2 : ℝ) = 2 * Real.pi := by ring
        rw [hdiv, Real.sqrt_div (le_of_lt Real.pi_pos), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
        have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
        field_simp [hs2]
        nlinarith [hsq2]
      have hval : ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * Real.exp (-r ^ 2 / 2) = Real.sqrt (Real.pi / 2) := by
        linarith
      rw [hval]
      have harg : (1 : ℝ) + ((1 : ℕ) : ℝ) / 2 = (1 / 2 : ℝ) + 1 := by norm_num
      rw [harg, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
      simp only [Nat.cast_one]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_div (le_of_lt Real.pi_pos)]
      have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      field_simp [hs2]
      nlinarith [hsq2]
    | n + 2 =>
      -- Step `n → n + 2` via `d/dr (-r^(n+2) exp (-r^2/2)) = r^(n+3) exp(-r^2/2) - (n+2) r^(n+1) exp(-r^2/2)`
      have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
          HasDerivAt (fun r : ℝ => -(r ^ (n + 2) * Real.exp (-r ^ 2 / 2)))
            (x ^ (n + 3) * Real.exp (-x ^ 2 / 2) - ((n + 2 : ℕ) : ℝ) * (x ^ (n + 1) * Real.exp (-x ^ 2 / 2))) x := by
        intro x _
        have h1 : HasDerivAt (fun r : ℝ => -r ^ 2 / 2) (-x) x := by
          convert ((hasDerivAt_pow 2 x).neg.div_const (2 : ℝ)) using 1; ring
        have hmul := (hasDerivAt_pow (n + 2) x).mul h1.exp
        convert hmul.fun_neg using 1
        have hpow : x ^ (n + 3) = x ^ (n + 2) * x := by rw [pow_succ]
        have hsub : n + 2 - 1 = n + 1 := by omega
        rw [hpow, hsub]
        ring
      have hint_diff : IntegrableOn
          (fun r : ℝ => r ^ (n + 3) * Real.exp (-r ^ 2 / 2) - ((n + 2 : ℕ) : ℝ) * (r ^ (n + 1) * Real.exp (-r ^ 2 / 2)))
          (Set.Ioi 0) :=
        (integrableOn_pow_mul_exp_neg_sq_div_two (n + 3)).sub
          ((integrableOn_pow_mul_exp_neg_sq_div_two (n + 1)).const_mul _)
      have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_diff
        (tendsto_pow_mul_exp_neg_sq_div_two_atTop (n + 2))
      simp only [zero_pow (by omega : n + 2 ≠ 0), zero_mul, neg_zero, sub_self] at hftc
      rw [integral_sub (integrableOn_pow_mul_exp_neg_sq_div_two (n + 3))
          ((integrableOn_pow_mul_exp_neg_sq_div_two (n + 1)).const_mul _),
          integral_const_mul] at hftc
      have hprev := ih n (by omega)
      rw [hprev] at hftc
      have hrec : ∫ r in Set.Ioi (0 : ℝ), r ^ (n + 3) * Real.exp (-r ^ 2 / 2) =
          ((n + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ ((n : ℝ) / 2) * Real.Gamma (1 + (n : ℝ) / 2)) := by
        linarith
      rw [hrec]
      have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
      have harg1 : ((n + 2 : ℕ) : ℝ) / 2 = (n : ℝ) / 2 + 1 := by rw [hcast]; ring
      rw [harg1, show (1 : ℝ) + ((n : ℝ) / 2 + 1) = (1 + (n : ℝ) / 2) + 1 by ring,
          Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
          Real.Gamma_add_one (by positivity : (1 : ℝ) + (n : ℝ) / 2 ≠ 0), hcast]
      ring

/-! ### Stage 4.2: Angular Wedge Measure & Exact Moments of the 2D Surrogate `W(z)` -/

/-- Exact angular integral: for `0 < η ≤ 1 / 4`,
`∫ θ in Ioo (-π) π, (if |cos θ| < 2 η then (1 : ℝ) else 0) = 4 * arcsin (2 η)`. -/
lemma integral_indicator_abs_cos_lt {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, (if |Real.cos θ| < 2 * η then (1 : ℝ) else 0) =
      4 * Real.arcsin (2 * η) := by
  set α := Real.arcsin (2 * η)
  have h2η_pos : 0 < 2 * η := by linarith
  have h2η_le : 2 * η ≤ 1 / 2 := by linarith
  have hsin_α : Real.sin α = 2 * η := Real.sin_arcsin (by linarith) (by linarith)
  have hα_pos : 0 < α := by
    have h0 : Real.arcsin 0 < Real.arcsin (2 * η) :=
      Real.strictMonoOn_arcsin ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩ h2η_pos
    rwa [Real.arcsin_zero] at h0
  have hα_le : α ≤ Real.pi / 6 := by
    calc α = Real.arcsin (2 * η) := rfl
      _ ≤ Real.arcsin (1 / 2) := Real.arcsin_le_arcsin h2η_le
      _ = Real.pi / 6 := by rw [← Real.sin_pi_div_six, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
  let I₁ : Set ℝ := Set.Ioo (-(Real.pi / 2) - α) (-(Real.pi / 2) + α)
  let I₂ : Set ℝ := Set.Ioo (Real.pi / 2 - α) (Real.pi / 2 + α)
  -- Show `{θ ∈ Ioo (-π) π | |cos θ| < 2η} = I₁ ∪ I₂`
  have hset_eq : {θ : ℝ | θ ∈ Set.Ioo (-Real.pi) Real.pi ∧ |Real.cos θ| < 2 * η} = I₁ ∪ I₂ := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioo, I₁, I₂]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hcos⟩
      rcases lt_trichotomy θ 0 with hneg | rfl | hpos
      · left
        have h1 : Real.sin (Real.pi / 2 + θ) = Real.cos θ := by
          rw [add_comm, Real.sin_add_pi_div_two]
        rw [← h1, abs_lt, ← hsin_α, ← Real.sin_neg] at hcos
        have hmem_t : Real.pi / 2 + θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
        have hmem_α : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hmem_nα : -α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hgt : -α < Real.pi / 2 + θ := (Real.strictMonoOn_sin.lt_iff_lt hmem_nα hmem_t).mp hcos.1
        have hlt : Real.pi / 2 + θ < α := (Real.strictMonoOn_sin.lt_iff_lt hmem_t hmem_α).mp hcos.2
        constructor <;> linarith
      · rw [Real.cos_zero, abs_one] at hcos; linarith
      · right
        have h1 : Real.sin (Real.pi / 2 - θ) = Real.cos θ := Real.sin_pi_div_two_sub θ
        rw [← h1, abs_lt, ← hsin_α, ← Real.sin_neg] at hcos
        have hmem_t : Real.pi / 2 - θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
        have hmem_α : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hmem_nα : -α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hgt : -α < Real.pi / 2 - θ := (Real.strictMonoOn_sin.lt_iff_lt hmem_nα hmem_t).mp hcos.1
        have hlt : Real.pi / 2 - θ < α := (Real.strictMonoOn_sin.lt_iff_lt hmem_t hmem_α).mp hcos.2
        constructor <;> linarith
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · refine ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, ?_⟩
        have hrew : Real.cos θ = Real.sin (Real.pi / 2 + θ) := by rw [add_comm, Real.sin_add_pi_div_two]
        rw [hrew, abs_lt, ← hsin_α, ← Real.sin_neg]
        have hmem_t : Real.pi / 2 + θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hmem_α : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hmem_nα : -α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        exact ⟨Real.strictMonoOn_sin hmem_nα hmem_t (by linarith),
               Real.strictMonoOn_sin hmem_t hmem_α (by linarith)⟩
      · refine ⟨⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩, ?_⟩
        have hrew : Real.cos θ = Real.sin (Real.pi / 2 - θ) := (Real.sin_pi_div_two_sub θ).symm
        rw [hrew, abs_lt, ← hsin_α, ← Real.sin_neg]
        have hmem_t : Real.pi / 2 - θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hmem_α : α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        have hmem_nα : -α ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
        exact ⟨Real.strictMonoOn_sin hmem_nα hmem_t (by linarith),
               Real.strictMonoOn_sin hmem_t hmem_α (by linarith)⟩
  -- Rewrite the set integral as the indicator integral over `I₁ ∪ I₂`
  have hrew_ind : ∫ θ in Set.Ioo (-Real.pi) Real.pi, (if |Real.cos θ| < 2 * η then (1 : ℝ) else 0) =
      ∫ θ : ℝ, (I₁ ∪ I₂).indicator (fun _ => (1 : ℝ)) θ := by
    rw [← integral_indicator measurableSet_Ioo]
    congr 1; ext θ
    by_cases h : θ ∈ Set.Ioo (-Real.pi) Real.pi ∧ |Real.cos θ| < 2 * η
    · have hmem : θ ∈ I₁ ∪ I₂ := by rw [← hset_eq]; exact h
      simp [Set.indicator_of_mem h.1, Set.indicator_of_mem hmem, h.2]
    · have hnmem : θ ∉ I₁ ∪ I₂ := by rw [← hset_eq]; exact h
      by_cases h1 : θ ∈ Set.Ioo (-Real.pi) Real.pi
      · have h2 : ¬ |Real.cos θ| < 2 * η := fun hc => h ⟨h1, hc⟩
        simp [Set.indicator_of_mem h1, Set.indicator_of_notMem hnmem, h2]
      · simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem hnmem]
  rw [hrew_ind, integral_indicator (measurableSet_Ioo.union measurableSet_Ioo), setIntegral_const, smul_eq_mul, mul_one]
  have hdisj : Disjoint I₁ I₂ := by
    rw [Set.disjoint_left]
    intro θ h1 h2
    simp only [I₁, I₂, Set.mem_Ioo] at h1 h2
    linarith [Real.pi_pos]
  rw [measureReal_def, measure_union hdisj measurableSet_Ioo, Real.volume_Ioo, Real.volume_Ioo,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
  ring

/-- **Exact 2D Gaussian Moments of the Scale-Free Surrogate `phiEta`**:
For `0 < η ≤ 1 / 4`, any unit vectors `vhat, u : E` (`‖vhat‖ = 1`, `‖u‖ = 1`), and `X a = phiEta η ⟪a, vhat⟫ ⟪a, u⟫`:
1. `X` is `p`-th power integrable for every `p : ℕ`;
2. `∫ a, X a ∂(stdGaussian E) ≤ (4 * √(2π) / 3) * η`;
3. For every `p ≥ 2`, `∫ a, (X a)^p ∂(stdGaussian E) ≤ (4 / 3 * η) * (p! * 2^p)`. -/
theorem lemma43_gaussian_moments
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    {vhat u : E} (hv : ‖vhat‖ = 1) (hu : ‖u‖ = 1) :
    let X : E → ℝ := fun a => phiEta η ⟪a, vhat⟫_ℝ ⟪a, u⟫_ℝ
    (∀ p : ℕ, Integrable (fun a => (X a) ^ p) (stdGaussian E)) ∧
    (∫ a, X a ∂(stdGaussian E) ≤ (4 * Real.sqrt (2 * Real.pi) / 3) * η) ∧
    (∀ p : ℕ, 2 ≤ p →
      ∫ a, (X a) ^ p ∂(stdGaussian E) ≤ (4 / 3 * η) * ((Nat.factorial p : ℝ) * (2 : ℝ) ^ p)) := by
  intro X
  have hX_nn : ∀ a : E, 0 ≤ X a := fun a => le_max_left _ _
  have hX_meas : Measurable X := by
    unfold X phiEta
    have h1 : Measurable (fun a : E => ⟪a, vhat⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    have h2 : Measurable (fun a : E => ⟪a, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    exact measurable_const.max (((continuous_abs.measurable.comp h2).const_mul 2).sub
      ((continuous_abs.measurable.comp h1).div_const η))
  -- Gram-Schmidt decomposition `u = c • vhat + w` with `⟪vhat, w⟫ = 0`
  set c : ℝ := ⟪vhat, u⟫_ℝ
  set w : E := u - c • vhat
  have hw_orth : ⟪vhat, w⟫_ℝ = 0 := by
    dsimp [w, c]
    rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hv]
    ring
  by_cases hw : w = 0
  · -- Collinear case `u = c • vhat` with `|c| = 1`: `X ≡ 0` identically!
    have hu_eq : u = c • vhat := sub_eq_zero.mp hw
    have hc_abs : |c| = 1 := by
      have h1 : ‖u‖ = |c| * ‖vhat‖ := by rw [hu_eq, norm_smul, Real.norm_eq_abs]
      rw [hu, hv, mul_one] at h1
      exact h1.symm
    have hX_zero : ∀ a : E, X a = 0 := by
      intro a
      dsimp [X, phiEta]
      rw [hu_eq, real_inner_smul_right, abs_mul, hc_abs, one_mul]
      apply max_eq_left
      have h1 : 2 * |⟪a, vhat⟫_ℝ| ≤ |⟪a, vhat⟫_ℝ| / η := by
        rw [le_div_iff₀ hη0]
        nlinarith [abs_nonneg ⟪a, vhat⟫_ℝ]
      linarith
    refine ⟨fun p => ?_, ?_, fun p hp => ?_⟩
    · have h0 : (fun a : E => (X a) ^ p) = fun _ => (0 : ℝ) ^ p := by ext a; rw [hX_zero a]
      rw [h0]; exact integrable_const _
    · simp only [hX_zero, integral_zero]; positivity
    · have h0 : (fun a : E => (X a) ^ p) = fun _ => (0 : ℝ) := by
        ext a; rw [hX_zero a, zero_pow (by omega)]
      rw [h0, integral_zero]; positivity
  · -- Non-collinear case: orthonormal pair `e₁ = vhat`, `e₂ = (‖w‖⁻¹) • w`
    have hw_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    set e₂ : E := (‖w‖⁻¹) • w
    have he₂_norm : ‖e₂‖ = 1 := by
      dsimp [e₂]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw_pos), inv_mul_cancel₀ (ne_of_gt hw_pos)]
    have he_orth : ⟪vhat, e₂⟫_ℝ = 0 := by
      dsimp [e₂]; rw [real_inner_smul_right, hw_orth, mul_zero]
    have hcw_sq : c ^ 2 + ‖w‖ ^ 2 = 1 := by
      have hu_decomp : u = c • vhat + w := by dsimp [w]; abel
      have hsq : ‖u‖ ^ 2 = ‖c • vhat‖ ^ 2 + 2 * ⟪c • vhat, w⟫_ℝ + ‖w‖ ^ 2 := by
        conv_lhs => rw [hu_decomp]
        exact norm_add_sq_real _ _
      rw [hu, norm_smul, Real.norm_eq_abs, hv, mul_one, sq_abs, real_inner_smul_left, hw_orth] at hsq
      linarith
    -- Pointwise domination `X a ≤ W (⟪a, vhat⟫, ⟪a, e₂⟫)` where `W(z) = if |z₁| < 2η‖z‖ then 2‖z‖ else 0`
    let W : ℝ × ℝ → ℝ := fun z =>
      if |z.1| < 2 * η * Real.sqrt (z.1 ^ 2 + z.2 ^ 2) then 2 * Real.sqrt (z.1 ^ 2 + z.2 ^ 2) else 0
    have hW_nn : ∀ z : ℝ × ℝ, 0 ≤ W z := by
      intro z; dsimp [W]; split_ifs <;> positivity
    have hW_meas : Measurable W := by
      dsimp [W]
      have hR : Measurable (fun z : ℝ × ℝ => Real.sqrt (z.1 ^ 2 + z.2 ^ 2)) := by fun_prop
      have hS : MeasurableSet {z : ℝ × ℝ | |z.1| < 2 * η * Real.sqrt (z.1 ^ 2 + z.2 ^ 2)} :=
        measurableSet_lt (by fun_prop) (hR.const_mul (2 * η))
      exact Measurable.ite hS (hR.const_mul 2) measurable_const
    have hX_le_W : ∀ a : E, X a ≤ W (⟪a, vhat⟫_ℝ, ⟪a, e₂⟫_ℝ) := by
      intro a
      have hcs : |⟪a, u⟫_ℝ| ≤ Real.sqrt (⟪a, vhat⟫_ℝ ^ 2 + ⟪a, e₂⟫_ℝ ^ 2) := by
        have hu_decomp : u = c • vhat + ‖w‖ • e₂ := by
          dsimp [e₂, w]; rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hw_pos), one_smul]; abel
        have hinner : ⟪a, u⟫_ℝ = c * ⟪a, vhat⟫_ℝ + ‖w‖ * ⟪a, e₂⟫_ℝ := by
          conv_lhs => rw [hu_decomp]
          rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
        rw [hinner, Real.le_sqrt (abs_nonneg _) (by positivity), sq_abs]
        nlinarith [sq_nonneg (c * ⟪a, e₂⟫_ℝ - ‖w‖ * ⟪a, vhat⟫_ℝ), hcw_sq]
      have h1 := lemma43_phiEta_upper_dom hη0 ⟪a, vhat⟫_ℝ ⟪a, u⟫_ℝ
      refine le_trans h1 ?_
      dsimp [W]
      split_ifs with hlt1 hlt2
      · linarith
      · exfalso; apply hlt2; nlinarith
      · positivity
      · exact le_rfl
    -- Compute exact moments of `W^p` under `N(0,1) × N(0,1)` for every `p ≥ 1`
    have hW_int : ∀ p : ℕ, Integrable (fun z : ℝ × ℝ => (W z) ^ p) ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      intro p
      -- `0 ≤ (W z)^p ≤ (2 √(z₁^2 + z₂^2))^p ≤ 2^p * (2 * (|z₁| + |z₂|))^p`? Even simpler:
      -- `(W z)^p ≤ 2^p * (|z₁| + |z₂|)^p ≤ 4^p * (|z₁|^p + |z₂|^p)`, integrable since `gaussianReal` has all Lp moments!
      have h_memLp : ∀ k : ℕ, Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 1) := by
        intro k
        have hmp := memLp_id_gaussianReal (μ := 0) (v := 1) (k : ℝ≥0)
        rcases eq_or_ne k 0 with rfl | hk0
        · simp
        · have := hmp.integrable_norm_rpow (by exact_mod_cast hk0) (by simp)
          simpa [Real.norm_eq_abs, Real.rpow_natCast] using this
      have hdom : Integrable (fun z : ℝ × ℝ => (4 : ℝ) ^ p * (|z.1| ^ p + |z.2| ^ p))
          ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
        have h1 : Integrable (fun z : ℝ × ℝ => |z.1| ^ p) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
          (h_memLp p).comp_fst (gaussianReal 0 1)
        have h2 : Integrable (fun z : ℝ × ℝ => |z.2| ^ p) ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
          (h_memLp p).comp_snd (gaussianReal 0 1)
        exact (h1.add h2).const_mul _
      refine hdom.mono' (hW_meas.pow_const p).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hW_nn z) p)]
      have hW_le : W z ≤ 2 * (|z.1| + |z.2|) := by
        have hrt : Real.sqrt (z.1 ^ 2 + z.2 ^ 2) ≤ |z.1| + |z.2| := by
          rw [Real.sqrt_le_iff]
          exact ⟨by positivity, by nlinarith [sq_abs z.1, sq_abs z.2, abs_nonneg z.1, abs_nonneg z.2]⟩
        dsimp [W]; split_ifs <;> linarith [abs_nonneg z.1, abs_nonneg z.2]
      have hpow1 : (W z) ^ p ≤ (2 * (|z.1| + |z.2|)) ^ p := pow_le_pow_left₀ (hW_nn z) hW_le p
      have hpow2 : (|z.1| + |z.2|) ^ p ≤ (2 : ℝ) ^ p * (|z.1| ^ p + |z.2| ^ p) := by
        have hmax : |z.1| + |z.2| ≤ 2 * max |z.1| |z.2| := by
          linarith [le_max_left |z.1| |z.2|, le_max_right |z.1| |z.2|]
        calc (|z.1| + |z.2|) ^ p
            ≤ (2 * max |z.1| |z.2|) ^ p := pow_le_pow_left₀ (by positivity) hmax p
          _ = (2 : ℝ) ^ p * (max |z.1| |z.2|) ^ p := mul_pow _ _ _
          _ ≤ (2 : ℝ) ^ p * (|z.1| ^ p + |z.2| ^ p) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rcases le_total |z.1| |z.2| with h | h
              · rw [max_eq_right h]; linarith [pow_nonneg (abs_nonneg z.1) p]
              · rw [max_eq_left h]; linarith [pow_nonneg (abs_nonneg z.2) p]
      calc (W z) ^ p ≤ (2 : ℝ) ^ p * (|z.1| + |z.2|) ^ p := by rwa [mul_pow] at hpow1
        _ ≤ (2 : ℝ) ^ p * ((2 : ℝ) ^ p * (|z.1| ^ p + |z.2| ^ p)) :=
            mul_le_mul_of_nonneg_left hpow2 (by positivity)
        _ = (4 : ℝ) ^ p * (|z.1| ^ p + |z.2| ^ p) := by
            rw [← mul_assoc, ← mul_pow]; norm_num
    have hW_moment_eq : ∀ p : ℕ, 1 ≤ p →
        ∫ z : ℝ × ℝ, (W z) ^ p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) =
          (2 * Real.arcsin (2 * η) / Real.pi) *
            ((2 : ℝ) ^ ((3 * (p : ℝ)) / 2) * Real.Gamma (1 + (p : ℝ) / 2)) := by
      intro p hp
      rw [integral_stdGaussian2D_polar (hW_int p)]
      have hcongr : ∫ q in polarCoord.target, (q.1 * Real.exp (-q.1 ^ 2 / 2)) * (W (polarCoord.symm q)) ^ p =
          ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
            ((2 : ℝ) ^ p * (q.1 ^ (p + 1) * Real.exp (-q.1 ^ 2 / 2))) *
            (if |Real.cos q.2| < 2 * η then (1 : ℝ) else 0) := by
        refine setIntegral_congr_fun polarCoord.open_target.measurableSet (fun q hq => ?_)
        have hr_pos : 0 < q.1 := hq.1
        simp only [polarCoord_symm_apply, W]
        have hsq : (q.1 * Real.cos q.2) ^ 2 + (q.1 * Real.sin q.2) ^ 2 = q.1 ^ 2 := by
          have hsc := Real.cos_sq_add_sin_sq q.2; nlinarith
        rw [hsq, Real.sqrt_sq (le_of_lt hr_pos), abs_mul, abs_of_pos hr_pos]
        have hiff : q.1 * |Real.cos q.2| < 2 * η * q.1 ↔ |Real.cos q.2| < 2 * η := by
          constructor <;> intro h <;> nlinarith
        by_cases hc : |Real.cos q.2| < 2 * η
        · rw [if_pos (hiff.mpr hc), if_pos hc, mul_pow, mul_one, pow_succ]
          ring
        · rw [if_neg (fun h => hc (hiff.mp h)), if_neg hc, zero_pow (by omega), mul_zero, mul_zero]
      rw [hcongr,
          show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
          setIntegral_prod_mul
            (f := fun r : ℝ => (2 : ℝ) ^ p * (r ^ (p + 1) * Real.exp (-r ^ 2 / 2)))
            (g := fun θ : ℝ => if |Real.cos θ| < 2 * η then (1 : ℝ) else 0),
          integral_const_mul,
          integral_pow_mul_exp_neg_sq_div_two p, integral_indicator_abs_cos_lt hη0 hη1]
      have hpow2 : (2 : ℝ) ^ p * (2 : ℝ) ^ ((p : ℝ) / 2) = (2 : ℝ) ^ ((3 * (p : ℝ)) / 2) := by
        rw [← Real.rpow_natCast (2 : ℝ) p, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1; ring
      calc (2 * Real.pi)⁻¹ *
            ((2 : ℝ) ^ p * ((2 : ℝ) ^ ((p : ℝ) / 2) * Real.Gamma (1 + (p : ℝ) / 2)) *
              (4 * Real.arcsin (2 * η)))
          = (2 * Real.arcsin (2 * η) / Real.pi) *
              (((2 : ℝ) ^ p * (2 : ℝ) ^ ((p : ℝ) / 2)) * Real.Gamma (1 + (p : ℝ) / 2)) := by ring
        _ = (2 * Real.arcsin (2 * η) / Real.pi) *
              ((2 : ℝ) ^ ((3 * (p : ℝ)) / 2) * Real.Gamma (1 + (p : ℝ) / 2)) := by rw [hpow2]
    -- Pushforward along `a ↦ (⟪a, vhat⟫, ⟪a, e₂⟫)`
    have hpair_meas : Measurable (fun a : E => (⟪a, vhat⟫_ℝ, ⟪a, e₂⟫_ℝ)) :=
      ((continuous_id.inner continuous_const).measurable).prodMk
        ((continuous_id.inner continuous_const).measurable)
    have hW_comp_int : ∀ p : ℕ, Integrable (fun a : E => (W (⟪a, vhat⟫_ℝ, ⟪a, e₂⟫_ℝ)) ^ p) (stdGaussian E) := by
      intro p
      have h1 : Integrable (fun z : ℝ × ℝ => (W z) ^ p)
          ((stdGaussian E).map (fun a : E => (⟪a, vhat⟫_ℝ, ⟪a, e₂⟫_ℝ))) := by
        rw [stdGaussian_map_inner_pair hv he₂_norm he_orth]
        exact hW_int p
      exact (integrable_map_measure (g := fun z : ℝ × ℝ => (W z) ^ p)
        (hW_meas.pow_const p).aestronglyMeasurable hpair_meas.aemeasurable).mp h1
    have hX_int : ∀ p : ℕ, Integrable (fun a : E => (X a) ^ p) (stdGaussian E) := by
      intro p
      refine (hW_comp_int p).mono' (hX_meas.pow_const p).aestronglyMeasurable
        (Filter.Eventually.of_forall fun a => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hX_nn a) p)]
      exact pow_le_pow_left₀ (hX_nn a) (hX_le_W a) p
    have hX_mom_le : ∀ p : ℕ, 1 ≤ p →
        ∫ a : E, (X a) ^ p ∂(stdGaussian E) ≤
          (4 / 3 * η) * ((2 : ℝ) ^ ((3 * (p : ℝ)) / 2) * Real.Gamma (1 + (p : ℝ) / 2)) := by
      intro p hp
      have h1 : ∫ a : E, (X a) ^ p ∂(stdGaussian E) ≤
          ∫ a : E, (W (⟪a, vhat⟫_ℝ, ⟪a, e₂⟫_ℝ)) ^ p ∂(stdGaussian E) :=
        integral_mono (hX_int p) (hW_comp_int p) (fun a => pow_le_pow_left₀ (hX_nn a) (hX_le_W a) p)
      have h2 : ∫ a : E, (W (⟪a, vhat⟫_ℝ, ⟪a, e₂⟫_ℝ)) ^ p ∂(stdGaussian E) =
          ∫ z : ℝ × ℝ, (W z) ^ p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
        rw [← stdGaussian_map_inner_pair hv he₂_norm he_orth]
        exact (integral_map (φ := fun a : E => (⟪a, vhat⟫_ℝ, ⟪a, e₂⟫_ℝ))
          (f := fun z : ℝ × ℝ => (W z) ^ p)
          hpair_meas.aemeasurable (hW_meas.pow_const p).aestronglyMeasurable).symm
      rw [h2, hW_moment_eq p hp] at h1
      have harcsin := lemma43_arcsin_bound (le_of_lt hη0) hη1
      have hrhs_nn : 0 ≤ (2 : ℝ) ^ ((3 * (p : ℝ)) / 2) * Real.Gamma (1 + (p : ℝ) / 2) :=
        mul_nonneg (by positivity) (le_of_lt (Real.Gamma_pos_of_pos (by positivity)))
      exact le_trans h1 (mul_le_mul_of_nonneg_right harcsin hrhs_nn)
    refine ⟨hX_int, ?_, ?_⟩
    · -- Mean bound (`p = 1`): `(4/3 * η) * (2^(3/2) * Γ(3/2)) = (4 * √(2π) / 3) * η`
      have h1 := hX_mom_le 1 le_rfl
      simp only [pow_one, Nat.cast_one] at h1
      have heq : (2 : ℝ) ^ ((3 * (1 : ℝ)) / 2) * Real.Gamma (1 + (1 : ℝ) / 2) = Real.sqrt (2 * Real.pi) := by
        have harg1 : (3 * (1 : ℝ)) / 2 = (1 : ℝ) + (1 / 2 : ℝ) := by norm_num
        have harg2 : (1 : ℝ) + (1 : ℝ) / 2 = (1 / 2 : ℝ) + 1 := by norm_num
        rw [harg1, harg2, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
            ← Real.sqrt_eq_rpow, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq,
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      rw [heq] at h1
      linarith
    · -- Bernstein moments (`p ≥ 2`): plug in our Phase II `lemma43_moment_induction`!
      intro p hp
      have h1 := hX_mom_le p (by omega)
      have h2 := lemma43_moment_induction p hp
      exact le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))

/-! ### Stage 4.3: Bernstein MGF Bound via `lintegral_tsum` & Fixed-Grid Union Bound -/

private lemma ennreal_tsum_split_two (g : ℕ → ℝ≥0∞) :
    ∑' p : ℕ, g p = g 0 + g 1 + ∑' k : ℕ, g (k + 2) := by
  have h1 : ∑' p : ℕ, g p = g 0 + ∑' p : ℕ, g (p + 1) := tsum_eq_zero_add' ENNReal.summable
  have h2 : ∑' p : ℕ, g (p + 1) = g 1 + ∑' k : ℕ, g (k + 2) := tsum_eq_zero_add' ENNReal.summable
  rw [h1, h2, add_assoc]

/-- **Lemma 4.3(2) — True Gaussian Bernstein MGF Bound**:
For `0 < η ≤ 1 / 4`, unit vectors `vhat, u : E`, and `0 < lam < 1 / 2`, setting
`X a = phiEta η ⟪a, vhat⟫ ⟪a, u⟫`, `μ = E[X]`, and `v₀ = (32 / 3) * η`:
`Integrable (fun a => exp (lam * (X a - μ))) (stdGaussian E)` and
`mgf (X - μ) (stdGaussian E) lam ≤ exp (lam^2 * v₀ / (2 * (1 - 2 * lam)))`. -/
theorem lemma43_gaussian_bernstein_mgf
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    {vhat u : E} (hv : ‖vhat‖ = 1) (hu : ‖u‖ = 1)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    let X : E → ℝ := fun a => phiEta η ⟪a, vhat⟫_ℝ ⟪a, u⟫_ℝ
    let μ : ℝ := ∫ a, X a ∂(stdGaussian E)
    let v₀ : ℝ := 32 / 3 * η
    Integrable (fun a => Real.exp (lam * (X a - μ))) (stdGaussian E) ∧
    mgf (fun a => X a - μ) (stdGaussian E) lam ≤
      Real.exp (lam ^ 2 * v₀ / (2 * (1 - lam * 2))) := by
  intro X μ v₀
  have hX_nn : ∀ a : E, 0 ≤ X a := fun a => le_max_left _ _
  have hX_meas : Measurable X := by
    unfold X phiEta
    have h1 : Measurable (fun a : E => ⟪a, vhat⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    have h2 : Measurable (fun a : E => ⟪a, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    exact measurable_const.max (((continuous_abs.measurable.comp h2).const_mul 2).sub
      ((continuous_abs.measurable.comp h1).div_const η))
  obtain ⟨hX_int, _, hX_mom⟩ := lemma43_gaussian_moments hη0 hη1 hv hu
  have hμ_nn : 0 ≤ μ := integral_nonneg hX_nn
  -- Step 1: Bound `∫⁻ a, ofReal (exp (lam * X a)) ∂P` by `ofReal (1 + lam * μ + lam^2 * v₀ / (2 * (1 - 2*lam)))`
  let f : ℕ → E → ℝ≥0∞ := fun p a => ENNReal.ofReal ((lam * X a) ^ p / (Nat.factorial p : ℝ))
  have hf_meas : ∀ p : ℕ, Measurable (f p) := fun p =>
    ENNReal.measurable_ofReal.comp (((hX_meas.const_mul lam).pow_const p).div_const _)
  have htsum_pt : ∀ a : E, ENNReal.ofReal (Real.exp (lam * X a)) = ∑' p : ℕ, f p a := by
    intro a
    have hser : HasSum (fun p : ℕ => (lam * X a) ^ p / (Nat.factorial p : ℝ)) (Real.exp (lam * X a)) := by
      have := NormedSpace.expSeries_div_hasSum_exp (lam * X a)
      rwa [← Real.exp_eq_exp_ℝ] at this
    rw [← hser.tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg
      (fun p => div_nonneg (pow_nonneg (mul_nonneg (le_of_lt hlam0) (hX_nn a)) p) (Nat.cast_nonneg _))
      hser.summable
  have hlint_eq : ∫⁻ a : E, ENNReal.ofReal (Real.exp (lam * X a)) ∂(stdGaussian E) =
      ∑' p : ℕ, ∫⁻ a : E, f p a ∂(stdGaussian E) := by
    simp_rw [htsum_pt]
    exact lintegral_tsum (fun p => (hf_meas p).aemeasurable)
  -- Evaluate each term `∫⁻ f p`
  have hterm : ∀ p : ℕ, ∫⁻ a : E, f p a ∂(stdGaussian E) =
      ENNReal.ofReal ((lam ^ p / (Nat.factorial p : ℝ)) * ∫ a, (X a) ^ p ∂(stdGaussian E)) := by
    intro p
    have hrew : (fun a : E => f p a) =
        (fun a : E => ENNReal.ofReal ((lam ^ p / (Nat.factorial p : ℝ)) * (X a) ^ p)) := by
      ext a; dsimp [f]; congr 1; rw [mul_pow]; ring
    rw [hrew, ← ofReal_integral_eq_lintegral_ofReal ((hX_int p).const_mul _)
          (Filter.Eventually.of_forall fun a => mul_nonneg (by positivity) (pow_nonneg (hX_nn a) p)),
        integral_const_mul]
  have hterm0 : ∫⁻ a : E, f 0 a ∂(stdGaussian E) = ENNReal.ofReal 1 := by
    rw [hterm 0]; simp
  have hterm1 : ∫⁻ a : E, f 1 a ∂(stdGaussian E) = ENNReal.ofReal (lam * μ) := by
    rw [hterm 1]; simp [μ]
  have hterm_ge2 : ∀ k : ℕ, ∫⁻ a : E, f (k + 2) a ∂(stdGaussian E) ≤
      ENNReal.ofReal ((4 / 3 * η) * (2 * lam) ^ (k + 2)) := by
    intro k
    rw [hterm (k + 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm := hX_mom (k + 2) (by omega)
    have hfact_ne : (Nat.factorial (k + 2) : ℝ) ≠ 0 := by positivity
    calc (lam ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)) * ∫ a, (X a) ^ (k + 2) ∂(stdGaussian E)
        ≤ (lam ^ (k + 2) / (Nat.factorial (k + 2) : ℝ)) *
            ((4 / 3 * η) * ((Nat.factorial (k + 2) : ℝ) * (2 : ℝ) ^ (k + 2))) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = (4 / 3 * η) * (2 * lam) ^ (k + 2) := by
          rw [mul_pow]; field_simp [hfact_ne]
  -- Geometric series for `∑' k, (4/3 * η) * (2 * lam)^(k + 2)`
  have h2lam_lt : 2 * lam < 1 := by linarith
  have h2lam_nn : 0 ≤ 2 * lam := by linarith
  have hgeom_sum : HasSum (fun k : ℕ => (4 / 3 * η) * (2 * lam) ^ (k + 2))
      (lam ^ 2 * v₀ / (2 * (1 - lam * 2))) := by
    have h1 := hasSum_geometric_of_lt_one h2lam_nn h2lam_lt
    have h2 := h1.mul_left ((4 / 3 * η) * (2 * lam) ^ 2)
    have hrew : (fun k : ℕ => (4 / 3 * η) * (2 * lam) ^ 2 * (2 * lam) ^ k) =
        (fun k : ℕ => (4 / 3 * η) * (2 * lam) ^ (k + 2)) := by
      ext k; rw [pow_add, mul_assoc]; ring
    rw [hrew] at h2
    have hval : (4 / 3 * η) * (2 * lam) ^ 2 * (1 - 2 * lam)⁻¹ = lam ^ 2 * v₀ / (2 * (1 - lam * 2)) := by
      dsimp [v₀]
      have hne : 1 - lam * 2 ≠ 0 := by linarith
      have hne' : 1 - 2 * lam ≠ 0 := by linarith
      field_simp [hne, hne']
      ring
    rwa [hval] at h2
  have hlint_le : ∫⁻ a : E, ENNReal.ofReal (Real.exp (lam * X a)) ∂(stdGaussian E) ≤
      ENNReal.ofReal (1 + lam * μ + lam ^ 2 * v₀ / (2 * (1 - lam * 2))) := by
    rw [hlint_eq, ennreal_tsum_split_two (fun p => ∫⁻ a : E, f p a ∂(stdGaussian E)), hterm0, hterm1]
    have htail_le : ∑' k : ℕ, ∫⁻ a : E, f (k + 2) a ∂(stdGaussian E) ≤
        ENNReal.ofReal (lam ^ 2 * v₀ / (2 * (1 - lam * 2))) := by
      calc ∑' k : ℕ, ∫⁻ a : E, f (k + 2) a ∂(stdGaussian E)
          ≤ ∑' k : ℕ, ENNReal.ofReal ((4 / 3 * η) * (2 * lam) ^ (k + 2)) := ENNReal.tsum_le_tsum hterm_ge2
        _ = ENNReal.ofReal (∑' k : ℕ, (4 / 3 * η) * (2 * lam) ^ (k + 2)) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hgeom_sum.summable).symm
        _ = ENNReal.ofReal (lam ^ 2 * v₀ / (2 * (1 - lam * 2))) := by rw [hgeom_sum.tsum_eq]
    have hnn_rhs : 0 ≤ lam ^ 2 * v₀ / (2 * (1 - lam * 2)) := by
      dsimp [v₀]; exact div_nonneg (by positivity) (by linarith)
    calc ENNReal.ofReal 1 + ENNReal.ofReal (lam * μ) + ∑' k : ℕ, ∫⁻ a : E, f (k + 2) a ∂(stdGaussian E)
        ≤ ENNReal.ofReal 1 + ENNReal.ofReal (lam * μ) + ENNReal.ofReal (lam ^ 2 * v₀ / (2 * (1 - lam * 2))) :=
          add_le_add le_rfl htail_le
      _ = ENNReal.ofReal (1 + lam * μ + lam ^ 2 * v₀ / (2 * (1 - lam * 2))) := by
          rw [← ENNReal.ofReal_add (by norm_num) (mul_nonneg (le_of_lt hlam0) hμ_nn),
              ← ENNReal.ofReal_add (by linarith [mul_nonneg (le_of_lt hlam0) hμ_nn]) hnn_rhs]
  -- Step 2: Deduce `Integrable` and Bochner integral bound, then apply `lemma43_bernstein_mgf_step`
  have hexp_int : Integrable (fun a : E => Real.exp (lam * X a)) (stdGaussian E) := by
    refine ⟨(Real.measurable_exp.comp (hX_meas.const_mul lam)).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have heq_enorm : (fun a : E => ‖Real.exp (lam * X a)‖ₑ) =
        (fun a : E => ENNReal.ofReal (Real.exp (lam * X a))) := by
      ext a; rw [Real.enorm_eq_ofReal (le_of_lt (Real.exp_pos _))]
    rw [heq_enorm]
    exact lt_of_le_of_lt hlint_le ENNReal.ofReal_lt_top
  have hfactor : (fun a : E => Real.exp (lam * (X a - μ))) =
      (fun a : E => Real.exp (-lam * μ) * Real.exp (lam * X a)) := by
    ext a; rw [← Real.exp_add]; congr 1; ring
  have hint_centered : Integrable (fun a : E => Real.exp (lam * (X a - μ))) (stdGaussian E) := by
    rw [hfactor]; exact hexp_int.const_mul _
  refine ⟨hint_centered, ?_⟩
  have hint_le : ∫ a : E, Real.exp (lam * X a) ∂(stdGaussian E) ≤
      1 + lam * μ + lam ^ 2 * v₀ / (2 * (1 - lam * 2)) := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hexp_int
      (Filter.Eventually.of_forall fun a => le_of_lt (Real.exp_pos _))
    rw [← h1] at hlint_le
    have hnn_rhs : 0 ≤ 1 + lam * μ + lam ^ 2 * v₀ / (2 * (1 - lam * 2)) := by
      have : 0 ≤ lam ^ 2 * v₀ / (2 * (1 - lam * 2)) := by dsimp [v₀]; exact div_nonneg (by positivity) (by linarith)
      linarith [mul_nonneg (le_of_lt hlam0) hμ_nn]
    exact (ENNReal.ofReal_le_ofReal_iff hnn_rhs).mp hlint_le
  unfold mgf
  rw [hfactor, integral_const_mul]
  calc Real.exp (-lam * μ) * ∫ a : E, Real.exp (lam * X a) ∂(stdGaussian E)
      ≤ Real.exp (-lam * μ) * (1 + lam * μ + lam ^ 2 * v₀ / (2 * (1 - lam * 2))) :=
        mul_le_mul_of_nonneg_left hint_le (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (lam ^ 2 * v₀ / (2 * (1 - lam * 2))) :=
        lemma43_bernstein_mgf_step hlam0 hμ_nn (by dsimp [v₀]; positivity) (by norm_num) (by linarith)

/-- Pointwise Bernstein upper tail for a single pair `(vhat, u)` of unit vectors:
`P((1/m) ∑ i, phiEta η ⟪a i, vhat⟫ ⟪a i, u⟫ > (4√(2π)/3 + 2) η) ≤ exp (-(3/22) m η)`. -/
theorem lemma43_pointwise_flip_tail
    {m : ℕ} (hm : 0 < m) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4)
    {vhat u : E} (hv : ‖vhat‖ = 1) (hu : ‖u‖ = 1) :
    iidStdGaussian E m {a : Fin m → E |
      (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η <
        (1 / (m : ℝ)) * ∑ i : Fin m, phiEta η ⟪a i, vhat⟫_ℝ ⟪a i, u⟫_ℝ} ≤
      ENNReal.ofReal (Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  let X : E → ℝ := fun x => phiEta η ⟪x, vhat⟫_ℝ ⟪x, u⟫_ℝ
  let μ : ℝ := ∫ x, X x ∂(stdGaussian E)
  let Z : Fin m → (Fin m → E) → ℝ := fun i a => X (a i) - μ
  have hX_meas : Measurable X := by
    unfold X phiEta
    have h1 : Measurable (fun x : E => ⟪x, vhat⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    have h2 : Measurable (fun x : E => ⟪x, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    exact measurable_const.max (((continuous_abs.measurable.comp h2).const_mul 2).sub
      ((continuous_abs.measurable.comp h1).div_const η))
  have hZ_meas : ∀ i : Fin m, Measurable (Z i) :=
    fun i => (hX_meas.sub measurable_const).comp (measurable_pi_apply i)
  have h_indep : iIndepFun Z (iidStdGaussian E m) := by
    unfold iidStdGaussian
    exact iIndepFun_pi (fun _ => (hX_meas.sub measurable_const).aemeasurable)
  have hμ_le : μ ≤ (4 * Real.sqrt (2 * Real.pi) / 3) * η :=
    (lemma43_gaussian_moments hη0 hη1 hv hu).2.1
  -- Set optimal Bernstein parameter `lam = (2 η) / (v₀ + 2 * (2 η))` with `v₀ = (32/3) η`
  set v₀ : ℝ := 32 / 3 * η
  have hv₀_pos : 0 < v₀ := by dsimp [v₀]; positivity
  obtain ⟨hlam_pos, hlamB_lt, hbern_exp⟩ :=
    lemma43_bernstein_exponent hm_pos hv₀_pos (by norm_num : (0 : ℝ) < 2) (by linarith : 0 < 2 * η)
  set lam : ℝ := (2 * η) / (v₀ + 2 * (2 * η))
  have hlam_lt_half : lam < 1 / 2 := by linarith
  -- Inclusion into `{a | m * (2 η) ≤ ∑ i, Z i a}`
  have hsub : {a : Fin m → E |
      (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η <
        (1 / (m : ℝ)) * ∑ i : Fin m, phiEta η ⟪a i, vhat⟫_ℝ ⟪a i, u⟫_ℝ} ⊆
      {a : Fin m → E | (m : ℝ) * (2 * η) ≤ ∑ i : Fin m, Z i a} := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    have hsum_eq : ∑ i : Fin m, Z i a = (∑ i : Fin m, X (a i)) - (m : ℝ) * μ := by
      dsimp [Z]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum_eq]
    have h1 : (m : ℝ) * ((4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η) < ∑ i : Fin m, X (a i) := by
      have hmul := mul_lt_mul_of_pos_left ha hm_pos
      have hsimp : (m : ℝ) * ((1 / (m : ℝ)) * ∑ i : Fin m, X (a i)) = ∑ i : Fin m, X (a i) := by
        field_simp [ne_of_gt hm_pos]
      dsimp [X] at hsimp ⊢
      linarith
    nlinarith
  refine le_trans (measure_mono hsub) ?_
  -- MGF of each `Z i` and sum `∑ i, Z i` at `lam`
  obtain ⟨h_int_1d, h_mgf_1d⟩ := lemma43_gaussian_bernstein_mgf hη0 hη1 hv hu hlam_pos hlam_lt_half
  have h_int_each : ∀ i : Fin m, Integrable (fun a => Real.exp (lam * Z i a)) (iidStdGaussian E m) := by
    intro i
    have haesm : AEStronglyMeasurable (fun x : E => Real.exp (lam * (X x - μ)))
        ((iidStdGaussian E m).map (fun a : Fin m → E => a i)) := by
      rw [iidStdGaussian_map_eval]; exact h_int_1d.aestronglyMeasurable
    have hm1 : Integrable (fun x : E => Real.exp (lam * (X x - μ)))
        ((iidStdGaussian E m).map (fun a : Fin m → E => a i)) := by
      rw [iidStdGaussian_map_eval]; exact h_int_1d
    exact (integrable_map_measure (g := fun x : E => Real.exp (lam * (X x - μ)))
      haesm (measurable_pi_apply i).aemeasurable).mp hm1
  have h_int_sum : Integrable (fun a => Real.exp (lam * ∑ i : Fin m, Z i a)) (iidStdGaussian E m) := by
    simpa using h_indep.integrable_exp_mul_sum hZ_meas (s := Finset.univ) (fun i _ => h_int_each i)
  have h_mgf_each : ∀ i : Fin m,
      mgf (Z i) (iidStdGaussian E m) lam ≤ Real.exp (lam ^ 2 * v₀ / (2 * (1 - lam * 2))) := by
    intro i
    have haesm : AEStronglyMeasurable (fun x : E => Real.exp (lam * (X x - μ)))
        ((iidStdGaussian E m).map (fun a : Fin m → E => a i)) := by
      rw [iidStdGaussian_map_eval]; exact h_int_1d.aestronglyMeasurable
    have heq : mgf (Z i) (iidStdGaussian E m) lam = mgf (fun x => X x - μ) (stdGaussian E) lam := by
      unfold mgf
      have hstep := integral_map (φ := fun a : Fin m → E => a i)
        (f := fun x : E => Real.exp (lam * (X x - μ)))
        (measurable_pi_apply i).aemeasurable haesm
      rw [iidStdGaussian_map_eval] at hstep
      exact hstep.symm
    rw [heq]
    exact h_mgf_1d
  have h_mgf_sum : mgf (fun a => ∑ i : Fin m, Z i a) (iidStdGaussian E m) lam ≤
      Real.exp ((m : ℝ) * (lam ^ 2 * v₀ / (2 * (1 - lam * 2)))) := by
    have hprod := h_indep.mgf_sum hZ_meas Finset.univ (t := lam)
    have hfun : (∑ i : Fin m, Z i) = (fun a => ∑ i : Fin m, Z i a) := by ext a; simp
    rw [hfun] at hprod
    have hle := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => mgf_nonneg) (fun i _ => h_mgf_each i)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul] at hle
    rwa [hprod]
  -- Apply Chernoff bound `measure_ge_le_exp_mul_mgf` and our Phase II `lemma43_bernstein_const_3_22`!
  have hchernoff := measure_ge_le_exp_mul_mgf (μ := iidStdGaussian E m)
    (X := fun a => ∑ i : Fin m, Z i a) ((m : ℝ) * (2 * η)) (le_of_lt hlam_pos) h_int_sum
  rw [← ENNReal.ofReal_toReal (measure_ne_top (iidStdGaussian E m) _)]
  refine ENNReal.ofReal_le_ofReal (le_trans hchernoff ?_)
  calc Real.exp (-lam * ((m : ℝ) * (2 * η))) * mgf (fun a => ∑ i, Z i a) (iidStdGaussian E m) lam
      ≤ Real.exp (-lam * ((m : ℝ) * (2 * η))) * Real.exp ((m : ℝ) * (lam ^ 2 * v₀ / (2 * (1 - lam * 2)))) :=
        mul_le_mul_of_nonneg_left h_mgf_sum (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-(m : ℝ) * lam * (2 * η) + (m : ℝ) * (lam ^ 2 * v₀ / (2 * (1 - lam * 2)))) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-(m : ℝ) * (2 * η) ^ 2 / (2 * (v₀ + 2 * (2 * η)))) := hbern_exp
    _ ≤ Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η) :=
        Real.exp_le_exp.mpr (lemma43_bernstein_const_3_22 (le_of_lt hm_pos) hη0 (le_of_lt hv₀_pos) le_rfl)

/-! ### Stage 4.4: Uniform Fixed-Grid Event for Pairwise Flip Surrogates (Stage 4 Main Theorem) -/

/-- **Stage 4 Main Theorem (Lemma 4.3 — Fixed Finite `(η/4)`-Net Concentration)**:
Constructs ONE fixed finite `(η/4)`-net `N ⊆ S^{d-1}` (`|N| ≤ (9 / η)^d`) and bounds
the failure probability of the uniform net upper bound across all `j < k` and `u₀ ∈ N` by
`M * (9 / η)^d * exp (-(3 / 22) * m * η)`, where `M = (Finset.univ.filter (fun p : Fin r × Fin r => p.1 < p.2)).card ≤ r^2 / 2`. -/
theorem prob_flip_net_event
    {m r : ℕ} (hm : 0 < m)
    (β_star : Fin r → E)
    (h_distinct : ∀ j k : Fin r, j ≠ k → β_star j ≠ β_star k)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 4) :
    ∃ N : Finset E,
      (∀ u₀ ∈ N, ‖u₀‖ = 1) ∧
      (∀ u : E, ‖u‖ = 1 → ∃ u₀ ∈ N, ‖u - u₀‖ ≤ η / 4) ∧
      iidStdGaussian E m {a : Fin m → E |
        ¬ ∀ (j k : Fin r), j < k → ∀ u₀ ∈ N,
          (1 / (m : ℝ)) * ∑ i : Fin m,
            phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u₀⟫_ℝ ≤
          (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η} ≤
      ENNReal.ofReal
        ((((Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2)).card : ℝ) *
          (9 / η) ^ Module.finrank ℝ E *
          Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) := by
  obtain ⟨N, hN_unit, hN_cover, hN_card⟩ := exists_sphere_eps_net E (by linarith : 0 < η / 4)
  have h9 : 1 + 2 / (η / 4) ≤ 9 / η := by
    have hrew : 1 + 2 / (η / 4) = (η + 8) / η := by field_simp [ne_of_gt hη0]; ring
    rw [hrew]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hη0)
  have hN_card9 : (N.card : ℝ) ≤ (9 / η) ^ Module.finrank ℝ E :=
    le_trans hN_card (pow_le_pow_left₀ (by positivity) h9 _)
  refine ⟨N, hN_unit, hN_cover, ?_⟩
  let pairs : Finset (Fin r × Fin r) := Finset.univ.filter (fun p => p.1 < p.2)
  have hsub :
      {a : Fin m → E |
        ¬ ∀ (j k : Fin r), j < k → ∀ u₀ ∈ N,
          (1 / (m : ℝ)) * ∑ i : Fin m,
            phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u₀⟫_ℝ ≤
          (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η} ⊆
      ⋃ p ∈ pairs, ⋃ u₀ ∈ N,
        {a : Fin m → E |
          (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η <
            (1 / (m : ℝ)) * ∑ i : Fin m,
              phiEta η ⟪a i, (‖β_star p.1 - β_star p.2‖⁻¹) • (β_star p.1 - β_star p.2)⟫_ℝ ⟪a i, u₀⟫_ℝ} := by
    intro a ha
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_lt, pairs,
      Finset.mem_filter, Finset.mem_univ, true_and] at hnot
    exact ha (fun j k hjk u₀ hu₀ => hnot (j, k) hjk u₀ hu₀)
  have h_pt : ∀ p ∈ pairs, ∀ u₀ ∈ N,
      iidStdGaussian E m {a : Fin m → E |
        (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η <
          (1 / (m : ℝ)) * ∑ i : Fin m,
            phiEta η ⟪a i, (‖β_star p.1 - β_star p.2‖⁻¹) • (β_star p.1 - β_star p.2)⟫_ℝ ⟪a i, u₀⟫_ℝ} ≤
        ENNReal.ofReal (Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) := by
    intro p hp u₀ hu₀
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    have hv_ne : β_star p.1 - β_star p.2 ≠ 0 := sub_ne_zero.mpr (h_distinct p.1 p.2 (ne_of_lt hlt))
    have hv_pos : 0 < ‖β_star p.1 - β_star p.2‖ := norm_pos_iff.mpr hv_ne
    have hvhat : ‖(‖β_star p.1 - β_star p.2‖⁻¹) • (β_star p.1 - β_star p.2)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv_pos), inv_mul_cancel₀ (ne_of_gt hv_pos)]
    exact lemma43_pointwise_flip_tail hm hη0 hη1 hvhat (hN_unit u₀ hu₀)
  calc iidStdGaussian E m _
      ≤ iidStdGaussian E m (⋃ p ∈ pairs, ⋃ u₀ ∈ N, _) := measure_mono hsub
    _ ≤ ∑ p ∈ pairs, iidStdGaussian E m (⋃ u₀ ∈ N, _) := measure_biUnion_finset_le pairs _
    _ ≤ ∑ p ∈ pairs, ∑ u₀ ∈ N, iidStdGaussian E m _ :=
        Finset.sum_le_sum (fun p _ => measure_biUnion_finset_le N _)
    _ ≤ ∑ _p ∈ pairs, ∑ _u₀ ∈ N, ENNReal.ofReal (Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) :=
        Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun u₀ hu₀ => h_pt p hp u₀ hu₀))
    _ = ENNReal.ofReal ((pairs.card : ℝ) * (N.card : ℝ) * Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((pairs.card : ℝ) * (9 / η) ^ Module.finrank ℝ E *
          Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := mul_le_mul_of_nonneg_left hN_card9 (Nat.cast_nonneg pairs.card)
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))

end Research107
