import Research107.Definitions
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Stage 1.1: Standard Gaussian Product Model `a₁, …, aₘ ~ i.i.d. N(0, I_d)` -/

/-- The i.i.d. standard Gaussian design measure on `Fin m → E`, matching `Definitions.lean`. -/
noncomputable def iidStdGaussian (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (m : ℕ) :
    Measure (Fin m → E) :=
  Measure.pi (fun _ : Fin m => stdGaussian E)

instance isProbabilityMeasure_iidStdGaussian (m : ℕ) :
    IsProbabilityMeasure (iidStdGaussian E m) := by
  unfold iidStdGaussian
  infer_instance

/-- The `i`-th coordinate evaluation `a ↦ a i` has law `stdGaussian E` under `iidStdGaussian E m`. -/
lemma iidStdGaussian_map_eval (m : ℕ) (i : Fin m) :
    (iidStdGaussian E m).map (fun a : Fin m → E => a i) = stdGaussian E := by
  unfold iidStdGaussian
  exact (measurePreserving_eval (fun _ : Fin m => stdGaussian E) i).map_eq

/-! ### Stage 1.2: 1D & 2D Orthogonal Projections and Symmetry of `stdGaussian E` -/

/-- Pushforward of `stdGaussian E` along `a ↦ ⟪a, v⟫_ℝ` is `gaussianReal 0 (Real.toNNReal (‖v‖^2))`. -/
theorem stdGaussian_map_inner (v : E) :
    (stdGaussian E).map (fun a : E => ⟪a, v⟫_ℝ) = gaussianReal 0 (Real.toNNReal (‖v‖ ^ 2)) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), charFun_gaussianReal]
  have h : (fun x : E => Complex.exp ((t : ℂ) * (⟪x, v⟫_ℝ : ℂ) * Complex.I)) =
      (fun x : E => Complex.exp ((⟪x, t • v⟫_ℝ : ℂ) * Complex.I)) := by
    ext x
    rw [real_inner_smul_right]
    push_cast
    ring_nf
  rw [h, ← charFun_apply, charFun_stdGaussian]
  simp only [norm_smul, Real.norm_eq_abs, Complex.ofReal_zero, mul_zero,
    Real.coe_toNNReal _ (sq_nonneg _)]
  congr 1
  rw [← Complex.ofReal_pow, mul_pow, sq_abs]
  push_cast
  ring

/-- For any unit vector `u` (`‖u‖ = 1`), `a ↦ ⟪a, u⟫_ℝ` has standard normal law `N(0, 1)`. -/
theorem stdGaussian_map_inner_unit {u : E} (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ) = gaussianReal 0 1 := by
  rw [stdGaussian_map_inner]
  simp [hu]

lemma hasLaw_inner_stdGaussian_unit {u : E} (hu : ‖u‖ = 1) :
    HasLaw (fun a : E => ⟪a, u⟫_ℝ) (gaussianReal 0 1) (stdGaussian E) where
  aemeasurable := (continuous_id.inner continuous_const).measurable.aemeasurable
  map_eq := stdGaussian_map_inner_unit hu

/-- For orthonormal `e₁, e₂ : E`, the pair `(⟪a, e₁⟫, ⟪a, e₂⟫)` has law `N(0,1) × N(0,1)`. -/
theorem stdGaussian_map_inner_pair {e₁ e₂ : E}
    (h1 : ‖e₁‖ = 1) (h2 : ‖e₂‖ = 1) (h12 : ⟪e₁, e₂⟫_ℝ = 0) :
    (stdGaussian E).map (fun a : E => (⟪a, e₁⟫_ℝ, ⟪a, e₂⟫_ℝ)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  apply Measure.ext_of_charFunDual
  ext L
  set t₁ : ℝ := L (1, 0)
  set t₂ : ℝ := L (0, 1)
  have hL : ∀ p : ℝ × ℝ, L p = t₁ * p.1 + t₂ * p.2 := by
    intro ⟨x, y⟩
    have hdecomp : (x, y) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    conv_lhs => rw [hdecomp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    dsimp [t₁, t₂]
    ring
  -- LHS: `charFunDual ((stdGaussian E).map f) L = exp (-(t₁^2 + t₂^2) / 2)`
  have hLHS : charFunDual ((stdGaussian E).map (fun a : E => (⟪a, e₁⟫_ℝ, ⟪a, e₂⟫_ℝ))) L =
      Complex.exp (-((t₁ ^ 2 + t₂ ^ 2 : ℝ) : ℂ) / 2) := by
    rw [charFunDual_apply, integral_map (by fun_prop) (by fun_prop)]
    have hfun : (fun a : E => Complex.exp ((L (⟪a, e₁⟫_ℝ, ⟪a, e₂⟫_ℝ) : ℂ) * Complex.I)) =
        (fun a : E => Complex.exp ((⟪a, t₁ • e₁ + t₂ • e₂⟫_ℝ : ℂ) * Complex.I)) := by
      ext a
      rw [hL, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    rw [hfun, ← charFun_apply, charFun_stdGaussian]
    have hnorm : ‖t₁ • e₁ + t₂ • e₂‖ ^ 2 = t₁ ^ 2 + t₂ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          h1, h2, mul_one, mul_one, sq_abs, sq_abs,
          real_inner_smul_left, real_inner_smul_right, h12]
      ring
    rw [← Complex.ofReal_pow, hnorm]
  -- RHS: `charFunDual (N(0,1) × N(0,1)) L = exp (-(t₁^2 + t₂^2) / 2)`
  have hRHS : charFunDual ((gaussianReal 0 1).prod (gaussianReal 0 1)) L =
      Complex.exp (-((t₁ ^ 2 + t₂ ^ 2 : ℝ) : ℂ) / 2) := by
    rw [charFunDual_apply]
    have hfun : (fun p : ℝ × ℝ => Complex.exp ((L p : ℂ) * Complex.I)) =
        (fun p : ℝ × ℝ =>
          Complex.exp ((t₁ : ℂ) * (p.1 : ℂ) * Complex.I) *
          Complex.exp ((t₂ : ℂ) * (p.2 : ℂ) * Complex.I)) := by
      ext ⟨x, y⟩
      rw [hL, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hfun,
        integral_prod_mul (f := fun x : ℝ => Complex.exp ((t₁ : ℂ) * (x : ℂ) * Complex.I))
          (g := fun y : ℝ => Complex.exp ((t₂ : ℂ) * (y : ℂ) * Complex.I)),
        ← charFun_apply_real, ← charFun_apply_real,
        charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add]
    congr 1
    simp only [Complex.ofReal_zero, mul_zero, zero_sub, NNReal.coe_one, one_mul]
    push_cast
    ring
  rw [hLHS, hRHS]

/-- Antipodal symmetry of `stdGaussian E`: `-a` has the same distribution as `a`. -/
theorem stdGaussian_neg_invariant :
    (stdGaussian E).map (fun a : E => -a) = stdGaussian E := by
  simpa using stdGaussian_map (LinearIsometryEquiv.neg ℝ (E := E))

/-! ### Stage 1.3: Almost-Sure Strict Active Cones (Eliminates `h_active`) -/

/-- Any hyperplane `{a | ⟪a, v⟫ = 0}` with `v ≠ 0` has standard Gaussian measure zero. -/
theorem stdGaussian_hyperplane_zero {v : E} (hv : v ≠ 0) :
    stdGaussian E {a : E | ⟪a, v⟫_ℝ = 0} = 0 := by
  have hmeas : Measurable (fun a : E => ⟪a, v⟫_ℝ) := (continuous_id.inner continuous_const).measurable
  have hpre : {a : E | ⟪a, v⟫_ℝ = 0} = (fun a : E => ⟪a, v⟫_ℝ) ⁻¹' ({0} : Set ℝ) := rfl
  rw [hpre, ← Measure.map_apply hmeas (measurableSet_singleton 0), stdGaussian_map_inner]
  have hne : Real.toNNReal (‖v‖ ^ 2) ≠ 0 := by
    intro h
    have h1 : (Real.toNNReal (‖v‖ ^ 2) : ℝ) = 0 := congrArg NNReal.toReal h
    rw [Real.coe_toNNReal _ (sq_nonneg _)] at h1
    exact hv (norm_eq_zero.mp (sq_eq_zero_iff.mp h1))
  exact gaussianReal_absolutelyContinuous 0 hne (by simp)

/-- **Elimination of `h_active`**: Whenever `β_star` has pairwise distinct rows, almost every i.i.d.
Gaussian sample `a : Fin m → E` has every `a i` lying in some strict active cone `activeCone β_star j₀`. -/
theorem iidStdGaussian_ae_active {m r : ℕ} (hr : 0 < r)
    (β_star : Fin r → E) (h_distinct : ∀ j k : Fin r, j ≠ k → β_star j ≠ β_star k) :
    ∀ᵐ a ∂(iidStdGaussian E m), ∀ i : Fin m, ∃ j₀ : Fin r, a i ∈ activeCone β_star j₀ := by
  -- For each `(i, j, k)` with `j ≠ k`, `⟪a i, β_star j - β_star k⟫ = 0` has measure 0
  have h_pair : ∀ (i : Fin m) (j k : Fin r), j ≠ k →
      ∀ᵐ a ∂(iidStdGaussian E m), ⟪a i, β_star j - β_star k⟫_ℝ ≠ 0 := by
    intro i j k hjk
    rw [ae_iff]
    have hset : {a : Fin m → E | ¬ ⟪a i, β_star j - β_star k⟫_ℝ ≠ 0} =
        (fun a : Fin m → E => a i) ⁻¹' {x : E | ⟪x, β_star j - β_star k⟫_ℝ = 0} := by
      ext a; simp
    rw [hset]
    have hclosed : MeasurableSet {x : E | ⟪x, β_star j - β_star k⟫_ℝ = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const |>.measurableSet
    rw [← Measure.map_apply (measurable_pi_apply i) hclosed, iidStdGaussian_map_eval]
    exact stdGaussian_hyperplane_zero (sub_ne_zero.mpr (h_distinct j k hjk))
  have h_all : ∀ᵐ a ∂(iidStdGaussian E m),
      ∀ (i : Fin m) (j k : Fin r), j ≠ k → ⟪a i, β_star j - β_star k⟫_ℝ ≠ 0 := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    rw [ae_all_iff]; intro k
    by_cases hjk : j ≠ k
    · filter_upwards [h_pair i j k hjk] with a ha _ using ha
    · exact Filter.Eventually.of_forall (fun _ h => absurd h hjk)
  filter_upwards [h_all] with a ha i
  have hne : (Finset.univ : Finset (Fin r)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_eq_sup' hne (fun j => ⟪a i, β_star j⟫_ℝ)
  refine ⟨j₀, fun k hkj => ?_⟩
  have hle : ⟪a i, β_star k⟫_ℝ ≤ ⟪a i, β_star j₀⟫_ℝ := by
    rw [← hj₀]
    exact Finset.le_sup' (fun j => ⟪a i, β_star j⟫_ℝ) (Finset.mem_univ k)
  have hne_val : ⟪a i, β_star j₀⟫_ℝ - ⟪a i, β_star k⟫_ℝ ≠ 0 := by
    rw [← inner_sub_right]
    exact ha i j₀ k (Ne.symm hkj)
  exact lt_of_le_of_ne hle (fun heq => hne_val (by linarith))

/-! ### Stage 1.4: Exact 1D Standard Gaussian Integrals (`|Z|`, `cosh(λZ)`, `exp(λ Z²)`) -/

/-- Exact Gaussian PDF formula for `N(0, 1)`. -/
lemma gaussianPDFReal_std (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal_def]

/-- `∫ z, |z| ∂(gaussianReal 0 1) = √(2 / π)`. -/
theorem integral_abs_gaussianReal_std :
    ∫ z : ℝ, |z| ∂(gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp_rw [smul_eq_mul, gaussianPDFReal_std, mul_assoc]
  rw [integral_const_mul]
  -- Compute `∫ x : ℝ, exp (-x^2 / 2) * |x| = 2`
  have h_even : ∫ x : ℝ, Real.exp (-x ^ 2 / 2) * |x| =
      2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) * x := by
    have hsplit : ∫ x : ℝ, Real.exp (-x ^ 2 / 2) * |x| =
        (∫ x in Set.Iic (0 : ℝ), Real.exp (-x ^ 2 / 2) * |x|) +
        (∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) * |x|) := by
      have hint : Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2) * |x|) := by
        have hdom : Integrable (fun x : ℝ => Real.exp (-(1 / 4 : ℝ) * x ^ 2)) :=
          integrable_exp_neg_mul_sq (by norm_num)
        refine hdom.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) (abs_nonneg _))]
        have h1 : |x| ≤ Real.exp (x ^ 2 / 4) := by
          have := Real.add_one_le_exp (x ^ 2 / 4)
          have hsq : |x| ≤ 1 + x ^ 2 / 4 := by nlinarith [sq_nonneg (|x| - 2), sq_abs x]
          linarith
        calc Real.exp (-x ^ 2 / 2) * |x|
            ≤ Real.exp (-x ^ 2 / 2) * Real.exp (x ^ 2 / 4) :=
              mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos _))
          _ = Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by rw [← Real.exp_add]; congr 1; ring
      exact (integral_add_compl measurableSet_Iic hint).symm.trans (by rw [Set.compl_Iic])
    have hpos : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) * |x| =
        ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) * x :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [abs_of_pos hx])
    have hneg : ∫ x in Set.Iic (0 : ℝ), Real.exp (-x ^ 2 / 2) * |x| =
        ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) * x := by
      have h0 : ∫ x in Set.Iic (-(0 : ℝ)), Real.exp (-x ^ 2 / 2) * |x| =
          ∫ x in Set.Ioi (0 : ℝ), Real.exp (-(-x) ^ 2 / 2) * |-x| :=
        (integral_comp_neg_Ioi (c := (0 : ℝ)) (f := fun x : ℝ => Real.exp (-x ^ 2 / 2) * |x|)).symm
      rw [neg_zero] at h0
      rw [h0]
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      simp [abs_of_pos (Set.mem_Ioi.mp hx)]
    rw [hsplit, hpos, hneg]; ring
  have h_half : ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x ^ 2 / 2) * x = 1 := by
    have hderiv : ∀ x ∈ Set.Ici (0 : ℝ),
        HasDerivAt (fun t : ℝ => -Real.exp (-t ^ 2 / 2)) (Real.exp (-x ^ 2 / 2) * x) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => -t ^ 2 / 2) (-x) x := by
        convert ((hasDerivAt_pow 2 x).neg.div_const (2 : ℝ)) using 1
        ring
      convert (h1.exp).fun_neg using 1
      ring
    have hlim : Filter.Tendsto (fun t : ℝ => -Real.exp (-t ^ 2 / 2)) Filter.atTop (nhds 0) := by
      have hsq : Filter.Tendsto (fun t : ℝ => -t ^ 2 / 2) Filter.atTop Filter.atBot := by
        refine Filter.tendsto_atBot.mpr (fun b => ?_)
        refine Filter.eventually_atTop.mpr ⟨max 1 (Real.sqrt (max 0 (-2 * b)) + 1), fun t ht => ?_⟩
        have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
        have ht2 : Real.sqrt (max 0 (-2 * b)) + 1 ≤ t := le_trans (le_max_right _ _) ht
        have hsq' : max 0 (-2 * b) ≤ t ^ 2 := by
          have hs0 : 0 ≤ Real.sqrt (max 0 (-2 * b)) := Real.sqrt_nonneg _
          have h1 : Real.sqrt (max 0 (-2 * b)) ^ 2 ≤ t ^ 2 := by nlinarith
          rwa [Real.sq_sqrt (le_max_left _ _)] at h1
        have : -2 * b ≤ t ^ 2 := le_trans (le_max_right _ _) hsq'
        linarith
      simpa using (Real.tendsto_exp_atBot.comp hsq).neg
    have hint_pos : IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2 / 2) * x) (Set.Ioi 0) := by
      have hdom : IntegrableOn (fun x : ℝ => Real.exp (-(1 / 4 : ℝ) * x ^ 2)) (Set.Ioi 0) :=
        (integrable_exp_neg_mul_sq (by norm_num)).integrableOn
      refine hdom.mono' (by fun_prop) ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt hx))]
      have h1 : x ≤ Real.exp (x ^ 2 / 4) := by
        have := Real.add_one_le_exp (x ^ 2 / 4)
        have hsq : x ≤ 1 + x ^ 2 / 4 := by nlinarith [sq_nonneg (x - 2)]
        linarith
      calc Real.exp (-x ^ 2 / 2) * x
          ≤ Real.exp (-x ^ 2 / 2) * Real.exp (x ^ 2 / 4) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos _))
        _ = Real.exp (-(1 / 4 : ℝ) * x ^ 2) := by rw [← Real.exp_add]; congr 1; ring
    have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint_pos hlim
    simpa using hftc
  rw [h_even, h_half, mul_one]
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hspi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpi)
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  field_simp [hs2, hspi]
  linarith

/-- For any vector `v : E`, `∫ a, |⟪a, v⟫| ∂(stdGaussian E) = ‖v‖ * √(2 / π)`. -/
theorem integral_abs_inner_stdGaussian (v : E) :
    ∫ a : E, |⟪a, v⟫_ℝ| ∂(stdGaussian E) = ‖v‖ * Real.sqrt (2 / Real.pi) := by
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
    rw [heq, integral_const_mul]
    have hmap : ∫ a : E, |⟪a, u⟫_ℝ| ∂(stdGaussian E) = ∫ z : ℝ, |z| ∂(gaussianReal 0 1) := by
      rw [← stdGaussian_map_inner_unit hu, integral_map (by fun_prop) (by fun_prop)]
    rw [hmap, integral_abs_gaussianReal_std]

/-- `∫ z, cosh (lam * z) ∂(gaussianReal 0 1) = exp (lam ^ 2 / 2)`. -/
theorem integral_cosh_mul_gaussianReal (lam : ℝ) :
    ∫ z : ℝ, Real.cosh (lam * z) ∂(gaussianReal 0 1) = Real.exp (lam ^ 2 / 2) := by
  simp_rw [Real.cosh_eq, div_eq_mul_inv]
  rw [integral_mul_const]
  have hint1 : Integrable (fun z : ℝ => Real.exp (lam * z)) (gaussianReal 0 1) :=
    integrable_exp_mul_gaussianReal lam
  have hint2 : Integrable (fun z : ℝ => Real.exp (-(lam * z))) (gaussianReal 0 1) := by
    have : (fun z : ℝ => Real.exp (-(lam * z))) = (fun z : ℝ => Real.exp ((-lam) * z)) := by
      ext z; ring_nf
    rw [this]
    exact integrable_exp_mul_gaussianReal (-lam)
  rw [integral_add hint1 hint2]
  have h1 : ∫ z : ℝ, Real.exp (lam * z) ∂(gaussianReal 0 1) = Real.exp (lam ^ 2 / 2) := by
    have := mgf_id_gaussianReal (μ := 0) (v := 1)
    have h := congrFun this lam
    simpa [mgf] using h
  have h2 : ∫ z : ℝ, Real.exp (-(lam * z)) ∂(gaussianReal 0 1) = Real.exp (lam ^ 2 / 2) := by
    have hrewrite : (fun z : ℝ => Real.exp (-(lam * z))) = (fun z : ℝ => Real.exp ((-lam) * z)) := by
      ext z; ring_nf
    rw [hrewrite]
    have := mgf_id_gaussianReal (μ := 0) (v := 1)
    have h := congrFun this (-lam)
    simpa [mgf] using h
  rw [h1, h2]
  rw [div_eq_mul_inv]
  ring

/-- Integrability of `exp (lam * z^2)` under `N(0, 1)` for `lam < 1/2`. -/
lemma integrable_exp_mul_sq_gaussianReal {lam : ℝ} (hlam : lam < 1 / 2) :
    Integrable (fun z : ℝ => Real.exp (lam * z ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff (measurable_gaussianPDF 0 1)
        (Filter.Eventually.of_forall (fun _ => gaussianPDF_lt_top))]
  have heq : (fun z : ℝ => Real.exp (lam * z ^ 2) * (gaussianPDF 0 1 z).toReal) =
      (fun z : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 - 2 * lam) / 2) * z ^ 2)) := by
    ext z
    rw [mul_comm, toReal_gaussianPDF, gaussianPDFReal_std, mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [heq]
  exact (integrable_exp_neg_mul_sq (by linarith : 0 < (1 - 2 * lam) / 2)).const_mul _

/-- Exact `χ²₁` MGF: `∫ z, exp (lam * z^2) ∂(gaussianReal 0 1) = 1 / √(1 - 2 * lam)` for `lam < 1/2`. -/
theorem integral_exp_mul_sq_gaussianReal {lam : ℝ} (hlam : lam < 1 / 2) :
    ∫ z : ℝ, Real.exp (lam * z ^ 2) ∂(gaussianReal 0 1) = 1 / Real.sqrt (1 - 2 * lam) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have heq : (fun z : ℝ => gaussianPDFReal 0 1 z • Real.exp (lam * z ^ 2)) =
      (fun z : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 - 2 * lam) / 2) * z ^ 2)) := by
    ext z
    rw [smul_eq_mul, gaussianPDFReal_std, mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [heq, integral_const_mul, integral_gaussian ((1 - 2 * lam) / 2)]
  have hpos : 0 < 1 - 2 * lam := by linarith
  have hdiv : Real.pi / ((1 - 2 * lam) / 2) = (2 * Real.pi) / (1 - 2 * lam) := by
    field_simp [ne_of_gt hpos]
  rw [hdiv, Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  have hs2pi : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp [hs2pi]

/-! ### Stage 1.5: Volumetric Covering Number on the Unit Sphere `S^{d-1}` -/

/-- **Volumetric Covering Number Theorem**: For any finite-dimensional real inner product space `E`
and any `ε > 0`, there exists a finite `ε`-net `N ⊆ S^{d-1}` of cardinality at most
`(1 + 2 / ε) ^ (Module.finrank ℝ E)`. -/
theorem exists_sphere_eps_net (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E,
      (∀ u₀ ∈ N, ‖u₀‖ = 1) ∧
      (∀ u : E, ‖u‖ = 1 → ∃ u₀ ∈ N, ‖u - u₀‖ ≤ ε) ∧
      (N.card : ℝ) ≤ (1 + 2 / ε) ^ Module.finrank ℝ E := by
  -- Handle trivial (`finrank = 0`) vs nontrivial (`finrank ≥ 1`) space cleanly
  by_cases hnt : Nontrivial E
  · haveI : Nontrivial E := hnt
    set d := Module.finrank ℝ E
    -- Predicate: `F` is a finite `ε`-separated subset of the unit sphere
    let IsSep (F : Finset E) : Prop :=
      (∀ x ∈ F, ‖x‖ = 1) ∧ (∀ x ∈ F, ∀ y ∈ F, x ≠ y → ε < ‖x - y‖)
    -- Step 1: Volume packing upper bound `(F.card : ℝ) ≤ (1 + 2 / ε)^d` for every `IsSep F`
    have h_pack : ∀ F : Finset E, IsSep F → (F.card : ℝ) ≤ (1 + 2 / ε) ^ d := by
      intro F ⟨hunit, hsep⟩
      -- Disjoint open balls `B(x, ε/2)` for `x ∈ F` lie inside `B(0, 1 + ε/2)`
      have hdisj : Set.Pairwise (F : Set E) (fun x y => Disjoint (Metric.ball x (ε / 2)) (Metric.ball y (ε / 2))) := by
        intro x hx y hy hxy
        rw [Set.disjoint_left]
        intro z hzx hzy
        have h1 : ‖z - x‖ < ε / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hzx
        have h2 : ‖z - y‖ < ε / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hzy
        have htri : ‖x - y‖ ≤ ‖z - x‖ + ‖z - y‖ := by
          have : x - y = -(z - x) + (z - y) := by abel
          calc ‖x - y‖ = ‖-(z - x) + (z - y)‖ := by rw [this]
            _ ≤ ‖-(z - x)‖ + ‖z - y‖ := norm_add_le _ _
            _ = ‖z - x‖ + ‖z - y‖ := by rw [norm_neg]
        have hgt := hsep x hx y hy hxy
        linarith
      have hsub : (⋃ x ∈ F, Metric.ball x (ε / 2)) ⊆ Metric.ball (0 : E) (1 + ε / 2) := by
        intro z hz
        simp only [Set.mem_iUnion, exists_prop] at hz
        rcases hz with ⟨x, hxF, hzx⟩
        rw [Metric.mem_ball, dist_zero_right]
        have h1 : ‖z - x‖ < ε / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hzx
        have h2 : ‖x‖ = 1 := hunit x hxF
        calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
          _ < 1 + ε / 2 := by linarith
      have hvol_le : volume (⋃ x ∈ F, Metric.ball x (ε / 2)) ≤ volume (Metric.ball (0 : E) (1 + ε / 2)) :=
        measure_mono hsub
      rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hvol_le
      set c_d : ℝ := Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)
      have hc_pos : 0 < c_d := by
        dsimp [c_d]
        exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) d)
          (Real.Gamma_pos_of_pos (by positivity))
      have hball : ∀ (x : E) (r : ℝ), 0 ≤ r →
          volume (Metric.ball x r) = ENNReal.ofReal (r ^ d * c_d) := by
        intro x r hr
        rw [InnerProductSpace.volume_ball x r, ENNReal.ofReal_mul (pow_nonneg hr d),
            ENNReal.ofReal_pow hr]
      have hsum_eq : ∑ x ∈ F, volume (Metric.ball x (ε / 2)) =
          ENNReal.ofReal ((F.card : ℝ) * ((ε / 2) ^ d * c_d)) := by
        have hconst : ∑ x ∈ F, volume (Metric.ball x (ε / 2)) =
            ∑ _x ∈ F, ENNReal.ofReal ((ε / 2) ^ d * c_d) :=
          Finset.sum_congr rfl (fun x _ => hball x (ε / 2) (by positivity))
        rw [hconst, Finset.sum_const, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      rw [hsum_eq, hball 0 (1 + ε / 2) (by positivity)] at hvol_le
      have hreal : (F.card : ℝ) * ((ε / 2) ^ d * c_d) ≤ (1 + ε / 2) ^ d * c_d :=
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol_le
      have hreal' : (F.card : ℝ) * (ε / 2) ^ d ≤ (1 + ε / 2) ^ d := by
        nlinarith [mul_le_mul_of_nonneg_right (le_rfl : c_d ≤ c_d) (by positivity : (0 : ℝ) ≤ 0)]
      have hpow_pos : 0 < (ε / 2) ^ d := pow_pos (by positivity) d
      rw [← le_div_iff₀ hpow_pos, ← div_pow] at hreal'
      have hdiv : (1 + ε / 2) / (ε / 2) = 1 + 2 / ε := by
        field_simp [ne_of_gt hε]; ring
      rwa [hdiv] at hreal'
    -- Step 2: Pick a maximum-cardinality `ε`-separated subset `N ⊆ S^{d-1}` using `Nat.findGreatest`
    let M : ℕ := Nat.floor ((1 + 2 / ε) ^ d)
    have h_card_le_M : ∀ F : Finset E, IsSep F → F.card ≤ M := by
      intro F hF
      exact Nat.le_floor (h_pack F hF)
    let P (k : ℕ) : Prop := ∃ F : Finset E, IsSep F ∧ F.card = k
    classical
    let k_max : ℕ := Nat.findGreatest P M
    have hP0 : P 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
    have hPk : P k_max := Nat.findGreatest_spec (Nat.zero_le M) hP0
    rcases hPk with ⟨N, ⟨hN_unit, hN_sep⟩, hN_card⟩
    refine ⟨N, hN_unit, ?_, h_pack N ⟨hN_unit, hN_sep⟩⟩
    -- Step 3: Maximality implies `N` is an `ε`-net of `S^{d-1}`
    intro u hu
    by_contra hfar
    push Not at hfar
    have hu_not_mem : u ∉ N := by
      intro hmem
      have := hfar u hmem
      rw [sub_self, norm_zero] at this
      linarith
    let N' : Finset E := insert u N
    have hN'_sep : IsSep N' := by
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxN
        · exact hu
        · exact hN_unit x hxN
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with rfl | hxN <;>
        rcases Finset.mem_insert.mp hy with rfl | hyN
        · exact absurd rfl hxy
        · exact hfar y hyN
        · rw [norm_sub_rev]; exact hfar x hxN
        · exact hN_sep x hxN y hyN hxy
    have hN'_card : N'.card = k_max + 1 := by
      rw [Finset.card_insert_of_notMem hu_not_mem, hN_card]
    have hleM : k_max + 1 ≤ M := by
      rw [← hN'_card]; exact h_card_le_M N' hN'_sep
    have hPk1 : P (k_max + 1) := ⟨N', hN'_sep, hN'_card⟩
    have hle := Nat.le_findGreatest hleM hPk1
    omega
  · -- Trivial space `E`: no vector has norm `1`, so `N = ∅` works
    have : Subsingleton E := not_nontrivial_iff_subsingleton.mp hnt
    refine ⟨∅, by simp, ?_, by simp; positivity⟩
    intro u hu
    have : u = 0 := Subsingleton.elim u 0
    rw [this, norm_zero] at hu
    norm_num at hu

end Research107
