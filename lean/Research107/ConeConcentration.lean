import Research107.GaussianModel
import Research107.Concentration
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators InnerProductSpace ENNReal NNReal Classical

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Stage 3.1: Elementary Jensen for `exp` & Measurability of Active Cones -/

/-- Self-contained 5-line Jensen's inequality for `exp` on any probability measure `P`:
if `f` and `exp ∘ f` are integrable, then `exp (∫ x, f x ∂P) ≤ ∫ x, exp (f x) ∂P`. -/
lemma exp_integral_le_integral_exp {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Integrable f P) (hexp : Integrable (fun x => Real.exp (f x)) P) :
    Real.exp (∫ x, f x ∂P) ≤ ∫ x, Real.exp (f x) ∂P := by
  set m := ∫ x, f x ∂P
  have hpt : ∀ x, Real.exp m + Real.exp m * (f x - m) ≤ Real.exp (f x) := by
    intro x
    have h1 := Real.add_one_le_exp (f x - m)
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos m))
    rw [← Real.exp_add] at h2
    have h3 : m + (f x - m) = f x := by ring
    rw [h3] at h2
    linarith
  have hsub_int : Integrable (fun x => f x - m) P := hf.sub (integrable_const m)
  have hmul_int : Integrable (fun x => Real.exp m * (f x - m)) P := hsub_int.const_mul (Real.exp m)
  have hint_lhs : Integrable (fun x => Real.exp m + Real.exp m * (f x - m)) P :=
    (integrable_const (Real.exp m)).add hmul_int
  have hle := integral_mono hint_lhs hexp hpt
  rw [integral_add (integrable_const (Real.exp m)) hmul_int,
      integral_const, integral_const_mul, integral_sub hf (integrable_const m),
      integral_const, probReal_univ, one_smul, one_smul] at hle
  have hsub0 : (∫ x, f x ∂P) - m = 0 := sub_self m
  rw [hsub0, mul_zero, add_zero] at hle
  exact hle

/-- Every strict active cone `activeCone β_star j` is open, hence Borel measurable. -/
lemma measurableSet_activeCone {r : ℕ} (β_star : Fin r → E) (j : Fin r) :
    MeasurableSet (activeCone β_star j) := by
  have heq : activeCone β_star j =
      ⋂ k ∈ Finset.univ.filter (fun k : Fin r => k ≠ j),
        {a : E | ⟪a, β_star k⟫_ℝ < ⟪a, β_star j⟫_ℝ} := by
    ext a
    simp [activeCone]
  rw [heq]
  refine Finset.measurableSet_biInter _ (fun k _ => ?_)
  exact (isOpen_lt (continuous_id.inner continuous_const)
    (continuous_id.inner continuous_const)).measurableSet

/-- Population cone L1 norm `μ_j(u) = E_{a ~ N(0, I_d)}[1_{C_j^*}(a) |⟪a, u⟫|]`. -/
noncomputable def popConeNorm {r : ℕ} (β_star : Fin r → E) (j : Fin r) (u : E) : ℝ :=
  ∫ a : E, (if a ∈ activeCone β_star j then |⟪a, u⟫_ℝ| else 0) ∂(stdGaussian E)

/-! ### Stage 3.2: Lemma 4.1 — True Gaussian Sub-Gaussian MGF & Chernoff Tail -/

/-- Integrability of `exp (lam * (if a ∈ C then |⟪a, u⟫| else 0))` under `stdGaussian E`. -/
private lemma integrable_exp_indicator_abs_inner
    (C : Set E) (hC : MeasurableSet C) {u : E} (hu : ‖u‖ = 1) (lam : ℝ) :
    Integrable (fun a : E => Real.exp (lam * (if a ∈ C then |⟪a, u⟫_ℝ| else 0))) (stdGaussian E) := by
  have hinner_meas : Measurable (fun a : E => ⟪a, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hmeas_Y : Measurable (fun a : E => if a ∈ C then |⟪a, u⟫_ℝ| else 0) :=
    Measurable.ite hC (continuous_abs.measurable.comp hinner_meas) measurable_const
  have hdom_int : Integrable (fun a : E =>
      Real.exp (|lam| * ⟪a, u⟫_ℝ) + Real.exp (-|lam| * ⟪a, u⟫_ℝ)) (stdGaussian E) := by
    have h1 : Integrable (fun a : E => Real.exp (|lam| * ⟪a, u⟫_ℝ)) (stdGaussian E) := by
      have hg : Integrable (fun z : ℝ => Real.exp (|lam| * z))
          ((stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ)) := by
        rw [stdGaussian_map_inner_unit hu]
        exact integrable_exp_mul_gaussianReal (μ := 0) (v := 1) |lam|
      exact (integrable_map_measure (g := fun z : ℝ => Real.exp (|lam| * z))
        (by fun_prop) hinner_meas.aemeasurable).mp hg
    have h2 : Integrable (fun a : E => Real.exp (-|lam| * ⟪a, u⟫_ℝ)) (stdGaussian E) := by
      have hg : Integrable (fun z : ℝ => Real.exp (-|lam| * z))
          ((stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ)) := by
        rw [stdGaussian_map_inner_unit hu]
        exact integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-|lam|)
      exact (integrable_map_measure (g := fun z : ℝ => Real.exp (-|lam| * z))
        (by fun_prop) hinner_meas.aemeasurable).mp hg
    exact h1.add h2
  refine hdom_int.mono' (Real.measurable_exp.comp (hmeas_Y.const_mul lam)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hY_le : (if a ∈ C then |⟪a, u⟫_ℝ| else 0) ≤ |⟪a, u⟫_ℝ| := by
    split_ifs <;> [exact le_rfl; exact abs_nonneg _]
  have hY_nn : 0 ≤ (if a ∈ C then |⟪a, u⟫_ℝ| else 0) := by
    split_ifs <;> [exact abs_nonneg _; exact le_rfl]
  have hexp_le : lam * (if a ∈ C then |⟪a, u⟫_ℝ| else 0) ≤ |lam| * |⟪a, u⟫_ℝ| := by
    calc lam * (if a ∈ C then |⟪a, u⟫_ℝ| else 0)
        ≤ |lam| * (if a ∈ C then |⟪a, u⟫_ℝ| else 0) := mul_le_mul_of_nonneg_right (le_abs_self _) hY_nn
      _ ≤ |lam| * |⟪a, u⟫_ℝ| := mul_le_mul_of_nonneg_left hY_le (abs_nonneg _)
  rcases le_or_gt 0 ⟪a, u⟫_ℝ with hz | hz
  · have hle' : lam * (if a ∈ C then |⟪a, u⟫_ℝ| else 0) ≤ |lam| * ⟪a, u⟫_ℝ := by
      calc lam * (if a ∈ C then |⟪a, u⟫_ℝ| else 0) ≤ |lam| * |⟪a, u⟫_ℝ| := hexp_le
        _ = |lam| * ⟪a, u⟫_ℝ := by rw [abs_of_nonneg hz]
    exact le_trans (Real.exp_le_exp.mpr hle') (le_add_of_nonneg_right (le_of_lt (Real.exp_pos _)))
  · have hle' : lam * (if a ∈ C then |⟪a, u⟫_ℝ| else 0) ≤ -|lam| * ⟪a, u⟫_ℝ := by
      calc lam * (if a ∈ C then |⟪a, u⟫_ℝ| else 0) ≤ |lam| * |⟪a, u⟫_ℝ| := hexp_le
        _ = |lam| * -⟪a, u⟫_ℝ := by rw [abs_of_neg hz]
        _ = -|lam| * ⟪a, u⟫_ℝ := by ring
    exact le_trans (Real.exp_le_exp.mpr hle') (le_add_of_nonneg_left (le_of_lt (Real.exp_pos _)))

/-- Integrability of `if a ∈ C then |⟪a, u⟫| else 0` under `stdGaussian E`. -/
private lemma integrable_indicator_abs_inner
    (C : Set E) (hC : MeasurableSet C) {u : E} (hu : ‖u‖ = 1) :
    Integrable (fun a : E => if a ∈ C then |⟪a, u⟫_ℝ| else 0) (stdGaussian E) := by
  have hinner_meas : Measurable (fun a : E => ⟪a, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hmeas_Y : Measurable (fun a : E => if a ∈ C then |⟪a, u⟫_ℝ| else 0) :=
    Measurable.ite hC (continuous_abs.measurable.comp hinner_meas) measurable_const
  have hdom : Integrable (fun a : E => Real.exp (1 * (if a ∈ C then |⟪a, u⟫_ℝ| else 0))) (stdGaussian E) :=
    integrable_exp_indicator_abs_inner C hC hu 1
  refine hdom.mono' hmeas_Y.aestronglyMeasurable (Filter.Eventually.of_forall fun a => ?_)
  have hY_nn : 0 ≤ (if a ∈ C then |⟪a, u⟫_ℝ| else 0) := by
    split_ifs <;> [exact abs_nonneg _; exact le_rfl]
  rw [Real.norm_eq_abs, abs_of_nonneg hY_nn, one_mul]
  linarith [Real.add_one_le_exp (if a ∈ C then |⟪a, u⟫_ℝ| else 0)]

/-- **Lemma 4.1 (True Gaussian Sub-Gaussian MGF Bound)**:
For any measurable cone/set `C : Set E`, any unit vector `u` (`‖u‖ = 1`), and any `lam : ℝ`,
setting `Y a = 1_C(a) |⟪a, u⟫|` and `μ = E[Y]`:
`mgf (Y - μ) (stdGaussian E) lam ≤ exp (lam ^ 2)`. -/
theorem lemma41_gaussian_mgf
    (C : Set E) (hC : MeasurableSet C) {u : E} (hu : ‖u‖ = 1) (lam : ℝ) :
    let Y : E → ℝ := fun a => if a ∈ C then |⟪a, u⟫_ℝ| else 0
    let μ : ℝ := ∫ a, Y a ∂(stdGaussian E)
    Integrable (fun a => Real.exp (lam * (Y a - μ))) (stdGaussian E) ∧
    mgf (fun a => Y a - μ) (stdGaussian E) lam ≤ Real.exp (lam ^ 2) := by
  intro Y μ
  have hY_int : Integrable Y (stdGaussian E) := integrable_indicator_abs_inner C hC hu
  have hexp_pos : Integrable (fun a => Real.exp (lam * Y a)) (stdGaussian E) :=
    integrable_exp_indicator_abs_inner C hC hu lam
  have hexp_neg : Integrable (fun a => Real.exp (-lam * Y a)) (stdGaussian E) :=
    integrable_exp_indicator_abs_inner C hC hu (-lam)
  have hfactor : (fun a => Real.exp (lam * (Y a - μ))) =
      (fun a => Real.exp (-(lam * μ)) * Real.exp (lam * Y a)) := by
    ext a; rw [← Real.exp_add]; congr 1; ring
  have hint_centered : Integrable (fun a => Real.exp (lam * (Y a - μ))) (stdGaussian E) := by
    rw [hfactor]; exact hexp_pos.const_mul _
  refine ⟨hint_centered, ?_⟩
  -- Step 1: Jensen's inequality `exp (-lam * μ) ≤ ∫ a', exp (-lam * Y a') ∂P`
  have hjensen : Real.exp (-(lam * μ)) ≤ ∫ a', Real.exp (-lam * Y a') ∂(stdGaussian E) := by
    have hmean : -(lam * μ) = ∫ a', (-lam * Y a') ∂(stdGaussian E) := by
      rw [integral_const_mul]; dsimp [μ]; ring
    rw [hmean]
    exact exp_integral_le_integral_exp (hY_int.const_mul (-lam)) hexp_neg
  -- Step 2: Product representation `mgf ≤ ∫ (a, a'), exp (lam * (Y a - Y a')) ∂(P × P)`
  have hmgf_le_prod : mgf (fun a => Y a - μ) (stdGaussian E) lam ≤
      ∫ p : E × E, Real.exp (lam * (Y p.1 - Y p.2)) ∂((stdGaussian E).prod (stdGaussian E)) := by
    unfold mgf
    rw [hfactor, integral_const_mul]
    have hnn : 0 ≤ ∫ a, Real.exp (lam * Y a) ∂(stdGaussian E) :=
      integral_nonneg (fun _ => le_of_lt (Real.exp_pos _))
    calc Real.exp (-(lam * μ)) * ∫ a, Real.exp (lam * Y a) ∂(stdGaussian E)
        ≤ (∫ a', Real.exp (-lam * Y a') ∂(stdGaussian E)) *
            (∫ a, Real.exp (lam * Y a) ∂(stdGaussian E)) :=
          mul_le_mul_of_nonneg_right hjensen hnn
      _ = (∫ a, Real.exp (lam * Y a) ∂(stdGaussian E)) *
            (∫ a', Real.exp (-lam * Y a') ∂(stdGaussian E)) := mul_comm _ _
      _ = ∫ p : E × E, Real.exp (lam * Y p.1) * Real.exp (-lam * Y p.2)
            ∂((stdGaussian E).prod (stdGaussian E)) := (integral_prod_mul _ _).symm
      _ = ∫ p : E × E, Real.exp (lam * (Y p.1 - Y p.2))
            ∂((stdGaussian E).prod (stdGaussian E)) := by
          congr 1; ext p; rw [← Real.exp_add]; congr 1; ring
  -- Step 3: Symmetrize `exp (lam * (Y p.1 - Y p.2))` into `cosh (lam * (Y p.1 - Y p.2))` via `Prod.swap`
  have h_prod_int : Integrable (fun p : E × E => Real.exp (lam * (Y p.1 - Y p.2)))
      ((stdGaussian E).prod (stdGaussian E)) := by
    have heq : (fun p : E × E => Real.exp (lam * (Y p.1 - Y p.2))) =
        (fun p : E × E => Real.exp (lam * Y p.1) * Real.exp (-lam * Y p.2)) := by
      ext p; rw [← Real.exp_add]; congr 1; ring
    rw [heq]
    exact hexp_pos.mul_prod hexp_neg
  have h_prod_int_neg : Integrable (fun p : E × E => Real.exp (-(lam * (Y p.1 - Y p.2))))
      ((stdGaussian E).prod (stdGaussian E)) := by
    have heq : (fun p : E × E => Real.exp (-(lam * (Y p.1 - Y p.2)))) =
        (fun p : E × E => Real.exp (-lam * Y p.1) * Real.exp (lam * Y p.2)) := by
      ext p; rw [← Real.exp_add]; congr 1; ring
    rw [heq]
    exact hexp_neg.mul_prod hexp_pos
  have h_swap_eq :
      ∫ p : E × E, Real.exp (lam * (Y p.1 - Y p.2)) ∂((stdGaussian E).prod (stdGaussian E)) =
      ∫ p : E × E, Real.exp (-(lam * (Y p.1 - Y p.2))) ∂((stdGaussian E).prod (stdGaussian E)) := by
    have hsw : ((stdGaussian E).prod (stdGaussian E)).map Prod.swap =
        (stdGaussian E).prod (stdGaussian E) := Measure.prod_swap
    have haesm : AEStronglyMeasurable (fun p : E × E => Real.exp (lam * (Y p.1 - Y p.2)))
        (((stdGaussian E).prod (stdGaussian E)).map Prod.swap) := by
      rw [hsw]; exact h_prod_int.aestronglyMeasurable
    conv_lhs => rw [← hsw]
    rw [integral_map measurable_swap.aemeasurable haesm]
    congr 1; ext ⟨a, a'⟩; simp only [Prod.swap_prod_mk]; congr 1; ring
  have h_cosh_eq :
      ∫ p : E × E, Real.exp (lam * (Y p.1 - Y p.2)) ∂((stdGaussian E).prod (stdGaussian E)) =
      ∫ p : E × E, Real.cosh (lam * (Y p.1 - Y p.2)) ∂((stdGaussian E).prod (stdGaussian E)) := by
    have havg : (fun p : E × E => Real.cosh (lam * (Y p.1 - Y p.2))) =
        (fun p : E × E => (Real.exp (lam * (Y p.1 - Y p.2)) + Real.exp (-(lam * (Y p.1 - Y p.2)))) / 2) := by
      ext p; exact Real.cosh_eq _
    rw [havg, integral_div, integral_add h_prod_int h_prod_int_neg, ← h_swap_eq]
    ring
  -- Step 4: Apply our Phase II `lemma41_cosh_domination` + `integral_cosh_mul_gaussianReal` + `lemma41_two_exp_sub_one_le_exp_two`
  have hcosh_int_1d : Integrable (fun a : E => Real.cosh (lam * ⟪a, u⟫_ℝ)) (stdGaussian E) := by
    have hinner_meas : Measurable (fun a : E => ⟪a, u⟫_ℝ) :=
      (continuous_id.inner continuous_const).measurable
    have heq : (fun a : E => Real.cosh (lam * ⟪a, u⟫_ℝ)) =
        (fun a : E => (Real.exp (lam * ⟪a, u⟫_ℝ) + Real.exp (-lam * ⟪a, u⟫_ℝ)) / 2) := by
      ext a; rw [Real.cosh_eq]; congr 2; ring
    rw [heq]
    have h1 : Integrable (fun a : E => Real.exp (lam * ⟪a, u⟫_ℝ)) (stdGaussian E) := by
      have hg : Integrable (fun z : ℝ => Real.exp (lam * z))
          ((stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ)) := by
        rw [stdGaussian_map_inner_unit hu]
        exact integrable_exp_mul_gaussianReal (μ := 0) (v := 1) lam
      exact (integrable_map_measure (g := fun z : ℝ => Real.exp (lam * z))
        (by fun_prop) hinner_meas.aemeasurable).mp hg
    have h2 : Integrable (fun a : E => Real.exp (-lam * ⟪a, u⟫_ℝ)) (stdGaussian E) := by
      have hg : Integrable (fun z : ℝ => Real.exp (-lam * z))
          ((stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ)) := by
        rw [stdGaussian_map_inner_unit hu]
        exact integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-lam)
      exact (integrable_map_measure (g := fun z : ℝ => Real.exp (-lam * z))
        (by fun_prop) hinner_meas.aemeasurable).mp hg
    exact (h1.add h2).div_const 2
  have hcosh_val : ∫ a : E, Real.cosh (lam * ⟪a, u⟫_ℝ) ∂(stdGaussian E) = Real.exp (lam ^ 2 / 2) := by
    have hinner_meas : Measurable (fun a : E => ⟪a, u⟫_ℝ) :=
      (continuous_id.inner continuous_const).measurable
    have hmap : ∫ a : E, Real.cosh (lam * ⟪a, u⟫_ℝ) ∂(stdGaussian E) =
        ∫ z : ℝ, Real.cosh (lam * z) ∂(gaussianReal 0 1) := by
      rw [← stdGaussian_map_inner_unit hu,
          integral_map hinner_meas.aemeasurable (by fun_prop)]
    rw [hmap, integral_cosh_mul_gaussianReal]
  have hdom_prod_int : Integrable
      (fun p : E × E => Real.cosh (lam * ⟪p.1, u⟫_ℝ) + Real.cosh (lam * ⟪p.2, u⟫_ℝ) - 1)
      ((stdGaussian E).prod (stdGaussian E)) := by
    have h1 : Integrable (fun p : E × E => Real.cosh (lam * ⟪p.1, u⟫_ℝ)) ((stdGaussian E).prod (stdGaussian E)) :=
      hcosh_int_1d.comp_fst (stdGaussian E)
    have h2 : Integrable (fun p : E × E => Real.cosh (lam * ⟪p.2, u⟫_ℝ)) ((stdGaussian E).prod (stdGaussian E)) :=
      hcosh_int_1d.comp_snd (stdGaussian E)
    exact (h1.add h2).sub (integrable_const 1)
  have hcosh_prod_int : Integrable (fun p : E × E => Real.cosh (lam * (Y p.1 - Y p.2)))
      ((stdGaussian E).prod (stdGaussian E)) := by
    have havg : (fun p : E × E => Real.cosh (lam * (Y p.1 - Y p.2))) =
        (fun p : E × E => (Real.exp (lam * (Y p.1 - Y p.2)) + Real.exp (-(lam * (Y p.1 - Y p.2)))) / 2) := by
      ext p; exact Real.cosh_eq _
    rw [havg]
    exact (h_prod_int.add h_prod_int_neg).div_const 2
  have h_pt_dom : ∀ p : E × E,
      Real.cosh (lam * (Y p.1 - Y p.2)) ≤
      Real.cosh (lam * ⟪p.1, u⟫_ℝ) + Real.cosh (lam * ⟪p.2, u⟫_ℝ) - 1 := by
    intro p
    have hy1_nn : 0 ≤ Y p.1 := by dsimp [Y]; split_ifs <;> [exact abs_nonneg _; exact le_rfl]
    have hy2_nn : 0 ≤ Y p.2 := by dsimp [Y]; split_ifs <;> [exact abs_nonneg _; exact le_rfl]
    have hy1_le : Y p.1 ≤ |⟪p.1, u⟫_ℝ| := by dsimp [Y]; split_ifs <;> [exact le_rfl; exact abs_nonneg _]
    have hy2_le : Y p.2 ≤ |⟪p.2, u⟫_ℝ| := by dsimp [Y]; split_ifs <;> [exact le_rfl; exact abs_nonneg _]
    exact lemma41_cosh_domination hy1_nn hy2_nn hy1_le hy2_le lam
  have h_dom_eval :
      ∫ p : E × E, (Real.cosh (lam * ⟪p.1, u⟫_ℝ) + Real.cosh (lam * ⟪p.2, u⟫_ℝ) - 1)
        ∂((stdGaussian E).prod (stdGaussian E)) = 2 * Real.exp (lam ^ 2 / 2) - 1 := by
    have h1 : Integrable (fun p : E × E => Real.cosh (lam * ⟪p.1, u⟫_ℝ)) ((stdGaussian E).prod (stdGaussian E)) :=
      hcosh_int_1d.comp_fst (stdGaussian E)
    have h2 : Integrable (fun p : E × E => Real.cosh (lam * ⟪p.2, u⟫_ℝ)) ((stdGaussian E).prod (stdGaussian E)) :=
      hcosh_int_1d.comp_snd (stdGaussian E)
    have h12 : Integrable (fun p : E × E => Real.cosh (lam * ⟪p.1, u⟫_ℝ) + Real.cosh (lam * ⟪p.2, u⟫_ℝ))
        ((stdGaussian E).prod (stdGaussian E)) := h1.add h2
    rw [integral_sub h12 (integrable_const 1), integral_add h1 h2, integral_const,
        probReal_univ, one_smul]
    have hf1 : ∫ p : E × E, Real.cosh (lam * ⟪p.1, u⟫_ℝ) ∂((stdGaussian E).prod (stdGaussian E)) =
        Real.exp (lam ^ 2 / 2) := by
      have hmul : (fun p : E × E => Real.cosh (lam * ⟪p.1, u⟫_ℝ)) =
          (fun p : E × E => Real.cosh (lam * ⟪p.1, u⟫_ℝ) * (1 : ℝ)) := by ext; simp
      rw [hmul, integral_prod_mul (f := fun a : E => Real.cosh (lam * ⟪a, u⟫_ℝ)) (g := fun _ : E => (1 : ℝ)),
          integral_const, probReal_univ, one_smul, mul_one, hcosh_val]
    have hf2 : ∫ p : E × E, Real.cosh (lam * ⟪p.2, u⟫_ℝ) ∂((stdGaussian E).prod (stdGaussian E)) =
        Real.exp (lam ^ 2 / 2) := by
      have hmul : (fun p : E × E => Real.cosh (lam * ⟪p.2, u⟫_ℝ)) =
          (fun p : E × E => (1 : ℝ) * Real.cosh (lam * ⟪p.2, u⟫_ℝ)) := by ext; simp
      rw [hmul, integral_prod_mul (f := fun _ : E => (1 : ℝ)) (g := fun a : E => Real.cosh (lam * ⟪a, u⟫_ℝ)),
          integral_const, probReal_univ, one_smul, one_mul, hcosh_val]
    rw [hf1, hf2]; ring
  calc mgf (fun a => Y a - μ) (stdGaussian E) lam
      ≤ ∫ p : E × E, Real.exp (lam * (Y p.1 - Y p.2)) ∂((stdGaussian E).prod (stdGaussian E)) := hmgf_le_prod
    _ = ∫ p : E × E, Real.cosh (lam * (Y p.1 - Y p.2)) ∂((stdGaussian E).prod (stdGaussian E)) := h_cosh_eq
    _ ≤ ∫ p : E × E, (Real.cosh (lam * ⟪p.1, u⟫_ℝ) + Real.cosh (lam * ⟪p.2, u⟫_ℝ) - 1)
          ∂((stdGaussian E).prod (stdGaussian E)) := integral_mono hcosh_prod_int hdom_prod_int h_pt_dom
    _ = 2 * Real.exp (lam ^ 2 / 2) - 1 := h_dom_eval
    _ ≤ Real.exp (2 * (lam ^ 2 / 2)) := lemma41_two_exp_sub_one_le_exp_two (lam ^ 2 / 2)
    _ = Real.exp (lam ^ 2) := by congr 1; ring

/-- **Lemma 4.1 (Two-Sided Empirical Tail for Signed Cone Sums)**:
For any measurable `C : Set E`, unit vector `u` (`‖u‖ = 1`), signs `s : Fin m → ℝ` (`|s i| ≤ 1`),
and `t > 0`, let `S(a) = (1/m) ∑ i, (if a i ∈ C then s i * |⟪a i, u⟫| else 0)` and
`μ_emp = ((1/m) ∑ i, s i) * ∫ x, (if x ∈ C then |⟪x, u⟫| else 0) ∂(stdGaussian E)`.
Then BOTH tails satisfy `≤ exp (-m * t^2 / 4)`. -/
theorem lemma41_empirical_tails
    {m : ℕ} (hm : 0 < m) (C : Set E) (hC : MeasurableSet C)
    (s : Fin m → ℝ) (hs : ∀ i : Fin m, |s i| ≤ 1)
    {u : E} (hu : ‖u‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    let S : (Fin m → E) → ℝ := fun a =>
      (1 / (m : ℝ)) * ∑ i : Fin m, if a i ∈ C then s i * |⟪a i, u⟫_ℝ| else 0
    let μ₀ : ℝ := ∫ x : E, (if x ∈ C then |⟪x, u⟫_ℝ| else 0) ∂(stdGaussian E)
    let μ_emp : ℝ := ((1 / (m : ℝ)) * ∑ i : Fin m, s i) * μ₀
    iidStdGaussian E m {a | S a ≤ μ_emp - t} ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * t ^ 2 / 4)) ∧
    iidStdGaussian E m {a | μ_emp + t ≤ S a} ≤ ENNReal.ofReal (Real.exp (-(m : ℝ) * t ^ 2 / 4)) := by
  intro S μ₀ μ_emp
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  let Y₀ : E → ℝ := fun x => if x ∈ C then |⟪x, u⟫_ℝ| else 0
  let Z : Fin m → (Fin m → E) → ℝ := fun i a => s i * (Y₀ (a i) - μ₀)
  have hinner_meas : Measurable (fun x : E => ⟪x, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hY₀_meas : Measurable Y₀ := Measurable.ite hC (continuous_abs.measurable.comp hinner_meas) measurable_const
  have hZ_meas : ∀ i : Fin m, Measurable (Z i) :=
    fun i => ((hY₀_meas.sub measurable_const).const_mul (s i)).comp (measurable_pi_apply i)
  have h_indep : iIndepFun Z (iidStdGaussian E m) := by
    unfold iidStdGaussian
    exact iIndepFun_pi (fun i => ((hY₀_meas.sub measurable_const).const_mul (s i)).aemeasurable)
  -- For ANY `θ : ℝ`, `mgf (∑ i, Z i) ≤ exp (m * θ^2)`
  have h_mgf_bound : ∀ θ : ℝ,
      Integrable (fun a => Real.exp (θ * ∑ i : Fin m, Z i a)) (iidStdGaussian E m) ∧
      mgf (fun a => ∑ i : Fin m, Z i a) (iidStdGaussian E m) θ ≤ Real.exp ((m : ℝ) * θ ^ 2) := by
    intro θ
    have h_each : ∀ i : Fin m,
        Integrable (fun a => Real.exp (θ * Z i a)) (iidStdGaussian E m) ∧
        mgf (Z i) (iidStdGaussian E m) θ ≤ Real.exp (θ ^ 2) := by
      intro i
      have h1 := lemma41_gaussian_mgf C hC hu (θ * s i)
      have haesm : AEStronglyMeasurable (fun x : E => Real.exp ((θ * s i) * (Y₀ x - μ₀)))
          ((iidStdGaussian E m).map (fun a : Fin m → E => a i)) := by
        rw [iidStdGaussian_map_eval]; exact h1.1.aestronglyMeasurable
      have hcomp_eq : (fun a : Fin m → E => Real.exp (θ * Z i a)) =
          (fun x : E => Real.exp ((θ * s i) * (Y₀ x - μ₀))) ∘ (fun a : Fin m → E => a i) := by
        ext a; dsimp [Z, Y₀]; congr 1; ring
      have h_int : Integrable (fun a => Real.exp (θ * Z i a)) (iidStdGaussian E m) := by
        rw [hcomp_eq]
        have hm1 : Integrable (fun x : E => Real.exp ((θ * s i) * (Y₀ x - μ₀)))
            ((iidStdGaussian E m).map (fun a : Fin m → E => a i)) := by
          rw [iidStdGaussian_map_eval]; exact h1.1
        exact (integrable_map_measure (g := fun x : E => Real.exp ((θ * s i) * (Y₀ x - μ₀)))
          haesm (measurable_pi_apply i).aemeasurable).mp hm1
      have h_mgf_eq : mgf (Z i) (iidStdGaussian E m) θ =
          mgf (fun x => Y₀ x - μ₀) (stdGaussian E) (θ * s i) := by
        unfold mgf
        have hstep : ∫ a : Fin m → E, Real.exp (θ * Z i a) ∂(iidStdGaussian E m) =
            ∫ x : E, Real.exp ((θ * s i) * (Y₀ x - μ₀)) ∂((iidStdGaussian E m).map (fun a : Fin m → E => a i)) := by
          rw [integral_map (φ := fun a : Fin m → E => a i)
              (f := fun x : E => Real.exp ((θ * s i) * (Y₀ x - μ₀)))
              (measurable_pi_apply i).aemeasurable haesm]
          refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
          dsimp [Z]; congr 1; ring
        rw [hstep, iidStdGaussian_map_eval]
      have hsq : (θ * s i) ^ 2 ≤ θ ^ 2 := by
        have hsi2 : (s i) ^ 2 ≤ 1 := by
          have := hs i
          nlinarith [sq_abs (s i), abs_nonneg (s i)]
        have : (θ * s i) ^ 2 = θ ^ 2 * (s i) ^ 2 := by ring
        nlinarith [sq_nonneg θ]
      exact ⟨h_int, by rw [h_mgf_eq]; exact le_trans h1.2 (Real.exp_le_exp.mpr hsq)⟩
    have hint_sum : Integrable (fun a => Real.exp (θ * ∑ i : Fin m, Z i a)) (iidStdGaussian E m) := by
      simpa using h_indep.integrable_exp_mul_sum hZ_meas (s := Finset.univ) (fun i _ => (h_each i).1)
    have hprod := h_indep.mgf_sum hZ_meas Finset.univ (t := θ)
    have hfun : (∑ i : Fin m, Z i) = (fun a => ∑ i : Fin m, Z i a) := by
      ext a; simp
    rw [hfun] at hprod
    have hprod_le : ∏ i : Fin m, mgf (Z i) (iidStdGaussian E m) θ ≤ ∏ _i : Fin m, Real.exp (θ ^ 2) :=
      Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => (h_each i).2)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul] at hprod_le
    exact ⟨hint_sum, by rw [hprod]; exact hprod_le⟩
  -- Relate `S a - μ_emp` to `(1 / m) * ∑ i, Z i a`
  have h_diff_eq : ∀ a : Fin m → E, (m : ℝ) * (S a - μ_emp) = ∑ i : Fin m, Z i a := by
    intro a
    dsimp [S, μ_emp, Z]
    have h1 : ∀ i : Fin m, (if a i ∈ C then s i * |⟪a i, u⟫_ℝ| else 0) = s i * Y₀ (a i) := by
      intro i; dsimp [Y₀]; split_ifs <;> ring
    simp_rw [h1, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    field_simp [ne_of_gt hm_pos]
  constructor
  · -- Lower tail: `S a ≤ μ_emp - t ↔ ∑ i, Z i a ≤ -(m * t)`, use `measure_le_le_exp_mul_mgf` at `θ = -(t/2)`
    have hset : {a : Fin m → E | S a ≤ μ_emp - t} =
        {a : Fin m → E | ∑ i : Fin m, Z i a ≤ -((m : ℝ) * t)} := by
      ext a; simp only [Set.mem_ofPred_eq]
      constructor <;> intro h
      · have := mul_le_mul_of_nonneg_left (show S a - μ_emp ≤ -t by linarith) (le_of_lt hm_pos)
        linarith [h_diff_eq a]
      · have : (m : ℝ) * (S a - μ_emp) ≤ (m : ℝ) * (-t) := by linarith [h_diff_eq a]
        have := le_of_mul_le_mul_left this hm_pos
        linarith
    rw [hset]
    obtain ⟨hint, hmgf⟩ := h_mgf_bound (-(t / 2))
    have htail := measure_le_le_exp_mul_mgf (μ := iidStdGaussian E m)
      (X := fun a => ∑ i : Fin m, Z i a) (-((m : ℝ) * t)) (by linarith : -(t / 2) ≤ 0) hint
    rw [← ENNReal.ofReal_toReal (measure_ne_top (iidStdGaussian E m) _)]
    refine ENNReal.ofReal_le_ofReal (le_trans htail ?_)
    calc Real.exp (-(-(t / 2)) * -((m : ℝ) * t)) * mgf (fun a => ∑ i, Z i a) (iidStdGaussian E m) (-(t / 2))
        ≤ Real.exp (-(-(t / 2)) * -((m : ℝ) * t)) * Real.exp ((m : ℝ) * (-(t / 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left hmgf (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(t / 2) * (m : ℝ) * t + (m : ℝ) * (t / 2) ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp (-(m : ℝ) * t ^ 2 / 4) := lemma41_chernoff_opt (m : ℝ) t
  · -- Upper tail: `μ_emp + t ≤ S a ↔ m * t ≤ ∑ i, Z i a`, use `measure_ge_le_exp_mul_mgf` at `θ = t/2`
    have hset : {a : Fin m → E | μ_emp + t ≤ S a} =
        {a : Fin m → E | (m : ℝ) * t ≤ ∑ i : Fin m, Z i a} := by
      ext a; simp only [Set.mem_ofPred_eq]
      constructor <;> intro h
      · have := mul_le_mul_of_nonneg_left (show t ≤ S a - μ_emp by linarith) (le_of_lt hm_pos)
        linarith [h_diff_eq a]
      · have : (m : ℝ) * t ≤ (m : ℝ) * (S a - μ_emp) := by linarith [h_diff_eq a]
        have := le_of_mul_le_mul_left this hm_pos
        linarith
    rw [hset]
    obtain ⟨hint, hmgf⟩ := h_mgf_bound (t / 2)
    have htail := measure_ge_le_exp_mul_mgf (μ := iidStdGaussian E m)
      (X := fun a => ∑ i : Fin m, Z i a) ((m : ℝ) * t) (by linarith : (0 : ℝ) ≤ t / 2) hint
    rw [← ENNReal.ofReal_toReal (measure_ne_top (iidStdGaussian E m) _)]
    refine ENNReal.ofReal_le_ofReal (le_trans htail ?_)
    calc Real.exp (-(t / 2) * ((m : ℝ) * t)) * mgf (fun a => ∑ i, Z i a) (iidStdGaussian E m) (t / 2)
        ≤ Real.exp (-(t / 2) * ((m : ℝ) * t)) * Real.exp ((m : ℝ) * (t / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left hmgf (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-(t / 2) * (m : ℝ) * t + (m : ℝ) * (t / 2) ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
      _ = Real.exp (-(m : ℝ) * t ^ 2 / 4) := lemma41_chernoff_opt (m : ℝ) t

/-! ### Stage 3.3: Lemma 4.2 — Uniform Fixed-Grid Event for Signed Cone Norms -/

/-- **Stage 3 Main Theorem (Lemma 4.2 — Fixed Finite `(γ/8)`-Net Concentration)**:
Constructs ONE fixed finite `(γ/8)`-net `N ⊆ S^{d-1}` (`|N| ≤ (1 + 16/γ)^d`) and bounds
the failure probability of the uniform net lower bound `T_j(u₀) ≥ 3γ/4` across all `(j, u₀) ∈ Fin r × N`
by `r * (1 + 16/γ)^d * exp (-m γ^2 / 64)`. -/
theorem prob_cone_net_event
    {m r : ℕ} (hm : 0 < m)
    (β_star : Fin r → E) (s : Fin m → ℝ) (hs : ∀ i : Fin m, |s i| ≤ 1)
    {γ : ℝ} (hγ : 0 < γ)
    (h_pop : ∀ (j : Fin r) (u : E), ‖u‖ = 1 →
      γ ≤ ((1 / (m : ℝ)) * ∑ i : Fin m, s i) * popConeNorm β_star j u) :
    ∃ N : Finset E,
      (∀ u₀ ∈ N, ‖u₀‖ = 1) ∧
      (∀ u : E, ‖u‖ = 1 → ∃ u₀ ∈ N, ‖u - u₀‖ ≤ γ / 8) ∧
      iidStdGaussian E m {a : Fin m → E |
        ¬ ∀ (j : Fin r), ∀ u₀ ∈ N, 3 * γ / 4 ≤ signedConeNorm a s β_star j u₀} ≤
      ENNReal.ofReal ((r : ℝ) * (1 + 16 / γ) ^ Module.finrank ℝ E *
        Real.exp (-(m : ℝ) * γ ^ 2 / 64)) := by
  obtain ⟨N, hN_unit, hN_cover, hN_card⟩ := exists_sphere_eps_net E (by linarith : 0 < γ / 8)
  have h16 : 1 + 2 / (γ / 8) = 1 + 16 / γ := by field_simp [ne_of_gt hγ]; ring
  rw [h16] at hN_card
  refine ⟨N, hN_unit, hN_cover, ?_⟩
  have hsub :
      {a : Fin m → E | ¬ ∀ (j : Fin r), ∀ u₀ ∈ N, 3 * γ / 4 ≤ signedConeNorm a s β_star j u₀} ⊆
      ⋃ j : Fin r, ⋃ u₀ ∈ N, {a : Fin m → E | signedConeNorm a s β_star j u₀ ≤ 3 * γ / 4} := by
    intro a ha
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hnot
    exact ha (fun j u₀ hu₀ => le_of_lt (hnot j u₀ hu₀))
  have h_pt : ∀ (j : Fin r) (u₀ : E), u₀ ∈ N →
      iidStdGaussian E m {a | signedConeNorm a s β_star j u₀ ≤ 3 * γ / 4} ≤
        ENNReal.ofReal (Real.exp (-(m : ℝ) * γ ^ 2 / 64)) := by
    intro j u₀ hu₀
    have hu₀_norm : ‖u₀‖ = 1 := hN_unit u₀ hu₀
    have hμ := h_pop j u₀ hu₀_norm
    have htail := (lemma41_empirical_tails hm (activeCone β_star j)
      (measurableSet_activeCone β_star j) s hs hu₀_norm (by linarith : 0 ≤ γ / 4)).1
    have hsub_pt : {a : Fin m → E | signedConeNorm a s β_star j u₀ ≤ 3 * γ / 4} ⊆
        {a : Fin m → E | signedConeNorm a s β_star j u₀ ≤
          ((1 / (m : ℝ)) * ∑ i : Fin m, s i) * popConeNorm β_star j u₀ - γ / 4} := by
      intro a ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      linarith
    have hrew : -(m : ℝ) * (γ / 4) ^ 2 / 4 = -(m : ℝ) * γ ^ 2 / 64 := by ring
    rw [hrew] at htail
    exact le_trans (measure_mono hsub_pt) htail
  calc iidStdGaussian E m {a | ¬ ∀ (j : Fin r), ∀ u₀ ∈ N, 3 * γ / 4 ≤ signedConeNorm a s β_star j u₀}
      ≤ iidStdGaussian E m (⋃ j : Fin r, ⋃ u₀ ∈ N, {a | signedConeNorm a s β_star j u₀ ≤ 3 * γ / 4}) :=
        measure_mono hsub
    _ ≤ ∑ j : Fin r, iidStdGaussian E m (⋃ u₀ ∈ N, {a | signedConeNorm a s β_star j u₀ ≤ 3 * γ / 4}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ j : Fin r, ∑ u₀ ∈ N, iidStdGaussian E m {a | signedConeNorm a s β_star j u₀ ≤ 3 * γ / 4} :=
        Finset.sum_le_sum (fun j _ => measure_biUnion_finset_le N _)
    _ ≤ ∑ _j : Fin r, ∑ _u₀ ∈ N, ENNReal.ofReal (Real.exp (-(m : ℝ) * γ ^ 2 / 64)) :=
        Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun u₀ hu₀ => h_pt j u₀ hu₀))
    _ = ENNReal.ofReal ((r : ℝ) * (N.card : ℝ) * Real.exp (-(m : ℝ) * γ ^ 2 / 64)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((r : ℝ) * (1 + 16 / γ) ^ Module.finrank ℝ E *
          Real.exp (-(m : ℝ) * γ ^ 2 / 64)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := mul_le_mul_of_nonneg_left hN_card (Nat.cast_nonneg r)
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))

/-! ### Stage 3.4: Unconditional Phase III Proof of Proposition 4.1' (50% Breakdown Converse) -/

/-- **Proposition 4.1' (Phase III Corrected & Unconditionally Machine-Checked)**:
Under oblivious corruption support `s : Fin m → ℝ` (`s i ∈ {1, -1}`) with corrupted fraction
`α > 1/2` (meaning `(1/m) ∑ i, s i = 1 - 2 α < 0`), for ANY fixed unit vector `ĥ` (`‖ĥ‖ = 1`),
the **single fixed corruption vector** `ξ(a)_i := if s i = -1 then ⟪a i, ĥ⟫ else 0` makes every
uniform translation `β̃(t) = (β₁* + t ĥ, …, β_r* + t ĥ)` (`t ∈ (0, 1]`) strictly beat `β*`
simultaneously, with failure probability at most `exp (-(2 α - 1)^2 / (2 π) * m)`.
Hence `β*` is NOT a local minimizer with probability at least `1 - exp (-(2 α - 1)^2 / (2 π) * m)`. -/
theorem proposition41_prime_breakdown_necessity
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (β_star : Fin r → E) (s : Fin m → ℝ)
    (hs_pm : ∀ i : Fin m, s i = 1 ∨ s i = -1)
    {α : ℝ} (hα : 1 / 2 < α)
    (h_frac : (1 / (m : ℝ)) * ∑ i : Fin m, s i = 1 - 2 * α)
    {hhat : E} (hh : ‖hhat‖ = 1) :
    let ξ : (Fin m → E) → Fin m → ℝ := fun a i => if s i = -1 then ⟪a i, hhat⟫_ℝ else 0
    let y : (Fin m → E) → Fin m → ℝ := fun a i => maxLinearPred hr (a i) β_star + ξ a i
    iidStdGaussian E m {a : Fin m → E |
      ¬ ∀ t : ℝ, 0 < t → t ≤ 1 →
        l1EmpiricalLoss hr a (y a) (fun j => β_star j + t • hhat) <
        l1EmpiricalLoss hr a (y a) β_star} ≤
      ENNReal.ofReal (Real.exp (-((2 * α - 1) ^ 2 / (2 * Real.pi)) * (m : ℝ))) := by
  intro ξ y
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  -- Step 1: Deterministic exact identity for uniform translation `β̃(t)`
  have h_ident : ∀ (a : Fin m → E) (t : ℝ), 0 < t → t ≤ 1 →
      l1EmpiricalLoss hr a (y a) (fun j => β_star j + t • hhat) -
      l1EmpiricalLoss hr a (y a) β_star =
      t * ((1 / (m : ℝ)) * ∑ i : Fin m, if a i ∈ (Set.univ : Set E) then s i * |⟪a i, hhat⟫_ℝ| else 0) := by
    intro a t ht0 ht1
    -- For every `i`, `maxLinearPred hr (a i) (β* + t ĥ) = maxLinearPred hr (a i) β* + t * ⟪a i, ĥ⟫`
    have hpred : ∀ i : Fin m,
        maxLinearPred hr (a i) (fun j => β_star j + t • hhat) =
        maxLinearPred hr (a i) β_star + t * ⟪a i, hhat⟫_ℝ := by
      intro i
      unfold maxLinearPred
      have hne : (Finset.univ : Finset (Fin r)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hr⟩⟩
      apply le_antisymm
      · refine Finset.sup'_le _ _ (fun j _ => ?_)
        rw [inner_add_right, real_inner_smul_right]
        have hle := Finset.le_sup' (fun k : Fin r => ⟪a i, β_star k⟫_ℝ) (Finset.mem_univ j)
        linarith
      · obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_eq_sup' hne (fun k : Fin r => ⟪a i, β_star k⟫_ℝ)
        rw [hj₀]
        have hle := Finset.le_sup' (fun k : Fin r => ⟪a i, β_star k + t • hhat⟫_ℝ) (Finset.mem_univ j₀)
        rw [inner_add_right, real_inner_smul_right] at hle
        linarith
    unfold l1EmpiricalLoss
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    have h_each : ∀ i : Fin m,
        |y a i - maxLinearPred hr (a i) (fun j => β_star j + t • hhat)| -
        |y a i - maxLinearPred hr (a i) β_star| =
        t * (s i * |⟪a i, hhat⟫_ℝ|) := by
      intro i
      dsimp [y, ξ]
      rw [hpred i]
      rcases hs_pm i with hs1 | hsm1
      · have hne : s i ≠ -1 := by linarith
        rw [if_neg hne, hs1, one_mul]
        have h1 : maxLinearPred hr (a i) β_star + 0 - (maxLinearPred hr (a i) β_star + t * ⟪a i, hhat⟫_ℝ) =
            -(t * ⟪a i, hhat⟫_ℝ) := by ring
        have h2 : maxLinearPred hr (a i) β_star + 0 - maxLinearPred hr (a i) β_star = 0 := by ring
        rw [h1, h2, abs_zero, sub_zero, abs_neg, abs_mul, abs_of_pos ht0]
      · rw [if_pos hsm1, hsm1]
        have h1 : maxLinearPred hr (a i) β_star + ⟪a i, hhat⟫_ℝ -
            (maxLinearPred hr (a i) β_star + t * ⟪a i, hhat⟫_ℝ) = (1 - t) * ⟪a i, hhat⟫_ℝ := by ring
        have h2 : maxLinearPred hr (a i) β_star + ⟪a i, hhat⟫_ℝ - maxLinearPred hr (a i) β_star =
            ⟪a i, hhat⟫_ℝ := by ring
        rw [h1, h2, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
        ring
    simp_rw [h_each, Set.mem_univ, if_true, ← Finset.mul_sum]
    ring
  -- Step 2: Apply Lemma 4.1 upper tail with `C = Set.univ` and `t = (2 α - 1) * √(2 / π) > 0`
  let S : (Fin m → E) → ℝ := fun a =>
    (1 / (m : ℝ)) * ∑ i : Fin m, if a i ∈ (Set.univ : Set E) then s i * |⟪a i, hhat⟫_ℝ| else 0
  have hsub : {a : Fin m → E |
      ¬ ∀ t : ℝ, 0 < t → t ≤ 1 →
        l1EmpiricalLoss hr a (y a) (fun j => β_star j + t • hhat) <
        l1EmpiricalLoss hr a (y a) β_star} ⊆ {a : Fin m → E | 0 ≤ S a} := by
    intro a ha
    by_contra hlt
    simp only [Set.mem_ofPred_eq, not_le] at hlt
    apply ha
    intro t ht0 ht1
    have hid := h_ident a t ht0 ht1
    have hneg : t * S a < 0 := mul_neg_of_pos_of_neg ht0 hlt
    linarith
  have hs_abs : ∀ i : Fin m, |s i| ≤ 1 := by
    intro i; rcases hs_pm i with h | h <;> simp [h]
  have hμ₀ : ∫ x : E, (if x ∈ (Set.univ : Set E) then |⟪x, hhat⟫_ℝ| else 0) ∂(stdGaussian E) =
      Real.sqrt (2 / Real.pi) := by
    simp only [Set.mem_univ, if_true]
    rw [integral_abs_inner_stdGaussian, hh, one_mul]
  set gap : ℝ := (2 * α - 1) * Real.sqrt (2 / Real.pi)
  have hgap_nn : 0 ≤ gap := mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have htail := (lemma41_empirical_tails hm (Set.univ : Set E) MeasurableSet.univ s hs_abs hh hgap_nn).2
  dsimp only at htail
  simp only [Set.mem_univ, ite_true] at htail
  have hzero : ((1 / (m : ℝ)) * ∑ i : Fin m, s i) *
      (∫ x : E, |⟪x, hhat⟫_ℝ| ∂(stdGaussian E)) + gap = 0 := by
    rw [h_frac, integral_abs_inner_stdGaussian, hh, one_mul]; dsimp [gap]; ring
  have hsub2 : {a : Fin m → E | 0 ≤ S a} ⊆
      {a : Fin m → E | ((1 / (m : ℝ)) * ∑ i : Fin m, s i) *
        (∫ x : E, |⟪x, hhat⟫_ℝ| ∂(stdGaussian E)) + gap ≤
        (1 / (m : ℝ)) * ∑ i : Fin m, s i * |⟪a i, hhat⟫_ℝ|} := by
    intro a ha
    simp only [Set.mem_ofPred_eq, S, Set.mem_univ, ite_true] at ha ⊢
    linarith
  have hexp_eq : -(m : ℝ) * gap ^ 2 / 4 = -((2 * α - 1) ^ 2 / (2 * Real.pi)) * (m : ℝ) := by
    dsimp [gap]
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
    ring
  rw [hexp_eq] at htail
  exact le_trans (measure_mono (Set.Subset.trans hsub hsub2)) htail

end Research107
