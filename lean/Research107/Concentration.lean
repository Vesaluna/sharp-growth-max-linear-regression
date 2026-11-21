import Research107.Definitions
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators InnerProductSpace

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Stage C.1: Lemma 4.1 (Exact 3-Line Sub-Gaussian MGF & Chernoff Algebra) -/

/-- Exact elementary inequality `2 e^u - 1 ≤ e^{2u}` for all `u : ℝ`. -/
lemma lemma41_two_exp_sub_one_le_exp_two (u : ℝ) :
    2 * Real.exp u - 1 ≤ Real.exp (2 * u) := by
  have h1 : Real.exp (2 * u) = Real.exp u * Real.exp u := by
    rw [two_mul, Real.exp_add]
  nlinarith [sq_nonneg (Real.exp u - 1)]

private lemma one_le_cosh_aux (x : ℝ) : 1 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have hp : 0 < Real.exp x := Real.exp_pos x
  have hmul : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hsq : 0 ≤ (Real.exp x - 1) ^ 2 := sq_nonneg _
  have h2 : 2 * Real.exp x ≤ (Real.exp x + Real.exp (-x)) * Real.exp x := by nlinarith
  nlinarith

private lemma cosh_le_cosh_of_abs_le {x y : ℝ} (h : |x| ≤ |y|) : Real.cosh x ≤ Real.cosh y := by
  have hx : Real.cosh x = Real.cosh |x| := by
    rcases le_or_gt 0 x with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, Real.cosh_neg]
  have hy : Real.cosh y = Real.cosh |y| := by
    rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, Real.cosh_neg]
  rw [hx, hy, Real.cosh_eq, Real.cosh_eq]
  set a := |y|
  set b := |x|
  have ha0 : 0 ≤ a := abs_nonneg y
  have hb0 : 0 ≤ b := abs_nonneg x
  have h1 : 0 ≤ Real.exp a - Real.exp b := sub_nonneg.mpr (Real.exp_le_exp.mpr h)
  have h2 : 0 ≤ 1 - Real.exp (-(a + b)) := by
    have : Real.exp (-(a + b)) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hid : (Real.exp a + Real.exp (-a)) - (Real.exp b + Real.exp (-b)) =
      (Real.exp a - Real.exp b) * (1 - Real.exp (-(a + b))) := by
    have he1 : Real.exp a * Real.exp (-(a + b)) = Real.exp (-b) := by
      rw [← Real.exp_add]; congr 1; ring
    have he2 : Real.exp b * Real.exp (-(a + b)) = Real.exp (-a) := by
      rw [← Real.exp_add]; congr 1; ring
    linarith [show (Real.exp a - Real.exp b) * (1 - Real.exp (-(a + b))) =
        Real.exp a - Real.exp b - Real.exp a * Real.exp (-(a + b)) + Real.exp b * Real.exp (-(a + b)) by ring]
  have hprod : 0 ≤ (Real.exp a - Real.exp b) * (1 - Real.exp (-(a + b))) := mul_nonneg h1 h2
  linarith

/-- Pointwise cosh domination for Lemma 4.1:
if `0 ≤ y ≤ |z|` and `0 ≤ y' ≤ |z'|`, then for all `λ : ℝ`,
`cosh (λ * (y - y')) ≤ cosh (λ * z) + cosh (λ * z') - 1`. -/
lemma lemma41_cosh_domination {y y' z z' : ℝ}
    (hy0 : 0 ≤ y) (hy'0 : 0 ≤ y') (hy : y ≤ |z|) (hy' : y' ≤ |z'|) (lam : ℝ) :
    Real.cosh (lam * (y - y')) ≤ Real.cosh (lam * z) + Real.cosh (lam * z') - 1 := by
  have hdiff : |y - y'| ≤ max |z| |z'| := by
    rw [abs_le]
    constructor
    · have : y' ≤ max |z| |z'| := le_trans hy' (le_max_right _ _)
      linarith
    · have : y ≤ max |z| |z'| := le_trans hy (le_max_left _ _)
      linarith
  have hmul : |lam * (y - y')| ≤ max |lam * z| |lam * z'| := by
    rw [abs_mul, abs_mul, abs_mul, ← mul_max_of_nonneg _ _ (abs_nonneg lam)]
    exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg lam)
  -- `Real.cosh` is even and increasing on `[0, ∞)`
  have hcosh_le : Real.cosh (lam * (y - y')) ≤ max (Real.cosh (lam * z)) (Real.cosh (lam * z')) := by
    rcases le_max_iff.mp hmul with h1 | h2
    · exact le_trans (cosh_le_cosh_of_abs_le h1) (le_max_left _ _)
    · exact le_trans (cosh_le_cosh_of_abs_le h2) (le_max_right _ _)
  have hge1_z : 1 ≤ Real.cosh (lam * z) := one_le_cosh_aux _
  have hge1_z' : 1 ≤ Real.cosh (lam * z') := one_le_cosh_aux _
  have hmax_le : max (Real.cosh (lam * z)) (Real.cosh (lam * z')) ≤
      Real.cosh (lam * z) + Real.cosh (lam * z') - 1 := by
    exact max_le (by linarith) (by linarith)
  exact le_trans hcosh_le hmax_le

/-- Optimal Chernoff exponent for Lemma 4.1: at `θ = t / 2`,
`exp (-θ * m * t + m * θ^2) = exp (-m * t^2 / 4)`. -/
lemma lemma41_chernoff_opt (m t : ℝ) :
    Real.exp (-(t / 2) * m * t + m * (t / 2) ^ 2) = Real.exp (-m * t ^ 2 / 4) := by
  congr 1; ring

/-! ### Stage C.2: Lemma 4.2 (Epsilon-Net Lipschitz Discretization Step) -/

/-- **Lemma 4.2 (Net-to-Sphere Discretization Step)**:
On the operator-norm event `∑_i ⟪a_i, w⟫^2 ≤ 4 * m * ‖w‖^2`, for any `s_i ∈ {-1, 1}` (or `|s_i| ≤ 1`)
and any `u, u₀` with `‖u - u₀‖ ≤ γ / 8`, if `T_j(u₀) ≥ 3γ / 4`, then `T_j(u) ≥ γ / 2`. -/
theorem lemma42_net_to_sphere {m r : ℕ} (hm : 0 < m)
    (a : Fin m → E) (s : Fin m → ℝ) (β_star : Fin r → E) (j : Fin r)
    (hs : ∀ i : Fin m, |s i| ≤ 1)
    (h_op : ∀ w : E, ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 ≤ 4 * (m : ℝ) * ‖w‖ ^ 2)
    {γ : ℝ} {u u₀ : E}
    (h_net_dist : ‖u - u₀‖ ≤ γ / 8)
    (h_net_val : 3 * γ / 4 ≤ signedConeNorm a s β_star j u₀) :
    γ / 2 ≤ signedConeNorm a s β_star j u := by
  classical
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  -- Bound `|T_j(u) - T_j(u₀)| ≤ (1/m) ∑_i |⟪a_i, u - u₀⟫|`
  have h_lip : |signedConeNorm a s β_star j u - signedConeNorm a s β_star j u₀| ≤
      (1 / (m : ℝ)) * ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ| := by
    unfold signedConeNorm
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (m : ℝ)),
        ← Finset.sum_sub_distrib]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |∑ i : Fin m, ((if a i ∈ activeCone β_star j then s i * |⟪a i, u⟫_ℝ| else 0) -
                        (if a i ∈ activeCone β_star j then s i * |⟪a i, u₀⟫_ℝ| else 0))|
        ≤ ∑ i : Fin m, |(if a i ∈ activeCone β_star j then s i * |⟪a i, u⟫_ℝ| else 0) -
                        (if a i ∈ activeCone β_star j then s i * |⟪a i, u₀⟫_ℝ| else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ| := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          split_ifs
          · rw [← mul_sub, abs_mul]
            calc |s i| * abs (|⟪a i, u⟫_ℝ| - |⟪a i, u₀⟫_ℝ|)
                ≤ 1 * abs (|⟪a i, u⟫_ℝ| - |⟪a i, u₀⟫_ℝ|) :=
                  mul_le_mul_of_nonneg_right (hs i) (abs_nonneg _)
              _ = abs (|⟪a i, u⟫_ℝ| - |⟪a i, u₀⟫_ℝ|) := one_mul _
              _ ≤ |⟪a i, u⟫_ℝ - ⟪a i, u₀⟫_ℝ| := abs_abs_sub_abs_le_abs_sub _ _
              _ = |⟪a i, u - u₀⟫_ℝ| := by rw [inner_sub_right]
          · simp
  -- Apply Cauchy-Schwarz + `h_op` to get `(1/m) ∑_i |⟪a_i, u - u₀⟫| ≤ 2 * ‖u - u₀‖`
  have h_cs : (1 / (m : ℝ)) * ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ| ≤ 2 * ‖u - u₀‖ := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun _ => (1 : ℝ)) (fun i => |⟪a i, u - u₀⟫_ℝ|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one,
               sq_abs] at h1
    have h2 := h_op (u - u₀)
    have hsq : ((1 / (m : ℝ)) * ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ|) ^ 2 ≤ (2 * ‖u - u₀‖) ^ 2 := by
      rw [mul_pow]
      have hcomb : (∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ|) ^ 2 ≤ (m : ℝ) * (4 * (m : ℝ) * ‖u - u₀‖ ^ 2) :=
        le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt hm_pos))
      have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
      have hmul := mul_le_mul_of_nonneg_left hcomb (by positivity : (0 : ℝ) ≤ (1 / (m : ℝ)) ^ 2)
      have hsimp : (1 / (m : ℝ)) ^ 2 * ((m : ℝ) * (4 * (m : ℝ) * ‖u - u₀‖ ^ 2)) =
          (2 * ‖u - u₀‖) ^ 2 := by
        field_simp [hm_ne]; ring
      linarith
    have hnn1 : 0 ≤ (1 / (m : ℝ)) * ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ| :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    have hnn2 : 0 ≤ 2 * ‖u - u₀‖ := by positivity
    nlinarith
  have h_abs := (abs_le.mp (le_trans h_lip h_cs)).1
  linarith

/-! ### Stage C.3: Lemma 4.3(2) (Surrogate Properties, Arcsin Bound, Bernstein Moments & Tail) -/

/-- `φ_η(z₁, ·)` is 2-Lipschitz in its second argument, independent of `η`! -/
lemma lemma43_phiEta_lipschitz (η z₁ z₂ z₂' : ℝ) :
    |phiEta η z₁ z₂ - phiEta η z₁ z₂'| ≤ 2 * |z₂ - z₂'| := by
  unfold phiEta
  have h1 : |max 0 (2 * |z₂| - |z₁| / η) - max 0 (2 * |z₂'| - |z₁| / η)| ≤
      |(2 * |z₂| - |z₁| / η) - (2 * |z₂'| - |z₁| / η)| := by
    set a := 2 * |z₂| - |z₁| / η
    set b := 2 * |z₂'| - |z₁| / η
    rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
    · rw [max_eq_right ha, max_eq_right hb]
    · rw [max_eq_right ha, max_eq_left (le_of_lt hb), sub_zero, abs_of_nonneg ha,
          abs_of_pos (by linarith)]; linarith
    · rw [max_eq_left (le_of_lt ha), max_eq_right hb, zero_sub, abs_neg, abs_of_nonneg hb,
          abs_of_neg (by linarith)]; linarith
    · rw [max_eq_left (le_of_lt ha), max_eq_left (le_of_lt hb), sub_self, abs_zero]
      exact abs_nonneg _
  have h2 : (2 * |z₂| - |z₁| / η) - (2 * |z₂'| - |z₁| / η) = 2 * (|z₂| - |z₂'|) := by ring
  rw [h2, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub z₂ z₂') (by norm_num))

/-- Pointwise upper bound `φ_η(z₁, z₂) ≤ 2|z₂| * 1{|z₁| < 2 η |z₂|}` for `η > 0`. -/
lemma lemma43_phiEta_upper_dom {η : ℝ} (hη : 0 < η) (z₁ z₂ : ℝ) :
    phiEta η z₁ z₂ ≤ if |z₁| < 2 * η * |z₂| then 2 * |z₂| else 0 := by
  unfold phiEta
  split_ifs with h
  · apply max_le
    · positivity
    · have : 0 ≤ |z₁| / η := div_nonneg (abs_nonneg _) (le_of_lt hη)
      linarith
  · push_neg at h
    apply max_le le_rfl
    have : 2 * |z₂| ≤ |z₁| / η := by
      rw [le_div_iff₀ hη]; linarith
    linarith

/-- **Lemma 4.3(2), Arcsin Bound**: For all `η ∈ [0, 1/4]`,
`(2 * Real.arcsin (2 * η)) / Real.pi ≤ (4 / 3) * η`. -/
theorem lemma43_arcsin_bound {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 4) :
    2 * Real.arcsin (2 * η) / Real.pi ≤ 4 / 3 * η := by
  rw [div_le_iff₀ Real.pi_pos]
  -- Equivalent to `arcsin (2η) ≤ (2π/3) η`, which follows from `2η ≤ sin ((2π/3) η)` by concavity of `sin` on `[0, π/6]`!
  have hgoal : Real.arcsin (2 * η) ≤ (2 * Real.pi / 3) * η := by
    have hx0 : 0 ≤ (2 * Real.pi / 3) * η := by positivity
    have hx_le : (2 * Real.pi / 3) * η ≤ Real.pi / 6 := by nlinarith [Real.pi_pos]
    have hsin_ge : 2 * η ≤ Real.sin ((2 * Real.pi / 3) * η) := by
      -- Write `(2π/3) η = (1 - 4η) * 0 + (4η) * (π/6)` and apply concavity of `sin` on `[0, π]`!
      have ht0 : 0 ≤ 4 * η := by linarith
      have ht1 : 0 ≤ 1 - 4 * η := by linarith
      have hsum : (1 - 4 * η) + 4 * η = 1 := by ring
      have hconv := strictConcaveOn_sin_Icc.concaveOn.2
        (Set.left_mem_Icc.mpr (le_of_lt Real.pi_pos))
        (⟨by positivity, by linarith [Real.pi_pos]⟩ : Real.pi / 6 ∈ Set.Icc (0 : ℝ) Real.pi)
        ht1 ht0 hsum
      simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero, Real.sin_pi_div_six] at hconv
      have harg : 4 * η * (Real.pi / 6) = (2 * Real.pi / 3) * η := by ring
      rw [harg] at hconv
      linarith
    have h_arcsin_sin : Real.arcsin (Real.sin ((2 * Real.pi / 3) * η)) = (2 * Real.pi / 3) * η :=
      Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    calc Real.arcsin (2 * η)
        ≤ Real.arcsin (Real.sin ((2 * Real.pi / 3) * η)) := Real.arcsin_le_arcsin hsin_ge
      _ = (2 * Real.pi / 3) * η := h_arcsin_sin
  linarith

/-- **Lemma 4.3(2), Exact Bernstein Moment Induction**:
For every integer `p ≥ 2`:
`2^(3p/2) * Γ(1 + p/2) ≤ p! * 2^p`.
This directly yields `E[X^p] ≤ (p!/2) * v₀ * B^{p-2}` with `v₀ = 8q ≤ (32/3) η` and `B = 2`. -/
theorem lemma43_moment_induction : ∀ p : ℕ, 2 ≤ p →
    (2 : ℝ) ^ ((3 * (p : ℝ)) / 2) * Real.Gamma (1 + (p : ℝ) / 2) ≤
      (Nat.factorial p : ℝ) * (2 : ℝ) ^ p := by
  intro p hp
  -- Strong induction on `p` with step `p → p + 2` and bases `p = 2` and `p = 3`!
  induction p using Nat.strong_induction_on with
  | h p ih =>
    match p with
    | 0 => omega
    | 1 => omega
    | 2 =>
      -- Base `p = 2`: `2^3 * Γ(2) = 8 * 1 = 8 = 2! * 2^2`
      have harg1 : (3 * ((2 : ℕ) : ℝ)) / 2 = (3 : ℝ) := by norm_num
      have harg2 : (1 : ℝ) + ((2 : ℕ) : ℝ) / 2 = (2 : ℝ) := by norm_num
      rw [harg1, harg2, show (2 : ℝ) = (1 : ℝ) + 1 by norm_num, Real.Gamma_add_one (by norm_num),
          Real.Gamma_one]
      norm_num [Nat.factorial]
    | 3 =>
      -- Base `p = 3`: `2^(9/2) * Γ(5/2) = 12 * √(2π) ≤ 48 = 3! * 2^3`
      have harg1 : (3 * ((3 : ℕ) : ℝ)) / 2 = (4 : ℝ) + (1 / 2 : ℝ) := by norm_num
      have harg2 : (1 : ℝ) + ((3 : ℕ) : ℝ) / 2 = (3 / 2 : ℝ) + 1 := by norm_num
      rw [harg1, harg2, Real.Gamma_add_one (by norm_num),
          show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.Gamma_add_one (by norm_num),
          Real.Gamma_one_half_eq, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.sqrt_eq_rpow]
      have h2_4 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
      rw [h2_4]
      have hs2 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_iff]; norm_num
      have hspi : Real.sqrt Real.pi ≤ 2 := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by linarith [Real.pi_lt_four]⟩
      have hprod : Real.sqrt 2 * Real.sqrt Real.pi ≤ 4 := by
        have h := mul_le_mul hs2 hspi (Real.sqrt_nonneg _) (by norm_num)
        linarith
      norm_num [Nat.factorial]
      nlinarith
    | n + 4 =>
      -- Step `n + 2 → n + 4` (where `n + 2 ≥ 2`)
      have hprev := ih (n + 2) (by omega) (by omega)
      have hcast_n4 : ((n + 4 : ℕ) : ℝ) = ((n + 2 : ℕ) : ℝ) + 2 := by push_cast; ring
      have harg1 : (3 * ((n + 4 : ℕ) : ℝ)) / 2 = (3 * ((n + 2 : ℕ) : ℝ)) / 2 + 3 := by
        rw [hcast_n4]; ring
      have harg2 : (1 : ℝ) + ((n + 4 : ℕ) : ℝ) / 2 = (1 + ((n + 2 : ℕ) : ℝ) / 2) + 1 := by
        rw [hcast_n4]; ring
      have hpos_g : (1 : ℝ) + ((n + 2 : ℕ) : ℝ) / 2 ≠ 0 := by positivity
      rw [harg1, harg2, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          Real.Gamma_add_one hpos_g]
      have h2_3 : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num
      rw [h2_3]
      have hfact : ((Nat.factorial (n + 4)) : ℝ) =
          (((n + 4 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)) * (Nat.factorial (n + 2) : ℝ) := by
        have hnat : Nat.factorial (n + 4) = (n + 4) * ((n + 3) * Nat.factorial (n + 2)) := by
          simp [Nat.factorial_succ]
        rw [hnat]; push_cast; ring
      have hpow : (2 : ℝ) ^ (n + 4) = 4 * (2 : ℝ) ^ (n + 2) := by
        rw [pow_add]; norm_num; ring
      rw [hfact, hpow]
      -- LHS = 8 * (1 + (n+2)/2) * prev_LHS = 4 * (n + 4) * prev_LHS
      -- RHS = 4 * (n + 4) * (n + 3) * prev_RHS ≥ 4 * (n + 4) * prev_LHS (since `n + 3 ≥ 3 ≥ 1`)!
      have hcoeff : (2 : ℝ) ^ ((3 * ((n + 2 : ℕ) : ℝ)) / 2) * 8 *
          ((1 + ((n + 2 : ℕ) : ℝ) / 2) * Real.Gamma (1 + ((n + 2 : ℕ) : ℝ) / 2)) =
          4 * ((n + 4 : ℕ) : ℝ) *
            ((2 : ℝ) ^ ((3 * ((n + 2 : ℕ) : ℝ)) / 2) * Real.Gamma (1 + ((n + 2 : ℕ) : ℝ) / 2)) := by
        rw [hcast_n4]; ring
      rw [hcoeff]
      have h1 : 4 * ((n + 4 : ℕ) : ℝ) *
          ((2 : ℝ) ^ ((3 * ((n + 2 : ℕ) : ℝ)) / 2) * Real.Gamma (1 + ((n + 2 : ℕ) : ℝ) / 2)) ≤
          4 * ((n + 4 : ℕ) : ℝ) * ((Nat.factorial (n + 2) : ℝ) * (2 : ℝ) ^ (n + 2)) :=
        mul_le_mul_of_nonneg_left hprev (by positivity)
      have hn3 : (1 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ n + 3)
      have hrhs_nn : 0 ≤ (Nat.factorial (n + 2) : ℝ) * (2 : ℝ) ^ (n + 2) := by positivity
      have h2 : 4 * ((n + 4 : ℕ) : ℝ) * ((Nat.factorial (n + 2) : ℝ) * (2 : ℝ) ^ (n + 2)) ≤
          ((n + 4 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ) * (Nat.factorial (n + 2) : ℝ) * (4 * (2 : ℝ) ^ (n + 2)) := by
        have hstep : 4 * ((n + 4 : ℕ) : ℝ) ≤ 4 * ((n + 4 : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ) := by
          nlinarith [show (0 : ℝ) ≤ 4 * ((n + 4 : ℕ) : ℝ) by positivity]
        have hmul := mul_le_mul_of_nonneg_right hstep hrhs_nn
        linarith
      exact le_trans h1 h2

/-- **Lemma 4.3(2), One-Sided Bernstein MGF Inequality (No Centering Factor Lost)**:
For nonnegative mean `μ ≥ 0`, variance parameter `v₀ ≥ 0`, scale `B > 0`, and `0 < λ < 1/B`:
`exp (-λ μ) * (1 + λ μ + λ^2 v₀ / (2(1 - λ B))) ≤ exp (λ^2 v₀ / (2(1 - λ B)))`. -/
lemma lemma43_bernstein_mgf_step {lam μ v₀ B : ℝ}
    (hlam : 0 < lam) (hμ : 0 ≤ μ) (hv₀ : 0 ≤ v₀) (hB : 0 < B) (hlamB : lam * B < 1) :
    Real.exp (-lam * μ) * (1 + lam * μ + lam ^ 2 * v₀ / (2 * (1 - lam * B))) ≤
      Real.exp (lam ^ 2 * v₀ / (2 * (1 - lam * B))) := by
  have h1 := Real.add_one_le_exp (lam * μ + lam ^ 2 * v₀ / (2 * (1 - lam * B)))
  have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos (-lam * μ)))
  rw [← Real.exp_add] at hmul
  have hsimp : -lam * μ + (lam * μ + lam ^ 2 * v₀ / (2 * (1 - lam * B))) =
      lam ^ 2 * v₀ / (2 * (1 - lam * B)) := by ring
  rw [hsimp] at hmul
  linarith

/-- **Lemma 4.3(2), Bernstein Chernoff Optimization & Exact Constant `3/22`**:
For `m > 0`, `v₀ ≥ 0`, `B > 0`, `t > 0`, setting `λ = t / (v₀ + B t)` satisfies `0 < λ < 1/B`
and gives `exp (-m λ t + m λ^2 v₀ / (2(1 - λ B))) ≤ exp (-m t^2 / (2(v₀ + B t)))`.
Moreover, when `v₀ ≤ (32/3) η`, `B = 2`, `t = 2 η`, `η > 0`, this is `≤ exp (-(3/22) m η)`. -/
theorem lemma43_bernstein_exponent {m v₀ B t : ℝ}
    (hm : 0 < m) (hv₀ : 0 < v₀) (hB : 0 < B) (ht : 0 < t) :
    let lam := t / (v₀ + B * t)
    0 < lam ∧ lam * B < 1 ∧
    Real.exp (-m * lam * t + m * (lam ^ 2 * v₀ / (2 * (1 - lam * B)))) ≤
      Real.exp (-m * t ^ 2 / (2 * (v₀ + B * t))) := by
  intro lam
  have hden : 0 < v₀ + B * t := by nlinarith
  have hlam_pos : 0 < lam := div_pos ht hden
  have hlamB_lt : lam * B < 1 := by
    dsimp [lam]
    rw [div_mul_eq_mul_div, div_lt_one hden]
    nlinarith
  refine ⟨hlam_pos, hlamB_lt, Real.exp_le_exp.mpr ?_⟩
  have h1m : 1 - lam * B = v₀ / (v₀ + B * t) := by
    dsimp [lam]; field_simp [ne_of_gt hden]; ring
  rw [h1m]
  dsimp [lam]
  have heq : -m * (t / (v₀ + B * t)) * t +
      m * ((t / (v₀ + B * t)) ^ 2 * v₀ / (2 * (v₀ / (v₀ + B * t)))) =
      -m * t ^ 2 / (2 * (v₀ + B * t)) := by
    field_simp [ne_of_gt hden, ne_of_gt hv₀]
    ring
  linarith

/-- Specialization of the Bernstein exponent to `v₀ ≤ (32/3) η`, `B = 2`, `t = 2 η` (for `η > 0`):
`-m t^2 / (2(v₀ + B t)) ≤ -(3/22) m η`. -/
lemma lemma43_bernstein_const_3_22 {m v₀ η : ℝ}
    (hm : 0 ≤ m) (hη : 0 < η) (hv₀_nn : 0 ≤ v₀) (hv₀ : v₀ ≤ 32 / 3 * η) :
    -m * (2 * η) ^ 2 / (2 * (v₀ + 2 * (2 * η))) ≤ -(3 / 22) * m * η := by
  have hden_pos : 0 < 2 * (v₀ + 2 * (2 * η)) := by linarith
  have hden_le : 2 * (v₀ + 2 * (2 * η)) ≤ 88 / 3 * η := by linarith
  have hfrac : 3 / 22 * m * η ≤ m * (2 * η) ^ 2 / (2 * (v₀ + 2 * (2 * η))) := by
    rw [le_div_iff₀ hden_pos]
    have hmul := mul_le_mul_of_nonneg_left hden_le (show 0 ≤ 3 / 22 * m * η by positivity)
    linarith
  have hneg : -m * (2 * η) ^ 2 / (2 * (v₀ + 2 * (2 * η))) =
      -(m * (2 * η) ^ 2 / (2 * (v₀ + 2 * (2 * η)))) := by ring
  linarith

/-- **Lemma 4.3(2), Net-to-Sphere Discretization Step & Exact Constant `< 6.35 η`**:
On `∑_i ⟪a_i, w⟫^2 ≤ 4 m ‖w‖^2`, if `‖u - u₀‖ ≤ η / 4` and the net point satisfies
`(1/m) ∑_i φ_η(..., u₀) ≤ (4√(2π)/3 + 2) η`, then `(1/m) ∑_i φ_η(..., u) ≤ (635/100) η`. -/
theorem lemma43_net_to_sphere {m : ℕ} (hm : 0 < m)
    (a : Fin m → E) (vhat u u₀ : E) {η : ℝ} (hη : 0 < η)
    (h_op : ∀ w : E, ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 ≤ 4 * (m : ℝ) * ‖w‖ ^ 2)
    (h_net_dist : ‖u - u₀‖ ≤ η / 4)
    (h_net_val : (1 / (m : ℝ)) * ∑ i : Fin m, phiEta η ⟪a i, vhat⟫_ℝ ⟪a i, u₀⟫_ℝ ≤
      (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η) :
    (1 / (m : ℝ)) * ∑ i : Fin m, phiEta η ⟪a i, vhat⟫_ℝ ⟪a i, u⟫_ℝ ≤ (635 / 100 : ℝ) * η := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have h_lip :
      (1 / (m : ℝ)) * ∑ i : Fin m, phiEta η ⟪a i, vhat⟫_ℝ ⟪a i, u⟫_ℝ -
      (1 / (m : ℝ)) * ∑ i : Fin m, phiEta η ⟪a i, vhat⟫_ℝ ⟪a i, u₀⟫_ℝ ≤
      2 * ((1 / (m : ℝ)) * ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ|) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    have hrhs : 2 * ((1 / (m : ℝ)) * ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ|) =
        (1 / (m : ℝ)) * ∑ i : Fin m, 2 * |⟪a i, u - u₀⟫_ℝ| := by
      rw [← Finset.mul_sum]; ring
    rw [hrhs]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h1 := lemma43_phiEta_lipschitz η ⟪a i, vhat⟫_ℝ ⟪a i, u⟫_ℝ ⟪a i, u₀⟫_ℝ
    have h2 : ⟪a i, u⟫_ℝ - ⟪a i, u₀⟫_ℝ = ⟪a i, u - u₀⟫_ℝ := (inner_sub_right _ _ _).symm
    rw [h2] at h1
    exact le_trans (le_abs_self _) h1
  have h_cs : (1 / (m : ℝ)) * ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ| ≤ 2 * ‖u - u₀‖ := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun _ => (1 : ℝ)) (fun i => |⟪a i, u - u₀⟫_ℝ|)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one,
               sq_abs] at h1
    have h2 := h_op (u - u₀)
    have hsq : ((1 / (m : ℝ)) * ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ|) ^ 2 ≤ (2 * ‖u - u₀‖) ^ 2 := by
      rw [mul_pow]
      have hcomb := le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt hm_pos))
      have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
      have hmul := mul_le_mul_of_nonneg_left hcomb (by positivity : (0 : ℝ) ≤ (1 / (m : ℝ)) ^ 2)
      have hsimp : (1 / (m : ℝ)) ^ 2 * ((m : ℝ) * (4 * (m : ℝ) * ‖u - u₀‖ ^ 2)) =
          (2 * ‖u - u₀‖) ^ 2 := by
        field_simp [hm_ne]; ring
      linarith
    have hnn1 : 0 ≤ (1 / (m : ℝ)) * ∑ i : Fin m, |⟪a i, u - u₀⟫_ℝ| :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    have hnn2 : 0 ≤ 2 * ‖u - u₀‖ := by positivity
    nlinarith
  -- Numeric bound: `4 * √(2π) / 3 + 3 ≤ 635 / 100` (since `2π < 6.29 < (2.51)^2`, `4*2.51/3 + 3 = 6.3467 < 6.35`!)
  have hpi_lt : Real.pi < 3.1416 := Real.pi_lt_d4
  have hs2pi_lt : Real.sqrt (2 * Real.pi) < 251 / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]
    linarith
  have hconst : 4 * Real.sqrt (2 * Real.pi) / 3 + 3 ≤ 635 / 100 := by linarith
  nlinarith

/-! ### Stage C.4: Exact Constants of Theorem 4 & Corollary 4.1 (Phase II Corrected!) -/

/-- Exact budget check for Theorem 4: with `C_flip = 635/100` and `η = γ / (26 * (r - 1))` (`r ≥ 2`),
`C_flip * η * (r - 1) ≤ γ / 4`. -/
lemma theorem4_budget_check {r : ℕ} (hr : 2 ≤ r) {γ : ℝ} (hγ : 0 ≤ γ) :
    let η := γ / (26 * ((r : ℝ) - 1))
    (635 / 100 : ℝ) * η * ((r : ℝ) - 1) ≤ γ / 4 := by
  intro η
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  dsimp [η]
  have hsimp : (635 / 100 : ℝ) * (γ / (26 * ((r : ℝ) - 1))) * ((r : ℝ) - 1) = (635 / 2600 : ℝ) * γ := by
    field_simp [ne_of_gt hr1]
    ring
  rw [hsimp]
  linarith

/-- **Corollary 4.1 (Phase II Corrected Radius & Condition Number Identities)**:
For `r = 2`, `α = 0`, `γ = 1 / √(2π)`, `η = γ / 26`:
- `ρ = (η / √2) * ‖v‖ = ‖v‖ / (52 * √π)` (NOT `‖v‖ / (52 * √(2π))`!);
- `ρ / 2 = ‖v‖ / (104 * √π)`;
- `L / μ = 2 / (γ / 4) = 8 * √(2π)`. -/
theorem corollary41_exact_identities (v_norm : ℝ) :
    let γ := 1 / Real.sqrt (2 * Real.pi)
    let η := γ / 26
    let ρ := (η / Real.sqrt 2) * v_norm
    ρ = v_norm / (52 * Real.sqrt Real.pi) ∧
    ρ / 2 = v_norm / (104 * Real.sqrt Real.pi) ∧
    2 / (γ / 4) = 8 * Real.sqrt (2 * Real.pi) := by
  intro γ η ρ
  have hs2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hspi_ne : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hs2pi_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hmul_rt : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) _
  refine ⟨?_, ?_, ?_⟩
  · dsimp [ρ, η, γ]
    rw [hmul_rt]
    have h1 : 1 / (Real.sqrt 2 * Real.sqrt Real.pi) / 26 / Real.sqrt 2 * v_norm =
        v_norm / (26 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt Real.pi) := by
      field_simp [hs2_ne, hspi_ne]
    rw [h1, hsq2]; ring
  · dsimp [ρ, η, γ]
    rw [hmul_rt]
    have h1 : 1 / (Real.sqrt 2 * Real.sqrt Real.pi) / 26 / Real.sqrt 2 * v_norm / 2 =
        v_norm / (52 * (Real.sqrt 2 * Real.sqrt 2) * Real.sqrt Real.pi) := by
      field_simp [hs2_ne, hspi_ne]; ring
    rw [h1, hsq2]; ring
  · dsimp [γ]
    field_simp [hs2pi_ne]
    ring

/-- **Theorem 4 Union Bound & Tail Algebra**:
If each of the 3 bad events has probability `≤ δ_fail / 3` (via `m ≥ (64/γ^2)(d log(1+16/γ) + log(3r/δ))`
and `m ≥ (22/(3η))(d log(9/η) + log(3M/δ))` and `m ≥ (32/9) log(3/δ)`),
then the corresponding exponential bounds are each `≤ δ_fail / 3`, and their sum is `≤ δ_fail`. -/
theorem theorem4_tail_algebra
    {m d r M : ℕ} {γ η δ_fail : ℝ}
    (hγ : 0 < γ) (hη : 0 < η) (hη_lt : η < 1) (hδ : 0 < δ_fail) (hr : 0 < r) (hM : 0 < M)
    (hm0 : (32 / 9 : ℝ) * Real.log (3 / δ_fail) ≤ (m : ℝ))
    (hm1 : (64 / γ ^ 2) * ((d : ℝ) * Real.log (1 + 16 / γ) + Real.log (3 * (r : ℝ) / δ_fail)) ≤ (m : ℝ))
    (hm2 : (22 / (3 * η)) * ((d : ℝ) * Real.log (9 / η) + Real.log (3 * (M : ℝ) / δ_fail)) ≤ (m : ℝ)) :
    Real.exp (-(9 / 32 : ℝ) * (m : ℝ)) +
    (r : ℝ) * (1 + 16 / γ) ^ d * Real.exp (-(m : ℝ) * γ ^ 2 / 64) +
    (M : ℝ) * (9 / η) ^ d * Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η) ≤ δ_fail := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  -- Term 0: `exp(-(9/32) m) ≤ δ_fail / 3`
  have h0 : Real.exp (-(9 / 32 : ℝ) * (m : ℝ)) ≤ δ_fail / 3 := by
    have hexp : Real.log (3 / δ_fail) ≤ (9 / 32 : ℝ) * (m : ℝ) := by linarith
    have h1 : Real.exp (-(9 / 32 : ℝ) * (m : ℝ)) ≤ Real.exp (-Real.log (3 / δ_fail)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at h1
    exact h1
  -- Term 1: `r * (1 + 16/γ)^d * exp(-m γ^2 / 64) ≤ δ_fail / 3`
  have h1 : (r : ℝ) * (1 + 16 / γ) ^ d * Real.exp (-(m : ℝ) * γ ^ 2 / 64) ≤ δ_fail / 3 := by
    have hbase : 0 < 1 + 16 / γ := by positivity
    have hexp : (d : ℝ) * Real.log (1 + 16 / γ) + Real.log (3 * (r : ℝ) / δ_fail) ≤
        (m : ℝ) * γ ^ 2 / 64 := by
      have := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ γ ^ 2 / 64)
      have hsimp : γ ^ 2 / 64 * (64 / γ ^ 2 * ((d : ℝ) * Real.log (1 + 16 / γ) +
          Real.log (3 * (r : ℝ) / δ_fail))) =
          (d : ℝ) * Real.log (1 + 16 / γ) + Real.log (3 * (r : ℝ) / δ_fail) := by
        field_simp [ne_of_gt hγ]
      linarith
    have hpow : (1 + 16 / γ) ^ d = Real.exp ((d : ℝ) * Real.log (1 + 16 / γ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbase, mul_comm]
    rw [hpow]
    have hcomb : (r : ℝ) * Real.exp ((d : ℝ) * Real.log (1 + 16 / γ)) *
        Real.exp (-(m : ℝ) * γ ^ 2 / 64) =
        (r : ℝ) * Real.exp ((d : ℝ) * Real.log (1 + 16 / γ) - (m : ℝ) * γ ^ 2 / 64) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [hcomb]
    have hle := Real.exp_le_exp.mpr (show (d : ℝ) * Real.log (1 + 16 / γ) - (m : ℝ) * γ ^ 2 / 64 ≤
        -Real.log (3 * (r : ℝ) / δ_fail) by linarith)
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at hle
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hr_pos)
    have hsimp : (r : ℝ) * (δ_fail / (3 * (r : ℝ))) = δ_fail / 3 := by
      field_simp [ne_of_gt hr_pos]
    linarith
  -- Term 2: `M * (9/η)^d * exp(-(3/22) m η) ≤ δ_fail / 3`
  have h2 : (M : ℝ) * (9 / η) ^ d * Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η) ≤ δ_fail / 3 := by
    have hbase : 0 < 9 / η := by positivity
    have hexp : (d : ℝ) * Real.log (9 / η) + Real.log (3 * (M : ℝ) / δ_fail) ≤
        (3 / 22 : ℝ) * (m : ℝ) * η := by
      have := mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ 3 * η / 22)
      have hsimp : 3 * η / 22 * (22 / (3 * η) * ((d : ℝ) * Real.log (9 / η) +
          Real.log (3 * (M : ℝ) / δ_fail))) =
          (d : ℝ) * Real.log (9 / η) + Real.log (3 * (M : ℝ) / δ_fail) := by
        field_simp [ne_of_gt hη]
      linarith
    have hpow : (9 / η) ^ d = Real.exp ((d : ℝ) * Real.log (9 / η)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbase, mul_comm]
    rw [hpow]
    have hcomb : (M : ℝ) * Real.exp ((d : ℝ) * Real.log (9 / η)) *
        Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η) =
        (M : ℝ) * Real.exp ((d : ℝ) * Real.log (9 / η) - (3 / 22 : ℝ) * (m : ℝ) * η) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    rw [hcomb]
    have hle := Real.exp_le_exp.mpr (show (d : ℝ) * Real.log (9 / η) - (3 / 22 : ℝ) * (m : ℝ) * η ≤
        -Real.log (3 * (M : ℝ) / δ_fail) by linarith)
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div] at hle
    have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hM_pos)
    have hsimp : (M : ℝ) * (δ_fail / (3 * (M : ℝ))) = δ_fail / 3 := by
      field_simp [ne_of_gt hM_pos]
    linarith
  linarith

end Research107
