import Research107.GaussianModel
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Stage 2: Unconditional Gaussian Matrix Operator Norm Tail Bound -/

/-- Minkowski / triangle inequality for the Euclidean row-projection seminorm
`w ↦ √(∑ i, ⟪a i, w⟫^2)`. -/
private lemma sqrt_sum_inner_sq_add_le {m : ℕ} (a : Fin m → E) (w₁ w₂ : E) :
    Real.sqrt (∑ i : Fin m, ⟪a i, w₁ + w₂⟫_ℝ ^ 2) ≤
      Real.sqrt (∑ i : Fin m, ⟪a i, w₁⟫_ℝ ^ 2) +
      Real.sqrt (∑ i : Fin m, ⟪a i, w₂⟫_ℝ ^ 2) := by
  have hnn1 : 0 ≤ ∑ i : Fin m, ⟪a i, w₁⟫_ℝ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hnn2 : 0 ≤ ∑ i : Fin m, ⟪a i, w₂⟫_ℝ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
    (fun i => ⟪a i, w₁⟫_ℝ) (fun i => ⟪a i, w₂⟫_ℝ)
  have hdot : ∑ i : Fin m, ⟪a i, w₁⟫_ℝ * ⟪a i, w₂⟫_ℝ ≤
      Real.sqrt (∑ i : Fin m, ⟪a i, w₁⟫_ℝ ^ 2) * Real.sqrt (∑ i : Fin m, ⟪a i, w₂⟫_ℝ ^ 2) := by
    calc ∑ i : Fin m, ⟪a i, w₁⟫_ℝ * ⟪a i, w₂⟫_ℝ
        ≤ |∑ i : Fin m, ⟪a i, w₁⟫_ℝ * ⟪a i, w₂⟫_ℝ| := le_abs_self _
      _ = Real.sqrt ((∑ i : Fin m, ⟪a i, w₁⟫_ℝ * ⟪a i, w₂⟫_ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∑ i : Fin m, ⟪a i, w₁⟫_ℝ ^ 2) * (∑ i : Fin m, ⟪a i, w₂⟫_ℝ ^ 2)) :=
            Real.sqrt_le_sqrt hcs
      _ = Real.sqrt (∑ i : Fin m, ⟪a i, w₁⟫_ℝ ^ 2) * Real.sqrt (∑ i : Fin m, ⟪a i, w₂⟫_ℝ ^ 2) :=
            Real.sqrt_mul hnn1 _
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have hexp : ∑ i : Fin m, ⟪a i, w₁ + w₂⟫_ℝ ^ 2 =
      (∑ i : Fin m, ⟪a i, w₁⟫_ℝ ^ 2) + 2 * (∑ i : Fin m, ⟪a i, w₁⟫_ℝ * ⟪a i, w₂⟫_ℝ) +
      (∑ i : Fin m, ⟪a i, w₂⟫_ℝ ^ 2) := by
    have h1 : ∀ i : Fin m, ⟪a i, w₁ + w₂⟫_ℝ ^ 2 =
        ⟪a i, w₁⟫_ℝ ^ 2 + 2 * (⟪a i, w₁⟫_ℝ * ⟪a i, w₂⟫_ℝ) + ⟪a i, w₂⟫_ℝ ^ 2 := by
      intro i; rw [inner_add_right]; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hexp]
  have hsq1 : Real.sqrt (∑ i : Fin m, ⟪a i, w₁⟫_ℝ ^ 2) ^ 2 = ∑ i : Fin m, ⟪a i, w₁⟫_ℝ ^ 2 :=
    Real.sq_sqrt hnn1
  have hsq2 : Real.sqrt (∑ i : Fin m, ⟪a i, w₂⟫_ℝ ^ 2) ^ 2 = ∑ i : Fin m, ⟪a i, w₂⟫_ℝ ^ 2 :=
    Real.sq_sqrt hnn2
  nlinarith

/-- **Deterministic `(1/6)`-net to operator norm bound**:
If `N` is a `(1/6)`-net of `S^{d-1}` and `∑ i, ⟪a i, u₀⟫^2 ≤ (25/9) m` for every `u₀ ∈ N`,
then `∑ i, ⟪a i, w⟫^2 ≤ 4 m ‖w‖^2` for all `w : E`. -/
theorem op_norm_of_one_sixth_net {m : ℕ} (a : Fin m → E) (N : Finset E)
    (h_net : ∀ u : E, ‖u‖ = 1 → ∃ u₀ ∈ N, ‖u - u₀‖ ≤ 1 / 6)
    (h_val : ∀ u₀ ∈ N, ∑ i : Fin m, ⟪a i, u₀⟫_ℝ ^ 2 ≤ (25 / 9 : ℝ) * (m : ℝ)) :
    ∀ w : E, ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 ≤ 4 * (m : ℝ) * ‖w‖ ^ 2 := by
  let g : E → ℝ := fun w => Real.sqrt (∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2)
  have hg_smul : ∀ (c : ℝ) (w : E), g (c • w) = |c| * g w := by
    intro c w
    dsimp [g]
    have h1 : ∑ i : Fin m, ⟪a i, c • w⟫_ℝ ^ 2 = c ^ 2 * ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_smul_right]; ring
    rw [h1, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  -- Handle trivial vs nontrivial unit sphere
  by_cases hs : ∃ u : E, ‖u‖ = 1
  · let S : Set ℝ := g '' {u : E | ‖u‖ = 1}
    have hS_ne : S.Nonempty := by
      rcases hs with ⟨u, hu⟩
      exact ⟨g u, u, hu, rfl⟩
    have hS_bdd : BddAbove S := by
      refine ⟨Real.sqrt (∑ i : Fin m, ‖a i‖ ^ 2), ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      dsimp [g]
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i _ => ?_))
      have hcs := abs_real_inner_le_norm (a i) u
      rw [hu, mul_one] at hcs
      have hsq : |⟪a i, u⟫_ℝ| ^ 2 ≤ ‖a i‖ ^ 2 := by nlinarith [abs_nonneg ⟪a i, u⟫_ℝ, norm_nonneg (a i)]
      rwa [sq_abs] at hsq
    let M : ℝ := sSup S
    have hM_nonneg : 0 ≤ M := by
      rcases hs with ⟨u, hu⟩
      exact le_trans (Real.sqrt_nonneg _) (le_csSup hS_bdd ⟨u, hu, rfl⟩)
    have hg_le_M : ∀ w : E, g w ≤ M * ‖w‖ := by
      intro w
      by_cases hw : w = 0
      · subst hw; simp [g]
      · have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
        let u := (‖w‖⁻¹) • w
        have hu : ‖u‖ = 1 := by
          dsimp [u]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
        have hgu : g u ≤ M := le_csSup hS_bdd ⟨u, hu, rfl⟩
        have hscale : g w = ‖w‖ * g u := by
          have : w = ‖w‖ • u := by
            dsimp [u]; rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
          conv_lhs => rw [this]
          rw [hg_smul, abs_of_pos hpos]
        rw [hscale]
        nlinarith
    -- Bootstrap: `M ≤ (5/3) √m + (1/6) M ⇒ M ≤ 2 √m`
    have hM_le : M ≤ (5 / 3 : ℝ) * Real.sqrt (m : ℝ) + (1 / 6 : ℝ) * M := by
      refine csSup_le hS_ne ?_
      rintro _ ⟨u, hu, rfl⟩
      rcases h_net u hu with ⟨u₀, hu₀N, hdist⟩
      have htri : g u ≤ g u₀ + g (u - u₀) := by
        have : u = u₀ + (u - u₀) := by abel
        conv_lhs => rw [this]
        exact sqrt_sum_inner_sq_add_le a u₀ (u - u₀)
      have hgu₀ : g u₀ ≤ (5 / 3 : ℝ) * Real.sqrt (m : ℝ) := by
        dsimp [g]
        calc Real.sqrt (∑ i : Fin m, ⟪a i, u₀⟫_ℝ ^ 2)
            ≤ Real.sqrt ((25 / 9 : ℝ) * (m : ℝ)) := Real.sqrt_le_sqrt (h_val u₀ hu₀N)
          _ = Real.sqrt (25 / 9 : ℝ) * Real.sqrt (m : ℝ) := Real.sqrt_mul (by norm_num) _
          _ = (5 / 3 : ℝ) * Real.sqrt (m : ℝ) := by
              rw [show (25 / 9 : ℝ) = (5 / 3 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      have hgdiff : g (u - u₀) ≤ (1 / 6 : ℝ) * M := by
        calc g (u - u₀) ≤ M * ‖u - u₀‖ := hg_le_M (u - u₀)
          _ ≤ M * (1 / 6 : ℝ) := mul_le_mul_of_nonneg_left hdist hM_nonneg
          _ = (1 / 6 : ℝ) * M := by ring
      linarith
    have hM_final : M ≤ 2 * Real.sqrt (m : ℝ) := by linarith
    intro w
    have hgw : g w ≤ 2 * Real.sqrt (m : ℝ) * ‖w‖ := by
      calc g w ≤ M * ‖w‖ := hg_le_M w
        _ ≤ (2 * Real.sqrt (m : ℝ)) * ‖w‖ := mul_le_mul_of_nonneg_right hM_final (norm_nonneg w)
    have hsq : g w ^ 2 ≤ (2 * Real.sqrt (m : ℝ) * ‖w‖) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2)]
    dsimp [g] at hsq
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hsq
    have hrhs : (2 * Real.sqrt (m : ℝ) * ‖w‖) ^ 2 = 4 * (m : ℝ) * ‖w‖ ^ 2 := by
      calc (2 * Real.sqrt (m : ℝ) * ‖w‖) ^ 2
          = 4 * (Real.sqrt (m : ℝ)) ^ 2 * ‖w‖ ^ 2 := by ring
        _ = 4 * (m : ℝ) * ‖w‖ ^ 2 := by rw [Real.sq_sqrt (Nat.cast_nonneg m)]
    linarith
  · -- Empty unit sphere ⇒ every `w = 0`
    intro w
    have hw : w = 0 := by
      by_contra hne
      have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hne
      apply hs
      refine ⟨(‖w‖⁻¹) • w, ?_⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
    subst hw
    simp

/-- Elementary numeric inequality for the `(1/6)`-net `χ²_m` Chernoff bound:
for `32 * d ≤ m`, `13^d * ((5/3) * exp (-8/9))^m ≤ exp (-(9/32) * m)`. -/
private lemma thirteen_pow_d_mul_chisq_le {m d : ℕ} (hd : 32 * d ≤ m) :
    (13 : ℝ) ^ d * ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ m ≤
      Real.exp (-(9 / 32 : ℝ) * (m : ℝ)) := by
  -- Step 1: `13 * ((5/3) * exp (-8/9))^32 ≤ exp (-9)`
  have hexp1 : (163 / 60 : ℝ) ≤ Real.exp 1 := by
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 6
    simp [Finset.sum_range_succ, Nat.factorial] at hsum
    linarith
  have h32_base : (13 : ℝ) * ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ 32 ≤ Real.exp (-9) := by
    have hpow19 : (13 : ℝ) * (5 / 3 : ℝ) ^ 32 ≤ Real.exp (175 / 9 : ℝ) := by
      calc (13 : ℝ) * (5 / 3 : ℝ) ^ 32
          ≤ (163 / 60 : ℝ) ^ 19 := by norm_num
        _ ≤ (Real.exp 1) ^ 19 := pow_le_pow_left₀ (by norm_num) hexp1 19
        _ = Real.exp 19 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ Real.exp (175 / 9 : ℝ) := Real.exp_le_exp.mpr (by norm_num)
    have hmul := mul_le_mul_of_nonneg_right hpow19 (le_of_lt (Real.exp_pos (-(256 / 9 : ℝ))))
    rw [← Real.exp_add] at hmul
    have hexp_pow : (Real.exp (-(8 / 9 : ℝ))) ^ 32 = Real.exp (-(256 / 9 : ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; norm_num
    rw [mul_pow, hexp_pow]
    have h1 : (175 / 9 : ℝ) + -(256 / 9 : ℝ) = -9 := by norm_num
    rw [h1] at hmul
    linarith
  -- Step 2: `(5/3) * exp (-8/9) ≤ exp (-9/32)`
  have h1_step : (5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ)) ≤ Real.exp (-(9 / 32 : ℝ)) := by
    have hquad : (5 / 3 : ℝ) ≤ Real.exp (175 / 288 : ℝ) := by
      have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 175 / 288) 3
      simp [Finset.sum_range_succ, Nat.factorial] at hsum
      linarith
    have hmul := mul_le_mul_of_nonneg_right hquad (le_of_lt (Real.exp_pos (-(8 / 9 : ℝ))))
    rw [← Real.exp_add] at hmul
    have h1 : (175 / 288 : ℝ) + -(8 / 9 : ℝ) = -(9 / 32 : ℝ) := by norm_num
    rwa [h1] at hmul
  -- Step 3: Split `m = 32 * d + (m - 32 * d)`
  set k := m - 32 * d
  have hm_eq : m = 32 * d + k := by omega
  have h1 : (13 : ℝ) ^ d * ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ (32 * d) ≤
      Real.exp (-(9 : ℝ) * (d : ℝ)) := by
    rw [pow_mul, ← mul_pow]
    calc ((13 : ℝ) * ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ 32) ^ d
        ≤ (Real.exp (-9)) ^ d := pow_le_pow_left₀ (by positivity) h32_base d
      _ = Real.exp (-(9 : ℝ) * (d : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h2 : ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ k ≤ Real.exp (-(9 / 32 : ℝ) * (k : ℝ)) := by
    calc ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ k
        ≤ (Real.exp (-(9 / 32 : ℝ))) ^ k := pow_le_pow_left₀ (by positivity) h1_step k
      _ = Real.exp (-(9 / 32 : ℝ) * (k : ℝ)) := by rw [← Real.exp_nat_mul]; congr 1; ring
  calc (13 : ℝ) ^ d * ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ m
      = ((13 : ℝ) ^ d * ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ (32 * d)) *
          ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ k := by rw [hm_eq, pow_add]; ring
    _ ≤ Real.exp (-(9 : ℝ) * (d : ℝ)) * Real.exp (-(9 / 32 : ℝ) * (k : ℝ)) :=
          mul_le_mul h1 h2 (by positivity) (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-(9 / 32 : ℝ) * (m : ℝ)) := by
          rw [← Real.exp_add]
          congr 1
          have hcast : (m : ℝ) = 32 * (d : ℝ) + (k : ℝ) := by exact_mod_cast hm_eq
          rw [hcast]; ring

/-- Pointwise `χ²_m` Chernoff bound for a single unit vector `u₀` (`‖u₀‖ = 1`):
`P(∑ i, ⟪a i, u₀⟫^2 > (25/9) m) ≤ ((5/3) * exp (-8/9))^m`. -/
theorem prob_chisq_unit_tail {m : ℕ} {u₀ : E} (hu₀ : ‖u₀‖ = 1) :
    iidStdGaussian E m {a : Fin m → E | (25 / 9 : ℝ) * (m : ℝ) < ∑ i : Fin m, ⟪a i, u₀⟫_ℝ ^ 2} ≤
      ENNReal.ofReal (((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ m) := by
  let Z : Fin m → (Fin m → E) → ℝ := fun i a => ⟪a i, u₀⟫_ℝ ^ 2
  have hsub : {a : Fin m → E | (25 / 9 : ℝ) * (m : ℝ) < ∑ i : Fin m, ⟪a i, u₀⟫_ℝ ^ 2} ⊆
      {a : Fin m → E | (25 / 9 : ℝ) * (m : ℝ) ≤ ∑ i : Fin m, Z i a} :=
    fun _ ha => le_of_lt (show (25 / 9 : ℝ) * (m : ℝ) < ∑ i : Fin m, Z i _ from ha)
  refine le_trans (measure_mono hsub) ?_
  -- Apply Chernoff bound `measure_ge_le_exp_mul_mgf` at `t = 8 / 25`
  have hinner_meas : Measurable (fun x : E => ⟪x, u₀⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  have hZ_each_meas : Measurable (fun x : E => ⟪x, u₀⟫_ℝ ^ 2) := hinner_meas.pow_const 2
  have hZ_meas : ∀ i : Fin m, Measurable (Z i) := fun i => hZ_each_meas.comp (measurable_pi_apply i)
  have h_indep : iIndepFun Z (iidStdGaussian E m) := by
    unfold iidStdGaussian
    exact iIndepFun_pi (fun _ => hZ_each_meas.aemeasurable)
  have hmap : ∀ i : Fin m,
      (iidStdGaussian E m).map (fun a : Fin m → E => ⟪a i, u₀⟫_ℝ) = gaussianReal 0 1 := by
    intro i
    have hcomp : (fun a : Fin m → E => ⟪a i, u₀⟫_ℝ) =
        (fun x : E => ⟪x, u₀⟫_ℝ) ∘ (fun a : Fin m → E => a i) := rfl
    rw [hcomp, ← Measure.map_map hinner_meas (measurable_pi_apply i),
        iidStdGaussian_map_eval, stdGaussian_map_inner_unit hu₀]
  have h_int_each : ∀ i : Fin m,
      Integrable (fun a : Fin m → E => Real.exp ((8 / 25 : ℝ) * Z i a)) (iidStdGaussian E m) := by
    intro i
    have h1 : Integrable (fun z : ℝ => Real.exp ((8 / 25 : ℝ) * z ^ 2))
        ((iidStdGaussian E m).map (fun a : Fin m → E => ⟪a i, u₀⟫_ℝ)) := by
      rw [hmap i]
      exact integrable_exp_mul_sq_gaussianReal (lam := 8 / 25) (by norm_num)
    exact (integrable_map_measure (g := fun z : ℝ => Real.exp ((8 / 25 : ℝ) * z ^ 2))
      (by fun_prop) (hinner_meas.comp (measurable_pi_apply i)).aemeasurable).mp h1
  have h_int_sum : Integrable (fun a : Fin m → E => Real.exp ((8 / 25 : ℝ) * ∑ i : Fin m, Z i a))
      (iidStdGaussian E m) := by
    simpa using h_indep.integrable_exp_mul_sum hZ_meas (s := Finset.univ) (fun i _ => h_int_each i)
  have h_mgf_each : ∀ i : Fin m, mgf (Z i) (iidStdGaussian E m) (8 / 25) = 5 / 3 := by
    intro i
    unfold mgf
    have h1 : ∫ a : Fin m → E, Real.exp ((8 / 25 : ℝ) * Z i a) ∂(iidStdGaussian E m) =
        ∫ z : ℝ, Real.exp ((8 / 25 : ℝ) * z ^ 2) ∂(gaussianReal 0 1) := by
      rw [← hmap i]
      exact (integral_map (φ := fun a : Fin m → E => ⟪a i, u₀⟫_ℝ)
        (f := fun z : ℝ => Real.exp ((8 / 25 : ℝ) * z ^ 2))
        (hinner_meas.comp (measurable_pi_apply i)).aemeasurable (by fun_prop)).symm
    rw [h1, integral_exp_mul_sq_gaussianReal (by norm_num)]
    have hsq : Real.sqrt (1 - 2 * (8 / 25 : ℝ)) = 3 / 5 := by
      rw [show (1 - 2 * (8 / 25 : ℝ)) = (3 / 5 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hsq]; norm_num
  have h_mgf_sum : mgf (fun a => ∑ i : Fin m, Z i a) (iidStdGaussian E m) (8 / 25) = (5 / 3 : ℝ) ^ m := by
    have hprod := h_indep.mgf_sum hZ_meas Finset.univ (t := 8 / 25)
    have hfun : (∑ i : Fin m, Z i) = (fun a => ∑ i : Fin m, Z i a) := by
      ext a; simp
    rw [hfun] at hprod
    simp only [h_mgf_each, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
    exact hprod
  have hchernoff := measure_ge_le_exp_mul_mgf (μ := iidStdGaussian E m)
    (X := fun a : Fin m → E => ∑ i : Fin m, Z i a)
    ((25 / 9 : ℝ) * (m : ℝ)) (by norm_num : (0 : ℝ) ≤ 8 / 25) h_int_sum
  rw [h_mgf_sum] at hchernoff
  have hsimp : Real.exp (-(8 / 25 : ℝ) * ((25 / 9 : ℝ) * (m : ℝ))) * (5 / 3 : ℝ) ^ m =
      ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ m := by
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [mul_comm]
    congr 2; ring
  rw [hsimp] at hchernoff
  rw [← ENNReal.ofReal_toReal (measure_ne_top (iidStdGaussian E m) _)]
  exact ENNReal.ofReal_le_ofReal hchernoff

/-- **Stage 2 Main Theorem (Unconditional Gaussian Operator Norm Event)**:
For any finite-dimensional real inner product space `E` and any `m ≥ 32 * finrank ℝ E`,
`iidStdGaussian E m {a | ¬ ∀ w, ∑ i, ⟪a i, w⟫^2 ≤ 4 m ‖w‖^2} ≤ exp (-(9/32) m)`. -/
theorem prob_operator_norm_event {m : ℕ} (hd : 32 * Module.finrank ℝ E ≤ m) :
    iidStdGaussian E m {a : Fin m → E | ¬ ∀ w : E, ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 ≤ 4 * (m : ℝ) * ‖w‖ ^ 2} ≤
      ENNReal.ofReal (Real.exp (-(9 / 32 : ℝ) * (m : ℝ))) := by
  -- Construct a fixed `(1/6)`-net `N` of `S^{d-1}` with `N.card ≤ 13^d`
  obtain ⟨N, hN_unit, hN_cover, hN_card⟩ := exists_sphere_eps_net E (by norm_num : (0 : ℝ) < 1 / 6)
  have h13 : (1 + 2 / (1 / 6 : ℝ)) = 13 := by norm_num
  rw [h13] at hN_card
  -- Inclusion of bad operator-norm event into the finite union over `u₀ ∈ N`
  have hsub : {a : Fin m → E | ¬ ∀ w : E, ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 ≤ 4 * (m : ℝ) * ‖w‖ ^ 2} ⊆
      ⋃ u₀ ∈ N, {a : Fin m → E | (25 / 9 : ℝ) * (m : ℝ) < ∑ i : Fin m, ⟪a i, u₀⟫_ℝ ^ 2} := by
    intro a ha
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hnot
    exact ha (op_norm_of_one_sixth_net a N hN_cover hnot)
  calc iidStdGaussian E m {a | ¬ ∀ w : E, ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 ≤ 4 * (m : ℝ) * ‖w‖ ^ 2}
      ≤ iidStdGaussian E m (⋃ u₀ ∈ N, {a | (25 / 9 : ℝ) * (m : ℝ) < ∑ i : Fin m, ⟪a i, u₀⟫_ℝ ^ 2}) :=
        measure_mono hsub
    _ ≤ ∑ u₀ ∈ N, iidStdGaussian E m {a | (25 / 9 : ℝ) * (m : ℝ) < ∑ i : Fin m, ⟪a i, u₀⟫_ℝ ^ 2} :=
        measure_biUnion_finset_le N _
    _ ≤ ∑ _u₀ ∈ N, ENNReal.ofReal (((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ m) :=
        Finset.sum_le_sum (fun u₀ hu₀ => prob_chisq_unit_tail (hN_unit u₀ hu₀))
    _ = ENNReal.ofReal ((N.card : ℝ) * ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ m) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((13 : ℝ) ^ Module.finrank ℝ E * ((5 / 3 : ℝ) * Real.exp (-(8 / 9 : ℝ))) ^ m) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hN_card (by positivity))
    _ ≤ ENNReal.ofReal (Real.exp (-(9 / 32 : ℝ) * (m : ℝ))) :=
        ENNReal.ofReal_le_ofReal (thirteen_pow_d_mul_chisq_le hd)

end Research107
