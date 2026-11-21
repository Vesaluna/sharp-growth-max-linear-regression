import Research107.MainTheorem
import Research107.GaussianModel
import Research107.GaussianOperatorNorm
import Research107.ConeConcentration
import Research107.FlipConcentration
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators InnerProductSpace ENNReal NNReal Classical

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Stage 5: Unconditional Probabilistic Main Theorem 4 (Zero Event Hypotheses!) -/

/-- Cardinality bound on ordered pairs `{(j, k) : Fin r × Fin r | j < k}`:
its cardinality is positive for `r ≥ 2` and at most `r^2 / 2`. -/
private lemma card_ordered_pairs_bounds {r : ℕ} (hr : 2 ≤ r) :
    let pairs := (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2)
    0 < pairs.card ∧ (pairs.card : ℝ) ≤ (r : ℝ) ^ 2 / 2 := by
  intro pairs
  have hpos : 0 < pairs.card := by
    refine Finset.card_pos.mpr ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_⟩
    simp [pairs, Fin.mk_lt_mk]
  refine ⟨hpos, ?_⟩
  -- `pairs` and `pairs_rev` are disjoint subsets of `Fin r × Fin r` of equal cardinality
  let pairs_rev := (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.2 < p.1)
  have hdisj : Disjoint pairs pairs_rev := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 : p.1 < p.2 := (Finset.mem_filter.mp hp1).2
    have h2 : p.2 < p.1 := (Finset.mem_filter.mp hp2).2
    exact lt_asymm h1 h2
  have hcard_eq : pairs.card = pairs_rev.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simp only [pairs, pairs_rev, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact hp
    · intro p₁ _ p₂ _ heq
      have h1 : p₁.2 = p₂.2 := congrArg Prod.fst heq
      have h2 : p₁.1 = p₂.1 := congrArg Prod.snd heq
      exact Prod.ext h2 h1
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      simp only [pairs, pairs_rev, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢; exact hq
  have hle_nat : 2 * pairs.card ≤ r * r := by
    have hunion : (pairs ∪ pairs_rev).card ≤ (Finset.univ : Finset (Fin r × Fin r)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [Finset.card_union_of_disjoint hdisj, ← hcard_eq, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin] at hunion
    omega
  have hle_real : (2 : ℝ) * (pairs.card : ℝ) ≤ (r : ℝ) ^ 2 := by
    have : ((2 * pairs.card : ℕ) : ℝ) ≤ ((r * r : ℕ) : ℝ) := by exact_mod_cast hle_nat
    push_cast at this
    linarith
  linarith

/-- Any population cone norm `popConeNorm β_star j u` for `‖u‖ = 1` is at most `√(2 / π) < 1`. -/
private lemma popConeNorm_le_sqrt_two_div_pi {r : ℕ} (β_star : Fin r → E) (j : Fin r)
    {u : E} (hu : ‖u‖ = 1) :
    popConeNorm β_star j u ≤ Real.sqrt (2 / Real.pi) := by
  unfold popConeNorm
  have h1 : Integrable (fun a : E => if a ∈ activeCone β_star j then |⟪a, u⟫_ℝ| else 0) (stdGaussian E) := by
    have hinner : Measurable (fun a : E => ⟪a, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    have hdom : Integrable (fun a : E => |⟪a, u⟫_ℝ|) (stdGaussian E) := by
      have hg : Integrable (fun z : ℝ => |z|) ((stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ)) := by
        rw [stdGaussian_map_inner_unit hu]
        have := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
        exact this.abs
      exact (integrable_map_measure (g := fun z : ℝ => |z|)
        continuous_abs.aestronglyMeasurable hinner.aemeasurable).mp hg
    refine hdom.mono' (Measurable.ite (measurableSet_activeCone β_star j)
      (continuous_abs.measurable.comp hinner) measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs]
    split_ifs <;> simp [abs_nonneg]
  have h2 : Integrable (fun a : E => |⟪a, u⟫_ℝ|) (stdGaussian E) := by
    have hinner : Measurable (fun a : E => ⟪a, u⟫_ℝ) := (continuous_id.inner continuous_const).measurable
    have hg : Integrable (fun z : ℝ => |z|) ((stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ)) := by
      rw [stdGaussian_map_inner_unit hu]
      have := (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl
      exact this.abs
    exact (integrable_map_measure (g := fun z : ℝ => |z|)
      continuous_abs.aestronglyMeasurable hinner.aemeasurable).mp hg
  have hle : ∫ a : E, (if a ∈ activeCone β_star j then |⟪a, u⟫_ℝ| else 0) ∂(stdGaussian E) ≤
      ∫ a : E, |⟪a, u⟫_ℝ| ∂(stdGaussian E) :=
    integral_mono h1 h2 (fun a => by split_ifs <;> [exact le_rfl; exact abs_nonneg _])
  rw [integral_abs_inner_stdGaussian, hu, one_mul] at hle
  exact hle

/-- **THEOREM 4 (Unconditional Probabilistic Verification — Zero Event Hypotheses!)**:
For any nontrivial finite-dimensional Euclidean space `E` (`d = finrank ℝ E ≥ 1`), `r ≥ 2`,
separated parameters `β_star` (`Δ_min > 0`), population cone margin `α_min > 0`, oblivious corruption
signs `s : Fin m → {1, -1}` with corrupted fraction `α ∈ [0, 1/2)`, failure probability `δ_fail ∈ (0, 1)`,
and sample size `m` satisfying the **exact verbatim sample complexity of Theorem 4** in `claims_and_proofs.md`:
with `iidStdGaussian E m`-probability at least `1 - δ_fail`, simultaneously for ALL arbitrary
(possibly unbounded, data-dependent) corruption vectors `ξ` supported on `{i | s i = -1}`:
1. Uniform macroscopic sharp growth `(γ/4) * frobNorm Δ ≤ f(β* + Δ) - f(β*)` for all `frobNorm Δ ≤ ρ`;
2. Global `2`-Lipschitzness `|f(β) - f(β')| ≤ 2 * frobNorm (β - β')`;
3. In the noiseless case (`ξ ≡ 0`), half-radius distance identity `‖β - β*‖_F ≤ ‖β - z‖_F` for every
   global minimizer `z` (`f(z) = 0`) and every `β ∈ B(β*, ρ/2)`.

No `h_event_op`, no `h_event_cone_net`, no `h_event_flip_net`, no `h_active` hypotheses remain! -/
theorem theorem4_unconditional_probabilistic [Nontrivial E]
    {m r : ℕ} (hm : 0 < m) (hr : 2 ≤ r)
    (β_star : Fin r → E)
    (s : Fin m → ℝ) (hs_pm : ∀ i : Fin m, s i = 1 ∨ s i = -1)
    {Δ_min α α_min δ_fail : ℝ}
    (hΔmin : 0 < Δ_min)
    (h_sep : ∀ j k : Fin r, j ≠ k → Δ_min ≤ ‖β_star j - β_star k‖)
    (hα0 : 0 ≤ α) (hα1 : α < 1 / 2)
    (h_frac : (1 / (m : ℝ)) * ∑ i : Fin m, s i = 1 - 2 * α)
    (hαmin : 0 < α_min)
    (h_cone_pop : ∀ (j : Fin r) (u : E), ‖u‖ = 1 → α_min ≤ popConeNorm β_star j u)
    (hδ0 : 0 < δ_fail) (hδ1 : δ_fail < 1)
    -- Exact verbatim sample-size hypotheses of Theorem 4 in `claims_and_proofs.md`:
    (_hm_op_d : 16 * (Module.finrank ℝ E : ℝ) ≤ (m : ℝ))
    (hm_op_log : (32 / 9 : ℝ) * Real.log (3 / δ_fail) ≤ (m : ℝ))
    (hm_cone : (64 / ((1 - 2 * α) * α_min) ^ 2) *
      ((Module.finrank ℝ E : ℝ) * Real.log (1 + 16 / ((1 - 2 * α) * α_min)) +
        Real.log (3 * (r : ℝ) / δ_fail)) ≤ (m : ℝ))
    (hm_flip : (22 / (3 * (((1 - 2 * α) * α_min) / (26 * ((r : ℝ) - 1))))) *
      ((Module.finrank ℝ E : ℝ) * Real.log (9 / (((1 - 2 * α) * α_min) / (26 * ((r : ℝ) - 1)))) +
        Real.log (3 * ((r : ℝ) ^ 2 / 2) / δ_fail)) ≤ (m : ℝ)) :
    let hr_pos : 0 < r := by omega
    let γ := (1 - 2 * α) * α_min
    let η := γ / (26 * ((r : ℝ) - 1))
    let ρ := (η / Real.sqrt 2) * Δ_min
    1 - ENNReal.ofReal δ_fail ≤ iidStdGaussian E m {a : Fin m → E |
      ∀ (ξ : Fin m → ℝ), (∀ i : Fin m, s i = 1 → ξ i = 0) →
        let y := fun i => maxLinearPred hr_pos (a i) β_star + ξ i
        (∀ Δ : Fin r → E, frobNorm Δ ≤ ρ →
          (γ / 4) * frobNorm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
            l1EmpiricalLoss hr_pos a y β_star ∧
          (γ / 4) * blockL1L2Norm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
            l1EmpiricalLoss hr_pos a y β_star) ∧
        (∀ β β' : Fin r → E,
          |l1EmpiricalLoss hr_pos a y β - l1EmpiricalLoss hr_pos a y β'| ≤
            2 * frobNorm (fun j => β j - β' j)) ∧
        ((∀ i : Fin m, ξ i = 0) →
          ∀ β z : Fin r → E,
            frobNorm (fun j => β j - β_star j) ≤ ρ / 2 →
            l1EmpiricalLoss hr_pos a y z = 0 →
            frobNorm (fun j => β j - β_star j) ≤ frobNorm (fun j => β j - z j))} := by
  intro hr_pos γ η ρ
  set d := Module.finrank ℝ E
  -- Step 1: Automatic bounds `α_min < 1`, `0 < γ < 1`, `0 < η ≤ 1/4`, and `32 * d ≤ m`!
  have h_exists_unit : ∃ u : E, ‖u‖ = 1 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    exact ⟨(‖x‖⁻¹) • x, by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ (ne_of_gt hp)]⟩
  have hαmin_lt_one : α_min < 1 := by
    rcases h_exists_unit with ⟨u, hu⟩
    have h1 := h_cone_pop ⟨0, hr_pos⟩ u hu
    have h2 := popConeNorm_le_sqrt_two_div_pi β_star ⟨0, hr_pos⟩ hu
    have hpi_gt : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    have hlt : Real.sqrt (2 / Real.pi) < 1 := by
      rw [Real.sqrt_lt' (by norm_num), one_pow, div_lt_one Real.pi_pos]
      linarith
    linarith
  have hγ_pos : 0 < γ := mul_pos (by linarith) hαmin
  have hγ_lt_one : γ < 1 := by
    have h1m : 1 - 2 * α ≤ 1 := by linarith
    nlinarith
  have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hη_pos : 0 < η := div_pos hγ_pos (by linarith)
  have hη_le_quarter : η ≤ 1 / 4 := by
    dsimp [η]
    rw [div_le_iff₀ (by linarith : 0 < 26 * ((r : ℝ) - 1))]
    nlinarith
  have hη_lt_one : η < 1 := by linarith
  -- Deduce `32 * d ≤ m` automatically from `hm_cone` (since `64 / γ^2 * log(1 + 16/γ) > 64 * log 17 > 64 > 32`)!
  have hd_32 : 32 * d ≤ m := by
    have hlog17 : (1 : ℝ) ≤ Real.log (1 + 16 / γ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have hexp1 : Real.exp 1 ≤ 4 := by
        have hhalf : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by
          linarith [Real.add_one_le_exp (-(1 / 2 : ℝ))]
        have hmul : Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ)) = 1 := by
          rw [← Real.exp_add]; norm_num
        have hle2 : Real.exp (1 / 2 : ℝ) ≤ 2 := by
          have hp := Real.exp_pos (1 / 2 : ℝ)
          nlinarith
        have hsq : Real.exp 1 = Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) := by
          rw [← Real.exp_add]; norm_num
        have hp := Real.exp_pos (1 / 2 : ℝ)
        nlinarith
      have h17 : (17 : ℝ) ≤ 1 + 16 / γ := by
        have : (16 : ℝ) ≤ 16 / γ := by
          rw [le_div_iff₀ hγ_pos]; nlinarith
        linarith
      linarith
    have hlog_pos : 0 ≤ Real.log (3 * (r : ℝ) / δ_fail) := by
      apply Real.log_nonneg
      rw [one_le_div hδ0]
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      linarith
    have h64 : (64 : ℝ) ≤ 64 / γ ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hγ_pos)]
      nlinarith
    have hreal : (32 : ℝ) * (d : ℝ) ≤ (m : ℝ) := by
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have h1 : (d : ℝ) ≤ (d : ℝ) * Real.log (1 + 16 / γ) + Real.log (3 * (r : ℝ) / δ_fail) := by
        nlinarith
      have h2 : (64 : ℝ) * (d : ℝ) ≤ (64 / γ ^ 2) *
          ((d : ℝ) * Real.log (1 + 16 / γ) + Real.log (3 * (r : ℝ) / δ_fail)) := by
        nlinarith
      linarith
    exact_mod_cast hreal
  -- Step 2: Assemble the 4 bad events and their exact measure bounds!
  have h_distinct : ∀ j k : Fin r, j ≠ k → β_star j ≠ β_star k := by
    intro j k hjk heq
    have h1 := h_sep j k hjk
    rw [heq, sub_self, norm_zero] at h1
    linarith
  have hs_abs : ∀ i : Fin m, |s i| ≤ 1 := by
    intro i; rcases hs_pm i with h | h <;> simp [h]
  -- Bad Event A: non-strict active cone membership (measure 0!)
  let B_active : Set (Fin m → E) :=
    {a | ¬ ∀ i : Fin m, ∃ j₀ : Fin r, a i ∈ activeCone β_star j₀}
  have hB_active : iidStdGaussian E m B_active = 0 :=
    ae_iff.mp (iidStdGaussian_ae_active hr_pos β_star h_distinct)
  -- Bad Event 0: operator norm `> 2 √m`
  let B_op : Set (Fin m → E) :=
    {a | ¬ ∀ w : E, ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 ≤ 4 * (m : ℝ) * ‖w‖ ^ 2}
  have hB_op : iidStdGaussian E m B_op ≤ ENNReal.ofReal (Real.exp (-(9 / 32 : ℝ) * (m : ℝ))) :=
    prob_operator_norm_event hd_32
  -- Bad Event 1: fixed `(γ/8)`-net cone norm failure
  have h_pop_cone : ∀ (j : Fin r) (u : E), ‖u‖ = 1 →
      γ ≤ ((1 / (m : ℝ)) * ∑ i : Fin m, s i) * popConeNorm β_star j u := by
    intro j u hu
    rw [h_frac]
    dsimp [γ]
    exact mul_le_mul_of_nonneg_left (h_cone_pop j u hu) (by linarith)
  obtain ⟨N_cone, _, hN_cone_cover, hB_cone⟩ := prob_cone_net_event hm β_star s hs_abs hγ_pos h_pop_cone
  let B_cone : Set (Fin m → E) :=
    {a | ¬ ∀ (j : Fin r), ∀ u₀ ∈ N_cone, 3 * γ / 4 ≤ signedConeNorm a s β_star j u₀}
  have hB_cone' : iidStdGaussian E m B_cone ≤
      ENNReal.ofReal ((r : ℝ) * (1 + 16 / γ) ^ d * Real.exp (-(m : ℝ) * γ ^ 2 / 64)) := hB_cone
  -- Bad Event 2: fixed `(η/4)`-net flip surrogate failure
  obtain ⟨N_flip, _, hN_flip_cover, hB_flip⟩ := prob_flip_net_event hm β_star h_distinct hη_pos hη_le_quarter
  let B_flip : Set (Fin m → E) :=
    {a | ¬ ∀ (j k : Fin r), j < k → ∀ u₀ ∈ N_flip,
      (1 / (m : ℝ)) * ∑ i : Fin m,
        phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u₀⟫_ℝ ≤
      (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η}
  -- Step 3: Total bad-event measure `≤ ENNReal.ofReal δ_fail` via `theorem4_tail_algebra`!
  let pairs := (Finset.univ : Finset (Fin r × Fin r)).filter (fun p => p.1 < p.2)
  have hB_flip' : iidStdGaussian E m B_flip ≤
      ENNReal.ofReal ((pairs.card : ℝ) * (9 / η) ^ d * Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) := hB_flip
  obtain ⟨hM_pos, hM_le⟩ := card_ordered_pairs_bounds hr
  have hm_flip_M : (22 / (3 * η)) *
      ((d : ℝ) * Real.log (9 / η) + Real.log (3 * (pairs.card : ℝ) / δ_fail)) ≤ (m : ℝ) := by
    have hlog_le : Real.log (3 * (pairs.card : ℝ) / δ_fail) ≤ Real.log (3 * ((r : ℝ) ^ 2 / 2) / δ_fail) := by
      refine Real.log_le_log (div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hM_pos)) hδ0) ?_
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM_le (by norm_num)) (le_of_lt hδ0)
    have hmul : (22 / (3 * η)) *
        ((d : ℝ) * Real.log (9 / η) + Real.log (3 * (pairs.card : ℝ) / δ_fail)) ≤
        (22 / (3 * η)) *
        ((d : ℝ) * Real.log (9 / η) + Real.log (3 * ((r : ℝ) ^ 2 / 2) / δ_fail)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hlog_le) (show 0 ≤ 22 / (3 * η) by positivity)
    exact le_trans hmul hm_flip
  have htail_sum := theorem4_tail_algebra hγ_pos hη_pos hη_lt_one hδ0 hr_pos hM_pos
    hm_op_log hm_cone hm_flip_M
  let B_all : Set (Fin m → E) := B_active ∪ B_op ∪ B_cone ∪ B_flip
  have hB_all : iidStdGaussian E m B_all ≤ ENNReal.ofReal δ_fail := by
    have hstep1 : iidStdGaussian E m B_all ≤
        iidStdGaussian E m B_active + iidStdGaussian E m B_op +
        iidStdGaussian E m B_cone + iidStdGaussian E m B_flip := by
      calc iidStdGaussian E m B_all
          ≤ iidStdGaussian E m (B_active ∪ B_op ∪ B_cone) + iidStdGaussian E m B_flip :=
            measure_union_le _ _
        _ ≤ (iidStdGaussian E m (B_active ∪ B_op) + iidStdGaussian E m B_cone) + iidStdGaussian E m B_flip :=
            add_le_add (measure_union_le _ _) le_rfl
        _ ≤ ((iidStdGaussian E m B_active + iidStdGaussian E m B_op) + iidStdGaussian E m B_cone) +
              iidStdGaussian E m B_flip :=
            add_le_add (add_le_add (measure_union_le _ _) le_rfl) le_rfl
    have hstep2 :
        iidStdGaussian E m B_active + iidStdGaussian E m B_op +
        iidStdGaussian E m B_cone + iidStdGaussian E m B_flip ≤
        0 + ENNReal.ofReal (Real.exp (-(9 / 32 : ℝ) * (m : ℝ))) +
        ENNReal.ofReal ((r : ℝ) * (1 + 16 / γ) ^ d * Real.exp (-(m : ℝ) * γ ^ 2 / 64)) +
        ENNReal.ofReal ((pairs.card : ℝ) * (9 / η) ^ d * Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) := by
      rw [hB_active]
      exact add_le_add (add_le_add (add_le_add le_rfl hB_op) hB_cone') hB_flip'
    have hstep3 :
        0 + ENNReal.ofReal (Real.exp (-(9 / 32 : ℝ) * (m : ℝ))) +
        ENNReal.ofReal ((r : ℝ) * (1 + 16 / γ) ^ d * Real.exp (-(m : ℝ) * γ ^ 2 / 64)) +
        ENNReal.ofReal ((pairs.card : ℝ) * (9 / η) ^ d * Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) =
        ENNReal.ofReal (Real.exp (-(9 / 32 : ℝ) * (m : ℝ)) +
          (r : ℝ) * (1 + 16 / γ) ^ d * Real.exp (-(m : ℝ) * γ ^ 2 / 64) +
          (pairs.card : ℝ) * (9 / η) ^ d * Real.exp (-(3 / 22 : ℝ) * (m : ℝ) * η)) := by
      rw [zero_add, ← ENNReal.ofReal_add (le_of_lt (Real.exp_pos _)) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact le_trans (le_trans hstep1 hstep2) (by rw [hstep3]; exact ENNReal.ofReal_le_ofReal htail_sum)
  -- Step 4: On `B_allᶜ`, invoke `main_theorem4_assembled` for EVERY corruption vector `ξ`!
  let Good : Set (Fin m → E) := {a : Fin m → E |
      ∀ (ξ : Fin m → ℝ), (∀ i : Fin m, s i = 1 → ξ i = 0) →
        let y := fun i => maxLinearPred hr_pos (a i) β_star + ξ i
        (∀ Δ : Fin r → E, frobNorm Δ ≤ ρ →
          (γ / 4) * frobNorm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
            l1EmpiricalLoss hr_pos a y β_star ∧
          (γ / 4) * blockL1L2Norm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
            l1EmpiricalLoss hr_pos a y β_star) ∧
        (∀ β β' : Fin r → E,
          |l1EmpiricalLoss hr_pos a y β - l1EmpiricalLoss hr_pos a y β'| ≤
            2 * frobNorm (fun j => β j - β' j)) ∧
        ((∀ i : Fin m, ξ i = 0) →
          ∀ β z : Fin r → E,
            frobNorm (fun j => β j - β_star j) ≤ ρ / 2 →
            l1EmpiricalLoss hr_pos a y z = 0 →
            frobNorm (fun j => β j - β_star j) ≤ frobNorm (fun j => β j - z j))}
  have huniv_sub : Set.univ ⊆ B_all ∪ Good := by
    intro a _
    by_cases ha : a ∈ B_all
    · exact Or.inl ha
    · right
      have hna : a ∉ B_active := fun h => ha (Or.inl (Or.inl (Or.inl h)))
      have hno : a ∉ B_op := fun h => ha (Or.inl (Or.inl (Or.inr h)))
      have hnc : a ∉ B_cone := fun h => ha (Or.inl (Or.inr h))
      have hnf : a ∉ B_flip := fun h => ha (Or.inr h)
      have h_act : ∀ i : Fin m, ∃ j₀ : Fin r, a i ∈ activeCone β_star j₀ := not_not.mp hna
      have h_op : ∀ w : E, ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 ≤ 4 * (m : ℝ) * ‖w‖ ^ 2 := not_not.mp hno
      have h_cone_n : ∀ (j : Fin r), ∀ u₀ ∈ N_cone, 3 * γ / 4 ≤ signedConeNorm a s β_star j u₀ :=
        not_not.mp hnc
      have h_flip_n : ∀ (j k : Fin r), j < k → ∀ u₀ ∈ N_flip,
          (1 / (m : ℝ)) * ∑ i : Fin m,
            phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u₀⟫_ℝ ≤
          (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η := not_not.mp hnf
      intro ξ hξ
      have h_signs : ∀ i : Fin m, (s i = 1 ∧ ξ i = 0) ∨ s i = -1 := by
        intro i
        rcases hs_pm i with h1 | hm1
        · exact Or.inl ⟨h1, hξ i h1⟩
        · exact Or.inr hm1
      have h_cone_net_pt : ∀ (j : Fin r) (u : E), ‖u‖ = 1 →
          ∃ u₀ : E, ‖u - u₀‖ ≤ γ / 8 ∧ 3 * γ / 4 ≤ signedConeNorm a s β_star j u₀ := by
        intro j u hu
        rcases hN_cone_cover u hu with ⟨u₀, hu₀N, hdist⟩
        exact ⟨u₀, hdist, h_cone_n j u₀ hu₀N⟩
      have h_flip_net_pt : ∀ (j k : Fin r), j < k → ∀ (u : E), ‖u‖ = 1 →
          ∃ u₀ : E, ‖u - u₀‖ ≤ η / 4 ∧
            (1 / (m : ℝ)) * ∑ i : Fin m,
              phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u₀⟫_ℝ ≤
            (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η := by
        intro j k hjk u hu
        rcases hN_flip_cover u hu with ⟨u₀, hu₀N, hdist⟩
        exact ⟨u₀, hdist, h_flip_n j k hjk u₀ hu₀N⟩
      exact main_theorem4_assembled hm hr a β_star s ξ γ Δ_min hγ_pos hΔmin h_sep
        h_signs h_act h_op h_cone_net_pt h_flip_net_pt
  -- Conclude `1 - ofReal δ_fail ≤ iidStdGaussian E m Good`!
  have h1_le : (1 : ℝ≥0∞) ≤ iidStdGaussian E m B_all + iidStdGaussian E m Good := by
    calc (1 : ℝ≥0∞) = iidStdGaussian E m Set.univ := (measure_univ).symm
      _ ≤ iidStdGaussian E m (B_all ∪ Good) := measure_mono huniv_sub
      _ ≤ iidStdGaussian E m B_all + iidStdGaussian E m Good := measure_union_le _ _
  have h1_le' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ_fail + iidStdGaussian E m Good :=
    le_trans h1_le (add_le_add hB_all le_rfl)
  exact tsub_le_iff_left.mpr h1_le'

/-! ### Stage 5.2: Unconditional Lemma 3.3 (Gaussian Bathtub Bound) & `π_min` Bridge to Theorem 4 -/

/-- **Lemma 3.3 (Full Measure-Theoretic Gaussian Bathtub Lower Bound)**:
For any finite-dimensional real inner product space `E`, any measurable set `C ⊆ E` with
Gaussian measure `stdGaussian E C ≥ p` (`p ∈ [0, 1]`), and any unit vector `u ∈ E` (`‖u‖ = 1`):
`(√(2π) / 6) * p^2 ≤ ∫ a, (if a ∈ C then |⟪a, u⟫| else 0) ∂(stdGaussian E)`.

Proof avoids quantile inversion by setting `t := √(π / 2) * p` directly: since the `N(0, 1)`
density is bounded above by `1 / √(2π)`, `ℙ(|Z| ≤ t) ≤ (2t)/√(2π) = p ≤ ℙ(C)`, so the
pointwise bathtub inequality `(1_C - 1_{|Z| ≤ t})(|Z| - t) ≥ 0` integrates directly to
`∫ 1_C |Z| ≥ ∫ 1_{|Z| ≤ t} |Z| = √(2/π)(1 - exp(-π p^2 / 4)) ≥ (√(2π) / 6) p^2`. -/
theorem lemma33_gaussian_bathtub
    {C : Set E} (hC : MeasurableSet C)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hCp : ENNReal.ofReal p ≤ stdGaussian E C)
    {u : E} (hu : ‖u‖ = 1) :
    (Real.sqrt (2 * Real.pi) / 6) * p ^ 2 ≤
      ∫ a : E, (if a ∈ C then |⟪a, u⟫_ℝ| else 0) ∂(stdGaussian E) := by
  set t : ℝ := Real.sqrt (Real.pi / 2) * p
  have ht0 : 0 ≤ t := mul_nonneg (Real.sqrt_nonneg _) hp0
  have hmap : (stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ) = gaussianReal 0 1 :=
    stdGaussian_map_inner_unit hu
  have hmeas_ip : Measurable (fun a : E => ⟪a, u⟫_ℝ) :=
    (continuous_id.inner continuous_const).measurable
  -- Integrability of `|⟪a, u⟫|` under `stdGaussian E`
  have habs_int : Integrable (fun a : E => |⟪a, u⟫_ℝ|) (stdGaussian E) := by
    have h1 : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
      ((memLp_id_gaussianReal (1 : ℝ≥0)).integrable le_rfl).norm
    have h2 : Integrable (fun z : ℝ => |z|) ((stdGaussian E).map (fun a : E => ⟪a, u⟫_ℝ)) := by
      rwa [hmap]
    exact (integrable_map_measure (g := fun z : ℝ => |z|)
      h2.aestronglyMeasurable hmeas_ip.aemeasurable).mp h2
  -- Define the four integrands
  let fC : E → ℝ := fun a => if a ∈ C then |⟪a, u⟫_ℝ| else 0
  let indC : E → ℝ := fun a => if a ∈ C then 1 else 0
  let indB : E → ℝ := fun a => if |⟪a, u⟫_ℝ| ≤ t then 1 else 0
  let fB : E → ℝ := fun a => if |⟪a, u⟫_ℝ| ≤ t then |⟪a, u⟫_ℝ| else 0
  have hB_meas : MeasurableSet {a : E | |⟪a, u⟫_ℝ| ≤ t} :=
    measurableSet_le (continuous_abs.measurable.comp hmeas_ip) measurable_const
  have hfC_int : Integrable fC (stdGaussian E) := by
    refine habs_int.mono' (Measurable.ite hC (continuous_abs.measurable.comp hmeas_ip) measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    dsimp [fC]; split_ifs <;> simp [abs_nonneg]
  have hfB_int : Integrable fB (stdGaussian E) := by
    refine habs_int.mono' (Measurable.ite hB_meas (continuous_abs.measurable.comp hmeas_ip) measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    dsimp [fB]; split_ifs <;> simp [abs_nonneg]
  have hindC_int : Integrable indC (stdGaussian E) := by
    refine (integrable_const (1 : ℝ)).mono' (Measurable.ite hC measurable_const measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    dsimp [indC]; split_ifs <;> norm_num
  have hindB_int : Integrable indB (stdGaussian E) := by
    refine (integrable_const (1 : ℝ)).mono' (Measurable.ite hB_meas measurable_const measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    dsimp [indB]; split_ifs <;> norm_num
  -- Pointwise bathtub inequality: `fB a + t * indC a - t * indB a ≤ fC a`
  have hpt : ∀ a : E, fB a + t * indC a - t * indB a ≤ fC a := by
    intro a
    have h0 : 0 ≤ indC a := by dsimp [indC]; split_ifs <;> norm_num
    have h1 : indC a ≤ 1 := by dsimp [indC]; split_ifs <;> norm_num
    have hbt := lemma33_bathtub_pointwise (indC a) h0 h1 ⟪a, u⟫_ℝ t
    have hmulC : indC a * |⟪a, u⟫_ℝ| = fC a := by dsimp [indC, fC]; split_ifs <;> ring
    have hmulB : indB a * |⟪a, u⟫_ℝ| = fB a := by dsimp [indB, fB]; split_ifs <;> ring
    have hbt' : 0 ≤ (indC a - indB a) * (|⟪a, u⟫_ℝ| - t) := hbt
    nlinarith
  have hint_mono :
      (∫ a : E, fB a ∂(stdGaussian E)) + t * (∫ a : E, indC a ∂(stdGaussian E)) -
        t * (∫ a : E, indB a ∂(stdGaussian E)) ≤
      ∫ a : E, fC a ∂(stdGaussian E) := by
    have h1_int : Integrable (fun a : E => t * indC a) (stdGaussian E) := hindC_int.const_mul t
    have h2_int : Integrable (fun a : E => t * indB a) (stdGaussian E) := hindB_int.const_mul t
    have hsum_int : Integrable (fun a : E => fB a + t * indC a) (stdGaussian E) := hfB_int.add h1_int
    have hdiff_int : Integrable (fun a : E => fB a + t * indC a - t * indB a) (stdGaussian E) :=
      hsum_int.sub h2_int
    have hstep := integral_mono hdiff_int hfC_int hpt
    rw [integral_sub hsum_int h2_int, integral_add hfB_int h1_int,
        integral_const_mul, integral_const_mul] at hstep
    exact hstep
  -- Step 1: `p ≤ ∫ indC`
  have hindC_ge : p ≤ ∫ a : E, indC a ∂(stdGaussian E) := by
    have heq : ∫ a : E, indC a ∂(stdGaussian E) = (stdGaussian E).real C := by
      have h1 : indC = C.indicator (fun _ => (1 : ℝ)) := by
        ext a; simp [indC, Set.indicator]
      rw [h1, integral_indicator_const (1 : ℝ) hC, smul_eq_mul, mul_one]
    rw [heq, Measure.real]
    have hne : stdGaussian E C ≠ ⊤ := measure_ne_top _ _
    have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hne).mpr hCp
    rwa [ENNReal.toReal_ofReal hp0] at this
  -- Step 2: `∫ indB ≤ p`
  have hindB_le : ∫ a : E, indB a ∂(stdGaussian E) ≤ p := by
    have hpull : ∫ a : E, indB a ∂(stdGaussian E) =
        ∫ z : ℝ, (if |z| ≤ t then (1 : ℝ) else 0) ∂(gaussianReal 0 1) := by
      rw [← hmap]
      have hmeas_g : Measurable (fun z : ℝ => if |z| ≤ t then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
          measurable_const measurable_const
      exact (integral_map (φ := fun a : E => ⟪a, u⟫_ℝ)
        (f := fun z : ℝ => if |z| ≤ t then (1 : ℝ) else 0)
        hmeas_ip.aemeasurable hmeas_g.aestronglyMeasurable).symm
    rw [hpull, integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    simp_rw [smul_eq_mul, gaussianPDFReal_std]
    have hrew : (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
        (if |x| ≤ t then (1 : ℝ) else 0)) =
        (Set.Icc (-t) t).indicator (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2)) := by
      ext x; simp only [Set.indicator, Set.mem_Icc, abs_le]; split_ifs <;> ring
    rw [hrew, integral_indicator measurableSet_Icc, integral_const_mul]
    have hle1 : ∫ x in Set.Icc (-t) t, Real.exp (-x ^ 2 / 2) ≤ ∫ x in Set.Icc (-t) t, (1 : ℝ) := by
      refine setIntegral_mono_on ?_ (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top.ne))
        measurableSet_Icc (fun x _ => ?_)
      · exact (Continuous.continuousOn (by fun_prop)).integrableOn_Icc
      · exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have hone : ∫ x in Set.Icc (-t) t, (1 : ℝ) = 2 * t := by
      rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by linarith)]; ring
    have hmul := mul_le_mul_of_nonneg_left (hle1.trans_eq hone)
      (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi)))
    refine hmul.trans_eq ?_
    dsimp [t]
    rw [Real.sqrt_div (le_of_lt Real.pi_pos), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hspi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hs2, hspi]; rw [hsq2]
  -- Step 3: Exact formula `∫ fB = √(2/π) * (1 - exp(-π p^2 / 4))`
  have hfB_eq : ∫ a : E, fB a ∂(stdGaussian E) =
      Real.sqrt (2 / Real.pi) * (1 - Real.exp (-Real.pi * p ^ 2 / 4)) := by
    have hpull : ∫ a : E, fB a ∂(stdGaussian E) =
        ∫ z : ℝ, (if |z| ≤ t then |z| else 0) ∂(gaussianReal 0 1) := by
      rw [← hmap]
      have hmeas_g : Measurable (fun z : ℝ => if |z| ≤ t then |z| else 0) :=
        Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const)
          continuous_abs.measurable measurable_const
      exact (integral_map (φ := fun a : E => ⟪a, u⟫_ℝ)
        (f := fun z : ℝ => if |z| ≤ t then |z| else 0)
        hmeas_ip.aemeasurable hmeas_g.aestronglyMeasurable).symm
    rw [hpull, integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    simp_rw [smul_eq_mul, gaussianPDFReal_std]
    have hrew : (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) *
        (if |x| ≤ t then |x| else 0)) =
        (Set.Icc (-t) t).indicator (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * |x|)) := by
      ext x; simp only [Set.indicator, Set.mem_Icc, abs_le]; split_ifs <;> ring
    rw [hrew, integral_indicator measurableSet_Icc, integral_const_mul,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : -t ≤ t)]
    have hcont_g : Continuous (fun x : ℝ => Real.exp (-x ^ 2 / 2) * |x|) := by fun_prop
    have hsplit : ∫ x in (-t)..t, Real.exp (-x ^ 2 / 2) * |x| =
        (∫ x in (-t)..(0 : ℝ), Real.exp (-x ^ 2 / 2) * |x|) +
        (∫ x in (0 : ℝ)..t, Real.exp (-x ^ 2 / 2) * |x|) :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont_g.intervalIntegrable (-t) 0) (hcont_g.intervalIntegrable 0 t)).symm
    have hpos_int : ∫ x in (0 : ℝ)..t, Real.exp (-x ^ 2 / 2) * |x| = 1 - Real.exp (-t ^ 2 / 2) := by
      have hcongr : ∫ x in (0 : ℝ)..t, Real.exp (-x ^ 2 / 2) * |x| =
          ∫ x in (0 : ℝ)..t, Real.exp (-x ^ 2 / 2) * x := by
        refine intervalIntegral.integral_congr (fun x hx => ?_)
        rw [Set.uIcc_of_le ht0] at hx
        rw [abs_of_nonneg hx.1]
      rw [hcongr]
      have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) t,
          HasDerivAt (fun z : ℝ => -Real.exp (-z ^ 2 / 2)) (Real.exp (-x ^ 2 / 2) * x) x := by
        intro x _
        have h1 : HasDerivAt (fun z : ℝ => -z ^ 2 / 2) (-x) x := by
          convert ((hasDerivAt_pow 2 x).neg.div_const (2 : ℝ)) using 1; ring
        convert (h1.exp).fun_neg using 1; ring
      have hint : IntervalIntegrable (fun x : ℝ => Real.exp (-x ^ 2 / 2) * x) volume 0 t :=
        (show Continuous (fun x : ℝ => Real.exp (-x ^ 2 / 2) * x) by fun_prop).intervalIntegrable 0 t
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      simp; ring
    have hneg_int : ∫ x in (-t)..(0 : ℝ), Real.exp (-x ^ 2 / 2) * |x| = 1 - Real.exp (-t ^ 2 / 2) := by
      have hcongr : ∫ x in (-t)..(0 : ℝ), Real.exp (-x ^ 2 / 2) * |x| =
          ∫ x in (-t)..(0 : ℝ), -(Real.exp (-x ^ 2 / 2) * x) := by
        refine intervalIntegral.integral_congr (fun x hx => ?_)
        rw [Set.uIcc_of_le (by linarith : -t ≤ 0)] at hx
        rw [abs_of_nonpos hx.2]; ring
      rw [hcongr]
      have hderiv : ∀ x ∈ Set.uIcc (-t) (0 : ℝ),
          HasDerivAt (fun z : ℝ => Real.exp (-z ^ 2 / 2)) (-(Real.exp (-x ^ 2 / 2) * x)) x := by
        intro x _
        have h1 : HasDerivAt (fun z : ℝ => -z ^ 2 / 2) (-x) x := by
          convert ((hasDerivAt_pow 2 x).neg.div_const (2 : ℝ)) using 1; ring
        convert h1.exp using 1; ring
      have hint : IntervalIntegrable (fun x : ℝ => -(Real.exp (-x ^ 2 / 2) * x)) volume (-t) 0 :=
        (show Continuous (fun x : ℝ => -(Real.exp (-x ^ 2 / 2) * x)) by fun_prop).intervalIntegrable (-t) 0
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      simp
    rw [hsplit, hneg_int, hpos_int]
    have ht_sq : -t ^ 2 / 2 = -Real.pi * p ^ 2 / 4 := by
      dsimp [t]
      rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi / 2)]; ring
    rw [ht_sq]
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs2 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    have hspi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
    have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hs2, hspi]; rw [hsq2]; ring
  -- Combine Steps 1–3 with `lemma33_analytic_lower_bound`!
  have hterm_nonneg : 0 ≤ t * (∫ a : E, indC a ∂(stdGaussian E)) - t * (∫ a : E, indB a ∂(stdGaussian E)) := by
    have : ∫ a : E, indB a ∂(stdGaussian E) ≤ ∫ a : E, indC a ∂(stdGaussian E) := le_trans hindB_le hindC_ge
    nlinarith
  have h1 : Real.sqrt (2 / Real.pi) * (1 - Real.exp (-Real.pi * p ^ 2 / 4)) ≤
      ∫ a : E, fC a ∂(stdGaussian E) := by
    rw [← hfB_eq]; linarith
  exact le_trans (lemma33_analytic_lower_bound hp0 hp1) h1

/-- **Theorem 4 (Bridged Directly From Geometric Cone Probabilities `π_min > 0`)**:
Eliminates BOTH `hαmin` and `h_cone_pop` by bridging directly from the geometric active-cone
probability assumption `∀ j, ENNReal.ofReal π_min ≤ stdGaussian E (activeCone β_star j)` via
`lemma33_gaussian_bathtub` (`α_min := (√(2π) / 6) * π_min^2`). -/
theorem theorem4_from_pi_min [Nontrivial E]
    {m r : ℕ} (hm : 0 < m) (hr : 2 ≤ r)
    (β_star : Fin r → E)
    (s : Fin m → ℝ) (hs_pm : ∀ i : Fin m, s i = 1 ∨ s i = -1)
    {Δ_min α π_min δ_fail : ℝ}
    (hΔmin : 0 < Δ_min)
    (h_sep : ∀ j k : Fin r, j ≠ k → Δ_min ≤ ‖β_star j - β_star k‖)
    (hα0 : 0 ≤ α) (hα1 : α < 1 / 2)
    (h_frac : (1 / (m : ℝ)) * ∑ i : Fin m, s i = 1 - 2 * α)
    (hπ0 : 0 < π_min) (hπ1 : π_min ≤ 1)
    (h_cone_prob : ∀ j : Fin r, ENNReal.ofReal π_min ≤ stdGaussian E (activeCone β_star j))
    (hδ0 : 0 < δ_fail) (hδ1 : δ_fail < 1)
    (hm_op_d : 16 * (Module.finrank ℝ E : ℝ) ≤ (m : ℝ))
    (hm_op_log : (32 / 9 : ℝ) * Real.log (3 / δ_fail) ≤ (m : ℝ))
    (hm_cone : (64 / ((1 - 2 * α) * ((Real.sqrt (2 * Real.pi) / 6) * π_min ^ 2)) ^ 2) *
      ((Module.finrank ℝ E : ℝ) * Real.log (1 + 16 / ((1 - 2 * α) * ((Real.sqrt (2 * Real.pi) / 6) * π_min ^ 2))) +
        Real.log (3 * (r : ℝ) / δ_fail)) ≤ (m : ℝ))
    (hm_flip : (22 / (3 * (((1 - 2 * α) * ((Real.sqrt (2 * Real.pi) / 6) * π_min ^ 2)) / (26 * ((r : ℝ) - 1))))) *
      ((Module.finrank ℝ E : ℝ) * Real.log (9 / (((1 - 2 * α) * ((Real.sqrt (2 * Real.pi) / 6) * π_min ^ 2)) / (26 * ((r : ℝ) - 1)))) +
        Real.log (3 * ((r : ℝ) ^ 2 / 2) / δ_fail)) ≤ (m : ℝ)) :
    let hr_pos : 0 < r := by omega
    let α_min := (Real.sqrt (2 * Real.pi) / 6) * π_min ^ 2
    let γ := (1 - 2 * α) * α_min
    let η := γ / (26 * ((r : ℝ) - 1))
    let ρ := (η / Real.sqrt 2) * Δ_min
    1 - ENNReal.ofReal δ_fail ≤ iidStdGaussian E m {a : Fin m → E |
      ∀ (ξ : Fin m → ℝ), (∀ i : Fin m, s i = 1 → ξ i = 0) →
        let y := fun i => maxLinearPred hr_pos (a i) β_star + ξ i
        (∀ Δ : Fin r → E, frobNorm Δ ≤ ρ →
          (γ / 4) * frobNorm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
            l1EmpiricalLoss hr_pos a y β_star ∧
          (γ / 4) * blockL1L2Norm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
            l1EmpiricalLoss hr_pos a y β_star) ∧
        (∀ β β' : Fin r → E,
          |l1EmpiricalLoss hr_pos a y β - l1EmpiricalLoss hr_pos a y β'| ≤
            2 * frobNorm (fun j => β j - β' j)) ∧
        ((∀ i : Fin m, ξ i = 0) →
          ∀ β z : Fin r → E,
            frobNorm (fun j => β j - β_star j) ≤ ρ / 2 →
            l1EmpiricalLoss hr_pos a y z = 0 →
            frobNorm (fun j => β j - β_star j) ≤ frobNorm (fun j => β j - z j))} := by
  have hαmin : 0 < (Real.sqrt (2 * Real.pi) / 6) * π_min ^ 2 := by positivity
  have h_cone_pop : ∀ (j : Fin r) (u : E), ‖u‖ = 1 →
      (Real.sqrt (2 * Real.pi) / 6) * π_min ^ 2 ≤ popConeNorm β_star j u := fun j u hu =>
    lemma33_gaussian_bathtub (measurableSet_activeCone β_star j) (le_of_lt hπ0) hπ1 (h_cone_prob j) hu
  exact theorem4_unconditional_probabilistic hm hr β_star s hs_pm hΔmin h_sep hα0 hα1 h_frac
    hαmin h_cone_pop hδ0 hδ1 hm_op_d hm_op_log hm_cone hm_flip

/-! ### Phase III–IV Unconditional Axiom Audits (Stages 1–5 + Lemma 3.3 + `π_min` Bridge + Prop. 4.1') -/
#print axioms iidStdGaussian_ae_active
#print axioms exists_sphere_eps_net
#print axioms prob_operator_norm_event
#print axioms lemma41_gaussian_mgf
#print axioms lemma41_empirical_tails
#print axioms prob_cone_net_event
#print axioms proposition41_prime_breakdown_necessity
#print axioms lemma43_gaussian_moments
#print axioms lemma43_gaussian_bernstein_mgf
#print axioms lemma43_pointwise_flip_tail
#print axioms prob_flip_net_event
#print axioms theorem4_unconditional_probabilistic
#print axioms lemma33_gaussian_bathtub
#print axioms theorem4_from_pi_min

end Research107
