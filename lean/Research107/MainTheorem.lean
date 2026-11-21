import Research107.Deterministic
import Research107.Population
import Research107.Concentration

open scoped BigOperators InnerProductSpace

namespace Research107

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Main Assembled Theorem (Conditional Deterministic Package for Theorem 4)**:
Combines the Stage A deterministic core (`theorem4_deterministic_core`),
Stage C net-to-sphere discretization (`lemma42_net_to_sphere`, `lemma43_net_to_sphere`),
exact budget verification (`theorem4_budget_check`), global Lipschitz bound (`theorem4_part2_global_lipschitz`),
and noiseless half-radius distance identity (`theorem4_part3_half_radius_distance`).

Every single remaining probabilistic assumption (operator norm event, net-point concentration of `T_j`,
and net-point Bernstein concentration of `φ_η`) is stated as an **explicit named hypothesis** below —
with zero `sorry`, zero `admit`, and zero custom `axiom`. -/
theorem main_theorem4_assembled
    {m r : ℕ} (hm : 0 < m) (hr : 2 ≤ r)
    (a : Fin m → E) (β_star : Fin r → E)
    (s : Fin m → ℝ) (ξ : Fin m → ℝ)
    (γ Δ_min : ℝ)
    (hγ : 0 < γ) (hΔmin : 0 < Δ_min)
    (h_sep : ∀ j k : Fin r, j ≠ k → Δ_min ≤ ‖β_star j - β_star k‖)
    (h_signs : ∀ i : Fin m, (s i = 1 ∧ ξ i = 0) ∨ s i = -1)
    (h_active : ∀ i : Fin m, ∃ j₀ : Fin r, a i ∈ activeCone β_star j₀)
    -- Probabilistic Event 0: Gaussian matrix operator norm `‖A‖_op ≤ 2√m`
    (h_event_op : ∀ w : E, ∑ i : Fin m, ⟪a i, w⟫_ℝ ^ 2 ≤ 4 * (m : ℝ) * ‖w‖ ^ 2)
    -- Probabilistic Event 1: `(γ/8)`-net concentration of signed cone norms `T_j(u₀) ≥ 3γ/4`
    (h_event_cone_net : ∀ (j : Fin r) (u : E), ‖u‖ = 1 →
      ∃ u₀ : E, ‖u - u₀‖ ≤ γ / 8 ∧ 3 * γ / 4 ≤ signedConeNorm a s β_star j u₀)
    -- Probabilistic Event 2: `(η/4)`-net Bernstein concentration of `φ_η`
    (h_event_flip_net : ∀ (j k : Fin r), j < k → ∀ (u : E), ‖u‖ = 1 →
      let η := γ / (26 * ((r : ℝ) - 1))
      ∃ u₀ : E, ‖u - u₀‖ ≤ η / 4 ∧
        (1 / (m : ℝ)) * ∑ i : Fin m,
          phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u₀⟫_ℝ ≤
        (4 * Real.sqrt (2 * Real.pi) / 3 + 2) * η) :
    let hr_pos : 0 < r := by omega
    let y := fun i => maxLinearPred hr_pos (a i) β_star + ξ i
    let η := γ / (26 * ((r : ℝ) - 1))
    let ρ := (η / Real.sqrt 2) * Δ_min
    -- (1) Uniform macroscopic sharp growth on `B(β*, ρ)` (both Frobenius and stronger block `ℓ_{1,2}` norms)
    (∀ Δ : Fin r → E, frobNorm Δ ≤ ρ →
      (γ / 4) * frobNorm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
        l1EmpiricalLoss hr_pos a y β_star ∧
      (γ / 4) * blockL1L2Norm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
        l1EmpiricalLoss hr_pos a y β_star) ∧
    -- (2) Global 2-Lipschitz continuity in Frobenius norm
    (∀ β β' : Fin r → E,
      |l1EmpiricalLoss hr_pos a y β - l1EmpiricalLoss hr_pos a y β'| ≤
        2 * frobNorm (fun j => β j - β' j)) ∧
    -- (3) In the noiseless case (`ξ ≡ 0`), half-radius distance identity for every global minimizer `z`
    ((∀ i : Fin m, ξ i = 0) →
      ∀ β z : Fin r → E,
        frobNorm (fun j => β j - β_star j) ≤ ρ / 2 →
        l1EmpiricalLoss hr_pos a y z = 0 →
        frobNorm (fun j => β j - β_star j) ≤ frobNorm (fun j => β j - z j)) := by
  intro hr_pos y η ρ
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hη : 0 < η := div_pos hγ (by positivity)
  have hρ : 0 < ρ := mul_pos (div_pos hη (Real.sqrt_pos.mpr (by norm_num))) hΔmin
  have hs_abs : ∀ i : Fin m, |s i| ≤ 1 := by
    intro i
    rcases h_signs i with ⟨h1, _⟩ | hm1
    · rw [h1]; norm_num
    · rw [hm1]; norm_num
  have h_cone : ∀ (j : Fin r) (u : E), ‖u‖ = 1 → γ / 2 ≤ signedConeNorm a s β_star j u := by
    intro j u hu
    rcases h_event_cone_net j u hu with ⟨u₀, hdist, hval⟩
    exact lemma42_net_to_sphere hm a s β_star j hs_abs h_event_op hdist hval
  have h_flip : ∀ (j k : Fin r), j < k → ∀ (u : E), ‖u‖ = 1 →
      (1 / (m : ℝ)) * ∑ i : Fin m,
        phiEta η ⟪a i, (‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k)⟫_ℝ ⟪a i, u⟫_ℝ ≤
      (635 / 100 : ℝ) * η := by
    intro j k hjk u hu
    rcases h_event_flip_net j k hjk u hu with ⟨u₀, hdist, hval⟩
    exact lemma43_net_to_sphere hm a ((‖β_star j - β_star k‖⁻¹) • (β_star j - β_star k))
      u u₀ hη h_event_op hdist hval
  have h_budget : (635 / 100 : ℝ) * η * ((r : ℝ) - 1) ≤ γ / 4 :=
    theorem4_budget_check hr (le_of_lt hγ)
  have h_part1 : ∀ Δ : Fin r → E, frobNorm Δ ≤ ρ →
      (γ / 4) * frobNorm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
        l1EmpiricalLoss hr_pos a y β_star ∧
      (γ / 4) * blockL1L2Norm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) -
        l1EmpiricalLoss hr_pos a y β_star := fun Δ hΔ =>
    theorem4_deterministic_core hm hr_pos a β_star Δ s ξ γ η Δ_min (635 / 100)
      (le_of_lt hγ) hη hΔmin h_sep h_signs h_active h_cone h_flip h_budget hΔ
  refine ⟨h_part1, ?_, ?_⟩
  · -- Part 2: Global 2-Lipschitz bound
    intro β β'
    have h_op2 : ∀ u : E, ∑ i : Fin m, ⟪a i, u⟫_ℝ ^ 2 ≤ ((2 : ℝ) ^ 2 * (m : ℝ)) * ‖u‖ ^ 2 := by
      intro u
      have := h_event_op u
      nlinarith
    exact theorem4_part2_global_lipschitz hm hr_pos a y 2 (by norm_num) h_op2 β β'
  · -- Part 3: Noiseless half-radius distance identity
    intro hξ β z hβ hz
    have hf0 : l1EmpiricalLoss hr_pos a y β_star = 0 := by
      unfold l1EmpiricalLoss
      have : ∀ i : Fin m, |y i - maxLinearPred hr_pos (a i) β_star| = 0 := by
        intro i; dsimp [y]; rw [hξ i, add_zero, sub_self, abs_zero]
      simp [this]
    have h_sh : ∀ Δ : Fin r → E, frobNorm Δ ≤ ρ →
        (γ / 4) * frobNorm Δ ≤ l1EmpiricalLoss hr_pos a y (fun j => β_star j + Δ j) := by
      intro Δ hΔ
      have h1 := (h_part1 Δ hΔ).1
      linarith
    exact theorem4_part3_half_radius_distance (l1EmpiricalLoss hr_pos a y) β_star
      (by linarith : 0 < γ / 4) hρ h_sh hβ hz

/-! ### Axiom Audit Checks (Verified Clean: Only Standard Lean Axioms) -/
#print axioms lemma31_pointwise_flip_decomp
#print axioms lemma43_part1_scale_free_domination
#print axioms theorem4_deterministic_core
#print axioms theorem4_part2_global_lipschitz
#print axioms theorem4_part3_half_radius_distance
#print axioms theorem1b_counterexample_constant
#print axioms theorem1b_class_not_weakly_convex
#print axioms theorem2_antipodal_pairing
#print axioms theorem2_voronoi_iff
#print axioms theorem2_global_quadratic_norm_bound
#print axioms theorem2_voronoi_parallelogram_bound
#print axioms theorem2_global_sharpness_from_remainder
#print axioms theorem2_wedge_trig_integral
#print axioms lemma33_analytic_lower_bound
#print axioms lemma41_cosh_domination
#print axioms lemma43_arcsin_bound
#print axioms lemma43_moment_induction
#print axioms lemma43_bernstein_mgf_step
#print axioms corollary41_exact_identities
#print axioms theorem4_tail_algebra
#print axioms main_theorem4_assembled

end Research107
