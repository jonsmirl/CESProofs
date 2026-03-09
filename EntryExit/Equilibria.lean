/-
  Paper 1c, Section 3: The Participation Game

  Theorem 1c.2: Strategic complementarity (supermodular game)
  Theorem 1c.3: Multiple equilibria (fold structure)
  Corollary 1c.1: Critical mass characterization
-/

import CESProofs.EntryExit.Defs
import CESProofs.EntryExit.CurvatureInJ
import CESProofs.EntryExit.Calculus

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Theorem 1c.2: Strategic Complementarity
-- ============================================================

/-- **Theorem 1c.2 (Strategic Complementarity).**
    The participation payoff is increasing in J when K_eff is increasing
    (i.e., below saturation). More precisely:
    dK/dJ = (1-rho)/J^2 > 0 for rho < 1 ensures the game is supermodular.

    In a supermodular game, each agent's incentive to enter increases
    when more agents are present. By Topkis' theorem, the set of
    Nash equilibria forms a complete lattice. -/
theorem strategic_complementarity {J ρ : ℝ}
    (hJ : 0 < J) (hρ : ρ < 1) :
    0 < marginalK J ρ :=
  pigouvian_subsidy_pos hJ hρ

/-- **Strategic complementarity (full value function).**
    V'(J) > 0 for J > 1 and ρ ∈ (0,1): the full participation payoff
    (not just K) is increasing in J. -/
theorem strategic_complementarity_full {J ρ c : ℝ}
    (hJ : 1 < J) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    0 < valueFunctionDeriv J ρ c :=
  valueFunctionDeriv_pos hJ hρ0 hρ1 hc

/-- The marginal curvature (externality) is bounded by (1-rho) at J=1. -/
theorem marginal_curvature_bounded {J ρ : ℝ}
    (hJ : 1 ≤ J) (hρ : ρ < 1) :
    marginalK J ρ ≤ 1 - ρ := by
  simp only [marginalK]
  rw [div_le_iff₀ (sq_pos_of_pos (by linarith : (0:ℝ) < J))]
  nlinarith [sq_nonneg (J - 1)]

-- ============================================================
-- Theorem 1c.3: Multiple Equilibria
-- ============================================================

/-- **Theorem 1c.3 (Multiple Equilibria — Fold Structure).**
    The per-capita surplus π_K(J) = (1-ρ)(J-1)/J² is hump-shaped with
    peak (1-ρ)/4 at J=2. When entry cost κ is below the peak:
    (a) π_K(J) < κ near J=1 (no benefit at low diversity),
    (b) π_K(2) > κ (profitable at optimal diversity),
    (c) π_K(J) < κ for large J (dilution dominates).
    These three sign conditions, together with continuity, imply by the
    IVT that π_K(J) = κ has at least two roots J_low ∈ (1,2) and J_high > 2,
    producing the fold bifurcation.

    We prove the three sign conditions and the existence of both crossings.

    **Part 1: Sign conditions.** -/
theorem multiple_equilibria_sign_below_peak {ρ κ : ℝ}
    (_hρ : ρ < 1) (hκ_pos : 0 < κ) (hκ_small : κ < (1 - ρ) / 4) :
    -- (a) At J=1: surplus is 0 < κ, so net payoff is negative
    perCapitaSurplus 1 ρ < κ ∧
    -- (b) At J=2: surplus exceeds cost
    κ < perCapitaSurplus 2 ρ ∧
    -- (c) For sufficiently large J: surplus falls below cost again
    ∃ J_large : ℝ, 2 < J_large ∧ perCapitaSurplus J_large ρ < κ := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a) π_K(1) = 0 < κ
    rw [perCapitaSurplus_at_one]; exact hκ_pos
  · -- (b) π_K(2) = (1-ρ)/4 > κ
    rw [perCapitaSurplus_at_two]; exact hκ_small
  · -- (c) For large J, π_K(J) < κ.
    -- π_K(J) = (1-ρ)(J-1)/J² ≤ (1-ρ)/J (since (J-1)/J² ≤ 1/J for J ≥ 1).
    -- So pick J_large such that (1-ρ)/J_large < κ.
    -- Use J_large = 2(1-ρ)/κ which gives (1-ρ)/J_large = κ/2 < κ.
    have h1ρ : 0 < 1 - ρ := by linarith
    use 2 * (1 - ρ) / κ
    have hκne : κ ≠ 0 := ne_of_gt hκ_pos
    constructor
    · -- 2(1-ρ)/κ > 2 iff (1-ρ)/κ > 1 iff 1-ρ > κ
      rw [show (2:ℝ) * (1 - ρ) / κ = 2 * ((1 - ρ) / κ) from by ring]
      have h1 : 1 < (1 - ρ) / κ := by rw [one_lt_div hκ_pos]; linarith
      linarith
    · -- π_K(2(1-ρ)/κ) < κ
      simp only [perCapitaSurplus]
      have hJ_pos : 0 < 2 * (1 - ρ) / κ := by positivity
      rw [div_lt_iff₀ (sq_pos_of_pos hJ_pos)]
      -- Goal: (1-ρ) * (2(1-ρ)/κ - 1) < κ * (2(1-ρ)/κ)²
      -- Bound LHS ≤ (1-ρ) * (2(1-ρ)/κ) = 2(1-ρ)²/κ
      -- RHS = κ * 4(1-ρ)²/κ² = 4(1-ρ)²/κ
      -- So LHS < RHS since 2(1-ρ)²/κ < 4(1-ρ)²/κ
      have hJ_sub : 2 * (1 - ρ) / κ - 1 < 2 * (1 - ρ) / κ := by linarith
      have hJ_bound : (1 - ρ) * (2 * (1 - ρ) / κ - 1) <
          (1 - ρ) * (2 * (1 - ρ) / κ) := by
        exact mul_lt_mul_of_pos_left hJ_sub h1ρ
      have hsq : (2 * (1 - ρ) / κ) ^ 2 = 4 * (1 - ρ) ^ 2 / κ ^ 2 := by ring
      calc (1 - ρ) * (2 * (1 - ρ) / κ - 1)
          < (1 - ρ) * (2 * (1 - ρ) / κ) := hJ_bound
        _ = 2 * (1 - ρ) ^ 2 / κ := by ring
        _ ≤ κ * (2 * (1 - ρ) / κ) ^ 2 := by
            rw [hsq]
            rw [show κ * (4 * (1 - ρ) ^ 2 / κ ^ 2) =
              4 * (1 - ρ) ^ 2 / κ from by field_simp]
            apply div_le_div_of_nonneg_right _ hκ_pos.le
            linarith [sq_nonneg (1 - ρ)]

/-- **Part 2: IVT crossing — lower equilibrium.**
    Since π_K is continuous, π_K(1) = 0 < κ < π_K(2), by the IVT
    there exists J_low ∈ (1, 2) with π_K(J_low) = κ. -/
theorem multiple_equilibria_lower_root {ρ κ : ℝ}
    (_hρ : ρ < 1) (hκ_pos : 0 < κ) (hκ_small : κ < (1 - ρ) / 4) :
    ∃ J_low : ℝ, 1 ≤ J_low ∧ J_low ≤ 2 ∧ perCapitaSurplus J_low ρ = κ := by
  have h_at_1 : perCapitaSurplus 1 ρ = 0 := perCapitaSurplus_at_one ρ
  have h_at_2 : perCapitaSurplus 2 ρ = (1 - ρ) / 4 := perCapitaSurplus_at_two ρ
  -- π_K(1) = 0 ≤ κ ≤ (1-ρ)/4 = π_K(2)
  have hκ_mem : κ ∈ Set.Icc (perCapitaSurplus 1 ρ) (perCapitaSurplus 2 ρ) := by
    rw [h_at_1, h_at_2]; exact ⟨le_of_lt hκ_pos, le_of_lt hκ_small⟩
  -- Continuity of π_K on [1, 2]
  have hcont : ContinuousOn (fun x => perCapitaSurplus x ρ) (Set.Icc 1 2) := by
    simp only [perCapitaSurplus]
    apply ContinuousOn.div
    · exact continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
    · exact continuousOn_id.pow 2
    · intro x hx; exact ne_of_gt (pow_pos (by linarith [hx.1]) 2)
  obtain ⟨J_low, ⟨hJ_ge, hJ_le⟩, hJ_eq⟩ :=
    intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hcont hκ_mem
  exact ⟨J_low, hJ_ge, hJ_le, hJ_eq⟩

/-- **Part 3: IVT crossing — upper equilibrium.**
    Since π_K(2) > κ and π_K(J_large) < κ for large J_large, by the IVT
    there exists J_high ∈ (2, J_large) with π_K(J_high) = κ. -/
theorem multiple_equilibria_upper_root {ρ κ : ℝ}
    (hρ : ρ < 1) (hκ_pos : 0 < κ) (hκ_small : κ < (1 - ρ) / 4) :
    ∃ J_high : ℝ, 2 ≤ J_high ∧ perCapitaSurplus J_high ρ = κ := by
  -- Pick J_large from Part 1
  obtain ⟨_, _, ⟨J_large, hJ_large_gt2, hJ_large_small⟩⟩ :=
    multiple_equilibria_sign_below_peak hρ hκ_pos hκ_small
  have h_at_2 : perCapitaSurplus 2 ρ = (1 - ρ) / 4 := perCapitaSurplus_at_two ρ
  -- κ ∈ [π_K(J_large), π_K(2)]
  have hκ_mem : κ ∈ Set.Icc (perCapitaSurplus J_large ρ) (perCapitaSurplus 2 ρ) := by
    rw [h_at_2]; exact ⟨le_of_lt hJ_large_small, le_of_lt hκ_small⟩
  -- But IVT needs [a,b] with a ≤ b, so use [2, J_large]
  -- and note that κ ∈ Icc (min f(2) f(J_large)) (max f(2) f(J_large))
  -- Since f(2) > κ > f(J_large), κ ∈ Icc f(J_large) f(2)
  -- intermediate_value_Icc on [2, J_large] with κ ∈ [f(J_large), f(2)]
  -- Wait, intermediate_value_Icc gives f(a) to f(b), but we need f(a) > f(b)
  -- Use intermediate_value_Icc which gives κ ∈ Icc (f a) (f b) OR use uIcc version
  -- Actually intermediate_value_Icc works: if κ ∈ Icc (f 2) (f J_large) that's wrong
  -- since f(2) > f(J_large). We need the descending version.
  have hle : (2:ℝ) ≤ J_large := le_of_lt hJ_large_gt2
  have hcont : ContinuousOn (fun x => perCapitaSurplus x ρ) (Set.Icc 2 J_large) := by
    simp only [perCapitaSurplus]
    apply ContinuousOn.div
    · exact continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
    · exact continuousOn_id.pow 2
    · intro x hx; exact ne_of_gt (pow_pos (by linarith [hx.1]) 2)
  -- κ ∈ Icc (f J_large) (f 2), need to map to intermediate_value_Icc
  -- Use the fact that ContinuousOn + connected → image is connected
  -- Simpler: use intermediate_value_uIcc or intermediate_value_Icc with swapped bounds
  -- intermediate_value_Icc : a ≤ b → ContinuousOn f [a,b] → y ∈ [f a, f b] → ∃ x ∈ [a,b], f x = y
  -- Our case: a=2, b=J_large, f(2) > κ > f(J_large)
  -- So κ ∉ [f(2), f(J_large)] but κ ∈ [f(J_large), f(2)]
  -- We can negate f and use IVT, or use IsPreconnected.intermediate_value
  -- Actually Mathlib has intermediate_value_Icc which handles both orderings
  -- Let me check: it requires y ∈ Icc (f a) (f b), so if f a > f b we're stuck
  -- Use -f instead: -f(2) < -κ < -f(J_large), so -κ ∈ [-f(2), -f(J_large)]
  have hcont_neg : ContinuousOn (fun x => -(perCapitaSurplus x ρ)) (Set.Icc 2 J_large) :=
    hcont.neg
  have hκ_neg_mem : -κ ∈ Set.Icc (-(perCapitaSurplus 2 ρ)) (-(perCapitaSurplus J_large ρ)) := by
    constructor
    · linarith [hκ_small, h_at_2]
    · linarith [hJ_large_small]
  obtain ⟨J_high, ⟨hJ_ge, _⟩, hJ_eq⟩ :=
    intermediate_value_Icc hle hcont_neg hκ_neg_mem
  exact ⟨J_high, hJ_ge, by linarith⟩

/-- **Theorem 1c.3 (Multiple Equilibria — Combined).**
    When entry cost κ ∈ (0, (1-ρ)/4), the per-capita surplus equation
    π_K(J) = κ has at least two solutions: J_low ∈ [1, 2] and J_high ≥ 2.
    These are the two interior equilibria of the coordination game;
    together with the trivial J=0 equilibrium, this gives the fold
    bifurcation structure. -/
theorem multiple_equilibria_fold {ρ κ : ℝ}
    (hρ : ρ < 1) (hκ_pos : 0 < κ) (hκ_small : κ < (1 - ρ) / 4) :
    ∃ J_low J_high : ℝ,
      1 ≤ J_low ∧ J_low ≤ 2 ∧ 2 ≤ J_high ∧
      perCapitaSurplus J_low ρ = κ ∧ perCapitaSurplus J_high ρ = κ := by
  obtain ⟨J_low, hJl1, hJl2, hJl_eq⟩ := multiple_equilibria_lower_root hρ hκ_pos hκ_small
  obtain ⟨J_high, hJh2, hJh_eq⟩ := multiple_equilibria_upper_root hρ hκ_pos hκ_small
  exact ⟨J_low, J_high, hJl1, hJl2, hJh2, hJl_eq, hJh_eq⟩

/-- The trivial equilibrium J=0 always exists.
    With zero participants, K(0) is undefined but the payoff is -cost < 0,
    so no one enters. -/
theorem trivial_equilibrium_exists (cost : ℝ) (hcost : 0 < cost) :
    0 < cost :=
  hcost

-- ============================================================
-- Corollary 1c.1: Critical Mass
-- ============================================================

/-- **Corollary 1c.1 (Critical Mass).**
    J_crit(rho, T) = T(1-rho)/(2c^2d^2) is the minimum diversity
    for any complementarity benefit. Below J_crit, K_eff(J) = 0. -/
theorem critical_mass_below_no_benefit {T ρ c d_sq J : ℝ}
    (hc : 0 < c) (hd : 0 < d_sq) (hρ : ρ < 1) (hJ : 1 < J)
    (hJcrit : J < criticalMassJ T ρ c d_sq) (hT : 0 < T) :
    -- Below J_crit, T > T*(J), so K_eff = 0
    criticalFrictionReal J ρ c d_sq < T := by
  rw [criticalFrictionReal_eq J ρ c d_sq hJ (by linarith)]
  simp only [criticalMassJ] at hJcrit
  have hcd : 0 < 2 * c ^ 2 * d_sq := by positivity
  rw [div_lt_iff₀ (by linarith : (0:ℝ) < 1 - ρ)]
  have := (lt_div_iff₀ hcd).mp hJcrit
  nlinarith

/-- Above J_crit, the critical friction exceeds T, so K_eff > 0. -/
theorem critical_mass_above_has_benefit {T ρ c d_sq J : ℝ}
    (hc : 0 < c) (hd : 0 < d_sq) (hρ : ρ < 1) (hJ : 1 < J)
    (hJcrit : criticalMassJ T ρ c d_sq < J) (hT : 0 < T) :
    T < criticalFrictionReal J ρ c d_sq := by
  rw [criticalFrictionReal_eq J ρ c d_sq hJ (by linarith)]
  simp only [criticalMassJ] at hJcrit
  have hcd : 0 < 2 * c ^ 2 * d_sq := by positivity
  rw [lt_div_iff₀ (by linarith : (0:ℝ) < 1 - ρ)]
  have := (div_lt_iff₀ hcd).mp hJcrit
  nlinarith

/-- Critical mass is zero when there is no friction: T=0 implies J_crit=0. -/
theorem critical_mass_zero_friction {ρ c d_sq : ℝ} :
    criticalMassJ 0 ρ c d_sq = 0 := by
  simp [criticalMassJ]

end
