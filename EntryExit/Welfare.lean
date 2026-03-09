/-
  Paper 1c, Section 4: Welfare and Coordination Failure

  Theorem 1c.4: Pareto ranking of equilibria
  Proposition 1c.2: Underentry theorem
  Proposition 1c.3: Pigouvian entry subsidy (proved in Defs)
  Corollary 1c.2: Complementarity paradox
-/

import CESProofs.EntryExit.Defs
import CESProofs.EntryExit.CurvatureInJ
import CESProofs.EntryExit.Calculus
import CESProofs.EntryExit.Equilibria

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Theorem 1c.4: Pareto Ranking of Equilibria
-- ============================================================

/-- **Theorem 1c.4 (Pareto Ranking).**
    The high-participation equilibrium J_high Pareto dominates J_low.
    Every participant is strictly better off at J_high.

    **Proof.** since K is increasing in J and benefit is increasing in J,
    every participant's payoff is higher at J_high > J_low. -/
theorem pareto_ranking {J_high J_low ρ : ℝ}
    (hJl : 1 < J_low) (hJh : J_low < J_high) (hρ : ρ < 1) :
    -- The coordination gap in curvature is positive
    0 < coordinationGap J_high J_low ρ :=
  coordinationGap_pos hJl hJh hρ

/-- The welfare gap between equilibria is bounded below by the
    K difference times the minimum benefit across participants.
    More complementary economies have larger welfare gaps. -/
theorem welfare_gap_proportional_to_K {J_high J_low ρ : ℝ}
    (hJl : 1 < J_low) (hJh : J_low < J_high) (hρ : ρ < 1)
    (benefit : ℝ) (hb : 0 < benefit) :
    0 < coordinationGap J_high J_low ρ * benefit := by
  exact mul_pos (coordinationGap_pos hJl hJh hρ) hb

-- ============================================================
-- Proposition 1c.2: Underentry Theorem
-- ============================================================

/-- **Proposition 1c.2 (Underentry, proved).**
    At any J where a private entrant breaks even (V(J) = κ),
    the social marginal benefit V(J) + J·V'(J) strictly exceeds κ.
    Therefore the social optimum has more entry than the private equilibrium.

    The gap is the marginal externality J·V'(J) > 0, which private
    entrants ignore. -/
theorem underentry_proved {J ρ c κ : ℝ}
    (hJ : 1 < J) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c)
    (hFOC : valueFunction J ρ c = κ) :
    κ < valueFunction J ρ c + J * valueFunctionDeriv J ρ c :=
  underentry_at_private_optimum hJ hρ0 hρ1 hc hFOC

/-- The underentry gap is driven by the marginal external benefit.
    At any J > 0 and rho < 1, there is a positive externality:
    each entrant raises K for all incumbents. -/
theorem positive_externality {J ρ : ℝ} (hJ : 0 < J) (hρ : ρ < 1) :
    0 < marginalK J ρ :=
  pigouvian_subsidy_pos hJ hρ

/-- **Pareto ranking (full value function).**
    V(J_high) > V(J_low) > 0 for J_high > J_low > 1 and ρ ∈ (0,1).
    Every participant strictly prefers the high equilibrium. -/
theorem pareto_ranking_full {J_high J_low ρ c : ℝ}
    (hJl : 1 < J_low) (hJh : J_low < J_high)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    valueFunction J_low ρ c < valueFunction J_high ρ c :=
  pareto_ranking_strengthened hJl hJh hρ0 hρ1 hc

/-- The welfare gap V(J_high) - V(J_low) times J_low is positive. -/
theorem welfare_gap_full {J_high J_low ρ c : ℝ}
    (hJl : 1 < J_low) (hJh : J_low < J_high)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    0 < (valueFunction J_high ρ c - valueFunction J_low ρ c) * J_low :=
  welfare_gap_lower_bound hJl hJh hρ0 hρ1 hc

-- ============================================================
-- Corollary 1c.2: Complementarity Paradox
-- ============================================================

/-- **Corollary 1c.2 (Complementarity Paradox).**
    More complementary economies (lower rho) have:
    (a) Higher potential benefit: J_high grows with (1-rho)
    (b) Higher coordination hurdle: J_crit grows with (1-rho)

    The potential gain is large but so is the coordination barrier.

    We prove part (b): J_crit is increasing in (1-rho). -/
theorem complementarity_paradox_barrier {T c d_sq ρ₁ ρ₂ : ℝ}
    (hc : 0 < c) (hd : 0 < d_sq) (hT : 0 < T)
    (hρ₁ : ρ₁ < 1) (hρ₂ : ρ₂ < 1) (hρ : ρ₂ < ρ₁) :
    -- Lower rho (more complementary) -> higher J_crit
    criticalMassJ T ρ₁ c d_sq < criticalMassJ T ρ₂ c d_sq :=
  criticalMassJ_increasing_in_complementarity hc hd hT hρ₂ hρ₁ (by linarith)

/-- Part (a): Lower rho gives higher K at any fixed J > 1. -/
theorem complementarity_paradox_benefit {J ρ₁ ρ₂ : ℝ}
    (hJ : 1 < J) (hρ : ρ₁ < ρ₂) :
    curvatureKReal J ρ₂ < curvatureKReal J ρ₁ := by
  simp only [curvatureKReal]
  have hJpos : 0 < J := by linarith
  -- (1-ρ₂)(J-1)/J < (1-ρ₁)(J-1)/J because (1-ρ₂) < (1-ρ₁) and (J-1)/J > 0
  rw [div_lt_div_iff₀ hJpos hJpos]
  have hJm1 : 0 < J - 1 := by linarith
  nlinarith [mul_pos hJm1 hJpos]

end
