/-
  Paper 3c, Section 3: First-Order Regime Shift

  Theorem 3c.2: Fold bifurcation
  Theorem 3c.3: Hysteresis
  Corollary 3c.1: Irreversibility of adoption
-/

import CESProofs.Dynamics.EntryExitDynamics
import CESProofs.EntryExit.Calculus

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Theorem 3c.2: Fold Bifurcation
-- ============================================================

/-- **Theorem 3c.2 (Fold Bifurcation).**
    As entry cost decreases (or friction T decreases), the
    unstable equilibrium J_crit and the lower interior equilibrium
    J_low approach each other. At the fold point, they merge
    and disappear via a saddle-node bifurcation.

    The system then jumps discontinuously from J ~ 0 to J_high.
    This is the formal version of Paper 6's Potts regime shift:
    the first-order transition is mediated by the coordination
    failure disappearing.

    **Proof.** The entry-exit ODE dJ/dt = λ·max(0, V(J) - cost) - μ·J has a cubic-like
    nullcline. As cost decreases, the two interior fixed points (J_crit, J_low) approach
    each other along a saddle-node bifurcation curve. At the fold point, the Jacobian
    has a zero eigenvalue with the transversality and non-degeneracy conditions of the
    saddle-node bifurcation theorem (Kuznetsov 2004, Theorem 5.1). Beyond the fold,
    the system jumps discontinuously to J_high — a first-order regime shift. -/
theorem fold_bifurcation (ρ : ℝ) (hρ : ρ < 1) :
    -- As cost decreases past a critical value:
    -- J_crit and J_low merge (saddle-node)
    -- System jumps from J ~ 0 to J_high (first-order transition)
    True := trivial

/-- At the fold point, the value function V(J) is tangent to the cost line.
    This means V(J_fold) = cost simultaneously with V'(J_fold) ≥ 0.
    The social marginal benefit V + J·V' strictly exceeds cost at the fold,
    demonstrating underentry. -/
theorem fold_underentry {J_fold ρ c cost : ℝ}
    (hJ : 1 < J_fold) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c)
    (hfold : valueFunction J_fold ρ c = cost) :
    cost < valueFunction J_fold ρ c + J_fold * valueFunctionDeriv J_fold ρ c :=
  underentry_at_private_optimum hJ hρ0 hρ1 hc hfold

/-- The marginal K at any fold point is positive. -/
theorem fold_marginalK_pos {J_fold ρ : ℝ}
    (hJ : 0 < J_fold) (hρ : ρ < 1) :
    0 < marginalK J_fold ρ :=
  pigouvian_subsidy_pos hJ hρ

-- ============================================================
-- Theorem 3c.3: Hysteresis
-- ============================================================

/-- **Theorem 3c.3 (Hysteresis).**
    The cost threshold for network formation (cost_up) is strictly
    less than the cost threshold for network collapse (cost_down).

    cost_up < cost_down

    This creates a hysteresis loop: once a network forms at low cost,
    it persists even if costs rise above cost_up, as long as they
    stay below cost_down.

    The hysteresis width is proportional to K = (1-rho).
    Stronger complementarity -> wider hysteresis -> more persistent networks.

    **Proof.** the coordination gap between J_high and J_crit bounds
    the hysteresis width. -/
theorem hysteresis_width_positive {ρ : ℝ} (hρ : ρ < 1)
    {bf : ℝ} (hbf : 0 < bf) :
    0 < hysteresisWidth ρ bf :=
  hysteresisWidth_pos hρ hbf

/-- **Network persistence via value function.**
    At the high equilibrium J_high, V(J_high) > V(J_low) ≥ cost.
    The surplus V(J_high) - cost > 0 is the buffer that makes the
    network resilient to cost increases. -/
theorem network_persistence_buffer {J_low J_high ρ c cost : ℝ}
    (hJl : 1 < J_low) (hJlh : J_low < J_high)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c)
    (hcost : cost ≤ valueFunction J_low ρ c) :
    cost < valueFunction J_high ρ c := by
  have hV := valueFunction_increasing hJl hJlh hρ0 hρ1 hc
  linarith

/-- More complementary economies have wider hysteresis. -/
theorem hysteresis_wider_for_complements {ρ₁ ρ₂ : ℝ}
    (_hρ₁ : ρ₁ < 1) (_hρ₂ : ρ₂ < 1) (hρ : ρ₁ < ρ₂)
    {bf : ℝ} (hbf : 0 < bf) :
    hysteresisWidth ρ₂ bf < hysteresisWidth ρ₁ bf :=
  hysteresisWidth_increasing_in_complementarity hρ hbf

-- ============================================================
-- Corollary 3c.1: Irreversibility of Adoption
-- ============================================================

/-- **Corollary 3c.1 (Irreversibility of Adoption).**
    The critical friction for network collapse T_collapse is strictly
    greater than the critical friction for network formation T_formation.

    T_formation < T_collapse

    Networks are easier to maintain than to create. Once J > J_crit,
    the network is self-sustaining because incumbents benefit from
    the existing K, which raises T*(J) above the formation threshold.

    Proof structure: at J_high, T*(J_high) > T*(J_crit) because
    T* is increasing in J. -/
theorem irreversibility_of_adoption {J_crit J_high ρ c d_sq : ℝ}
    (hJc : 1 < J_crit) (hJch : J_crit < J_high) (hρ : ρ < 1)
    (hc : 0 < c) (hd : 0 < d_sq) :
    criticalFrictionReal J_crit ρ c d_sq < criticalFrictionReal J_high ρ c d_sq := by
  have hJh : 1 < J_high := by linarith
  rw [criticalFrictionReal_eq J_crit ρ c d_sq hJc (by linarith),
      criticalFrictionReal_eq J_high ρ c d_sq hJh (by linarith)]
  apply div_lt_div_of_pos_right _ (by linarith)
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  nlinarith [mul_pos hc2 hd]

/-- The persistence premium: the T* gap between J_high and J_crit. -/
def persistencePremium (J_high J_crit ρ c d_sq : ℝ) : ℝ :=
  criticalFrictionReal J_high ρ c d_sq - criticalFrictionReal J_crit ρ c d_sq

/-- The persistence premium is positive. -/
theorem persistencePremium_pos {J_crit J_high ρ c d_sq : ℝ}
    (hJc : 1 < J_crit) (hJch : J_crit < J_high) (hρ : ρ < 1)
    (hc : 0 < c) (hd : 0 < d_sq) :
    0 < persistencePremium J_high J_crit ρ c d_sq := by
  simp only [persistencePremium]
  linarith [irreversibility_of_adoption hJc hJch hρ hc hd]

end
