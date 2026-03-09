/-
  Core definitions for the Lean formalization of Paper 1c:
  "Endogenous Diversity: Entry, Coordination, and Critical Mass"

  Makes J endogenous by treating it as a real-valued parameter.
  Defines curvatureKReal, participation payoff, critical mass,
  and coordination gap.

  All other Paper 1c files import this module.
-/

import CESProofs.Foundations.Defs
import CESProofs.Potential.Defs
import CESProofs.Foundations.GeneralWeights

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Real-Valued Curvature
-- ============================================================

/-- The curvature parameter with real-valued J:
    K(J, rho) = (1 - rho) * (J - 1) / J.
    This extends curvatureK to ℝ for calculus on J. -/
def curvatureKReal (J : ℝ) (ρ : ℝ) : ℝ := (1 - ρ) * (J - 1) / J

/-- Compatibility: curvatureKReal at natural J equals curvatureK. -/
theorem curvatureKReal_eq_nat (J : ℕ) (ρ : ℝ) :
    curvatureKReal ↑J ρ = curvatureK J ρ := by
  simp only [curvatureKReal, curvatureK]

-- ============================================================
-- Section 2: Effective Curvature with Real J
-- ============================================================

/-- The critical friction with real-valued J:
    T*(J) = 2(J-1) * c^2 * d^2 / K(J).
    Simplifies to 2 * J * c^2 * d^2 (since (J-1)/K = J/(1-rho)). -/
def criticalFrictionReal (J : ℝ) (ρ c d_sq : ℝ) : ℝ :=
  2 * (J - 1) * c ^ 2 * d_sq / curvatureKReal J ρ

/-- T*(J) simplifies to 2 * J * c^2 * d^2 when J > 1 and rho /= 1.
    Requires J > 1 so that K(J) > 0 (we are dividing by K). -/
theorem criticalFrictionReal_eq (J : ℝ) (ρ c d_sq : ℝ)
    (hJ : 1 < J) (hρ : ρ ≠ 1) :
    criticalFrictionReal J ρ c d_sq = 2 * J * c ^ 2 * d_sq / (1 - ρ) := by
  simp only [criticalFrictionReal, curvatureKReal]
  have hJne : J ≠ 0 := by linarith
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have hJm1 : J - 1 ≠ 0 := by linarith
  field_simp [hJne, h1ρ, hJm1]

/-- Effective curvature with real-valued J:
    K_eff(J) = K(J) * max(0, 1 - T/T*(J)). -/
def effectiveKReal (J ρ T Tstar : ℝ) : ℝ :=
  curvatureKReal J ρ * max 0 (1 - T / Tstar)

-- ============================================================
-- Section 3: Participation Payoff
-- ============================================================

/-- The per-participant benefit at symmetric equilibrium:
    benefit(J) = J^{1/rho - 1} * c.
    This is the per-capita share of G(J) = J^{1/rho} * c. -/
def perCapitaBenefit (J : ℝ) (ρ c : ℝ) : ℝ :=
  J ^ (1 / ρ - 1) * c

/-- Participation payoff:
    pi(J; rho, T, Tstar, c, cost) = K_eff(J) * benefit(J) - cost.
    An agent enters iff pi > 0. -/
def participationPayoff (J ρ T Tstar c cost : ℝ) : ℝ :=
  effectiveKReal J ρ T Tstar * perCapitaBenefit J ρ c - cost

-- ============================================================
-- Section 4: Critical Mass
-- ============================================================

/-- The critical mass: minimum J such that K_eff(J) > 0.
    Since T*(J) = 2Jc^2d^2/(1-rho), we need T < T*(J),
    i.e., J > T(1-rho)/(2c^2d^2).
    J_crit = T(1-rho)/(2c^2d^2). Below this, K_eff = 0. -/
def criticalMassJ (T ρ c d_sq : ℝ) : ℝ :=
  T * (1 - ρ) / (2 * c ^ 2 * d_sq)

/-- At J = J_crit, the critical friction equals T. -/
theorem criticalMassJ_characterization {T ρ c d_sq : ℝ}
    (hc : 0 < c) (hd : 0 < d_sq) (hρ : ρ < 1) :
    2 * criticalMassJ T ρ c d_sq * c ^ 2 * d_sq / (1 - ρ) = T := by
  simp only [criticalMassJ]
  have h1ρ : (0 : ℝ) ≠ 1 - ρ := by linarith
  have hcd : 0 < 2 * c ^ 2 * d_sq := by positivity
  field_simp

/-- Critical mass is increasing in T: more friction requires more participants. -/
theorem criticalMassJ_increasing_in_T {ρ c d_sq T₁ T₂ : ℝ}
    (hc : 0 < c) (hd : 0 < d_sq) (hρ : ρ < 1)
    (hT : T₁ < T₂) :
    criticalMassJ T₁ ρ c d_sq < criticalMassJ T₂ ρ c d_sq := by
  simp only [criticalMassJ]
  apply div_lt_div_of_pos_right
  · exact mul_lt_mul_of_pos_right hT (by linarith)
  · positivity

/-- Critical mass is increasing in (1-rho): more complementary economies
    require more participants to activate. -/
theorem criticalMassJ_increasing_in_complementarity {T c d_sq ρ₁ ρ₂ : ℝ}
    (hc : 0 < c) (hd : 0 < d_sq) (hT : 0 < T)
    (_hρ₁ : ρ₁ < 1) (_hρ₂ : ρ₂ < 1) (hρ : ρ₁ < ρ₂) :
    criticalMassJ T ρ₂ c d_sq < criticalMassJ T ρ₁ c d_sq := by
  simp only [criticalMassJ]
  apply div_lt_div_of_pos_right
  · exact mul_lt_mul_of_pos_left (by linarith) hT
  · positivity

-- ============================================================
-- Section 5: Coordination Gap
-- ============================================================

/-- The coordination gap: welfare difference between J_high and J_low equilibria.
    Measured as K(J_high) - K(J_low) times a benefit factor. -/
def coordinationGap (J_high J_low ρ : ℝ) : ℝ :=
  curvatureKReal J_high ρ - curvatureKReal J_low ρ

/-- The coordination gap is positive when J_high > J_low > 0 and rho < 1. -/
theorem coordinationGap_pos {J_high J_low ρ : ℝ}
    (hJl : 1 < J_low) (hJh : J_low < J_high) (hρ : ρ < 1) :
    0 < coordinationGap J_high J_low ρ := by
  simp only [coordinationGap, curvatureKReal]
  have h1ρ : 0 < 1 - ρ := by linarith
  have hJl_pos : 0 < J_low := by linarith
  have hJh_pos : 0 < J_high := by linarith
  rw [show (1 - ρ) * (J_high - 1) / J_high - (1 - ρ) * (J_low - 1) / J_low =
    (1 - ρ) * ((J_high - 1) / J_high - (J_low - 1) / J_low) from by ring]
  apply mul_pos h1ρ
  rw [div_sub_div _ _ (ne_of_gt hJh_pos) (ne_of_gt hJl_pos)]
  apply div_pos
  · nlinarith
  · exact mul_pos hJh_pos hJl_pos

-- ============================================================
-- Section 6: Pigouvian Entry Subsidy
-- ============================================================

/-- The marginal external benefit of entry at participation level J:
    s(J) = d[K(J)]/dJ * benefit(J) + K(J) * d[benefit(J)]/dJ.
    We define the K-component: dK/dJ = (1-rho)/J^2. -/
def marginalK (J ρ : ℝ) : ℝ := (1 - ρ) / J ^ 2

/-- The optimal Pigouvian entry subsidy equals the marginal external benefit.
    We formalize the curvature component dK/dJ > 0 for rho < 1. -/
theorem pigouvian_subsidy_pos {J ρ : ℝ} (hJ : 0 < J) (hρ : ρ < 1) :
    0 < marginalK J ρ := by
  simp only [marginalK]
  exact div_pos (by linarith) (sq_pos_of_pos hJ)

/-- The marginal external benefit is decreasing in J
    (the subsidy is most needed early). -/
theorem pigouvian_subsidy_decreasing {J₁ J₂ ρ : ℝ}
    (hJ₁ : 0 < J₁) (hρ : ρ < 1) (hJ : J₁ < J₂) :
    marginalK J₂ ρ < marginalK J₁ ρ := by
  simp only [marginalK]
  apply div_lt_div_of_pos_left (by linarith) (sq_pos_of_pos hJ₁)
  exact sq_lt_sq' (by linarith) hJ

end
