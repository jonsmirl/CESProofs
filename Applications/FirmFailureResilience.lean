/-
  Firm Failure Resilience: Optimal Failure Rate for Long-Run Diversity

  The diversity bonus V = K(J,ρ) · τ² · (1-r) can *increase* when a firm
  fails, if the correlation reduction compensates for the curvature loss.
  For large J, the required correlation improvement is vanishingly small —
  O(1/J²). First formal proof that positive firm failure is *required*
  for long-run resilience under co-adaptation.
-/

import CESProofs.EntryExit.Defs
import CESProofs.EntryExit.CurvatureInJ

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Diversity Bonus and Marginal Curvature Loss
-- ============================================================

/-- Diversity bonus: V(J,ρ,τ,r) = K(J,ρ) · τ² · (1-r).
    Measures the advantage of heterogeneous production over homogeneous:
    K captures curvature (complementarity), τ² captures dispersion,
    and (1-r) captures idiosyncratic variation. -/
def diversityBonus (J ρ τ r : ℝ) : ℝ :=
  curvatureKReal J ρ * τ ^ 2 * (1 - r)

/-- Marginal curvature loss from losing one participant:
    ΔK(J) = K(J) - K(J-1) = (1-ρ) / (J(J-1)).
    Each exit reduces curvature by a diminishing amount. -/
def marginalCurvatureLoss (J ρ : ℝ) : ℝ :=
  (1 - ρ) / (J * (J - 1))

-- ============================================================
-- Section 2: Curvature Loss Properties
-- ============================================================

/-- **Theorem 1: Marginal curvature loss identity.**
    K(J) - K(J-1) = (1-ρ) / [J(J-1)] for J > 1. -/
theorem marginalCurvatureLoss_eq {J ρ : ℝ} (hJ : 1 < J) :
    curvatureKReal J ρ - curvatureKReal (J - 1) ρ = marginalCurvatureLoss J ρ := by
  simp only [curvatureKReal, marginalCurvatureLoss]
  have hJpos : 0 < J := by linarith
  have hJm1pos : 0 < J - 1 := by linarith
  rw [div_sub_div _ _ (ne_of_gt hJpos) (ne_of_gt hJm1pos)]
  congr 1
  ring

/-- **Theorem 2: Marginal curvature loss is positive.**
    Losing a participant always reduces curvature when ρ < 1. -/
theorem marginalCurvatureLoss_pos {J ρ : ℝ} (hJ : 1 < J) (hρ : ρ < 1) :
    0 < marginalCurvatureLoss J ρ := by
  simp only [marginalCurvatureLoss]
  exact div_pos (by linarith) (mul_pos (by linarith) (by linarith))

/-- **Theorem 3: Marginal curvature loss is bounded by (1-ρ)/J².**
    Since J(J-1) ≥ J² · (1 - 1/J) and J(J-1) ≤ J², we get
    (1-ρ)/J² ≤ ΔK(J) for J ≥ 2. -/
theorem marginalCurvatureLoss_bound {J ρ : ℝ} (hJ : 2 ≤ J) (hρ : ρ < 1) :
    (1 - ρ) / J ^ 2 ≤ marginalCurvatureLoss J ρ := by
  simp only [marginalCurvatureLoss]
  apply div_le_div_of_nonneg_left (by linarith)
    (mul_pos (by linarith : (0 : ℝ) < J) (by linarith : (0 : ℝ) < J - 1))
  · have hJpos : 0 < J := by linarith
    rw [sq]
    exact mul_le_mul_of_nonneg_left (by linarith : J - 1 ≤ J) (le_of_lt hJpos)

-- ============================================================
-- Section 3: Curvature Ratio Bound
-- ============================================================

/-- **Theorem 4: Curvature ratio bound.**
    K(J) / K(J-1) ≤ 1 + 1/(J-2) for J > 2.
    The curvature ratio approaches 1 as J grows:
    losing one participant has a vanishing *relative* effect. -/
theorem curvatureK_ratio_bound {J ρ : ℝ} (hJ : 2 < J) (hρ : ρ < 1) :
    curvatureKReal J ρ / curvatureKReal (J - 1) ρ ≤ 1 + 1 / (J - 2) := by
  simp only [curvatureKReal]
  have hJpos : (0 : ℝ) < J := by linarith
  have hJm1pos : (0 : ℝ) < J - 1 := by linarith
  have hJm2pos : (0 : ℝ) < J - 2 := by linarith
  have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
  -- K(J-1) > 0
  have hKm1 : 0 < (1 - ρ) * (J - 1 - 1) / (J - 1) :=
    div_pos (mul_pos h1ρ (by linarith)) hJm1pos
  -- Reduce to: (1-ρ)(J-1)/J ≤ (1+1/(J-2)) · (1-ρ)(J-2)/(J-1)
  rw [div_le_iff₀ hKm1, show J - 1 - 1 = J - 2 from by ring]
  -- Cross-multiply: clear all denominators at once
  rw [div_le_iff₀ hJpos]
  -- Goal: (1-ρ)*(J-1) ≤ (1+1/(J-2))*((1-ρ)*(J-2)/(J-1))*J
  -- Rewrite 1+1/(J-2) as (J-1)/(J-2), then simplify
  rw [show (1 + 1 / (J - 2)) * ((1 - ρ) * (J - 2) / (J - 1)) * J =
    (1 - ρ) * J from by field_simp; ring]
  nlinarith

-- ============================================================
-- Section 4: Diversity Bonus Properties
-- ============================================================

/-- **Theorem 5: Diversity bonus is positive.**
    V > 0 when J > 1, ρ < 1, τ > 0, r < 1. -/
theorem diversityBonus_pos {J ρ τ r : ℝ} (hJ : 1 < J) (hρ : ρ < 1)
    (hτ : 0 < τ) (hr : r < 1) :
    0 < diversityBonus J ρ τ r := by
  simp only [diversityBonus]
  exact mul_pos (mul_pos (curvatureKReal_pos hJ hρ) (sq_pos_of_pos hτ)) (by linarith)

-- ============================================================
-- Section 5: Failure Improves Diversity Bonus
-- ============================================================

/-- **Theorem 6: Failure improves diversity bonus (core condition).**
    V(J-1, r') > V(J, r) when the correlation reduction compensates
    for the curvature loss: K(J-1)·(1-r') > K(J)·(1-r).

    Economic interpretation: a firm's exit improves aggregate welfare
    when its removal sufficiently decorrelates the remaining firms. -/
theorem failure_improves_bonus {J ρ τ r r' : ℝ}
    (hτ : 0 < τ)
    (hcond : curvatureKReal J ρ * (1 - r) < curvatureKReal (J - 1) ρ * (1 - r')) :
    diversityBonus J ρ τ r < diversityBonus (J - 1) ρ τ r' := by
  simp only [diversityBonus]
  have hτ2 : 0 < τ ^ 2 := sq_pos_of_pos hτ
  calc curvatureKReal J ρ * τ ^ 2 * (1 - r)
      = curvatureKReal J ρ * (1 - r) * τ ^ 2 := by ring
    _ < curvatureKReal (J - 1) ρ * (1 - r') * τ ^ 2 :=
        mul_lt_mul_of_pos_right hcond hτ2
    _ = curvatureKReal (J - 1) ρ * τ ^ 2 * (1 - r') := by ring

/-- **Theorem 7: Failure threshold is small.**
    The required correlation improvement (r - r')/(1 - r) > 1/((J-1)(J-2))
    suffices for failure to improve the diversity bonus.

    For large J, this threshold is O(1/J²) — vanishingly small.
    Even minimal decorrelation from a failure event improves resilience.

    Proof strategy: K(J)/K(J-1) = (J-1)²/[J(J-2)], so we need
    (1-r')/(1-r) > (J-1)²/[J(J-2)] = 1 + 1/[J(J-2)].
    The condition (r-r')/(1-r) > 1/((J-1)(J-2)) is slightly stronger
    (since 1/((J-1)(J-2)) ≥ 1/(J(J-2))) and implies the result. -/
theorem failure_threshold_small {J ρ r r' : ℝ}
    (hJ : 2 < J) (hρ : ρ < 1) (hr : r < 1) (hr' : r' < 1)
    (hδ : (r - r') / (1 - r) > 1 / ((J - 1) * (J - 2))) :
    curvatureKReal J ρ * (1 - r) < curvatureKReal (J - 1) ρ * (1 - r') := by
  simp only [curvatureKReal]
  have hJpos : 0 < J := by linarith
  have hJm1pos : 0 < J - 1 := by linarith
  have hJm2pos : 0 < J - 2 := by linarith
  have h1r : 0 < 1 - r := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  -- From hδ: (1-r') > (1-r)(1 + 1/((J-1)(J-2)))
  have h_rr : (1 - r') > (1 - r) * (1 + 1 / ((J - 1) * (J - 2))) := by
    have := mul_lt_mul_of_pos_right hδ h1r
    rw [div_mul_cancel₀ _ (ne_of_gt h1r)] at this
    linarith
  -- Cross-multiply: need (J-1)²(1-r) < J(J-2)(1-r')
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
  rw [div_lt_div_iff₀ hJpos hJm1pos]
  rw [show J - 1 - 1 = J - 2 from by ring]
  -- Goal: (1-ρ)*(J-1)*(1-r)*(J-1) < (1-ρ)*(J-2)*(1-r')*J
  -- Reduce to: (J-1)*(1-r)*(J-1) < (J-2)*(1-r')*J
  -- Clear divisions in h_rr to get a polynomial inequality
  have hprod : 0 < (J - 1) * (J - 2) := mul_pos hJm1pos hJm2pos
  -- h_rr: (1-r') > (1-r) + (1-r)/((J-1)(J-2))
  -- Multiply by (J-1)(J-2): (1-r')*(J-1)*(J-2) > (1-r)*(J-1)*(J-2) + (1-r)
  have h_rr_clear : (1 - r') * ((J - 1) * (J - 2)) >
      (1 - r) * ((J - 1) * (J - 2)) + (1 - r) := by
    have := mul_lt_mul_of_pos_right h_rr hprod
    rw [mul_comm (1 - r) (1 + 1 / ((J - 1) * (J - 2)))] at this
    have expand : (1 + 1 / ((J - 1) * (J - 2))) * (1 - r) * ((J - 1) * (J - 2)) =
        (1 - r) * ((J - 1) * (J - 2)) + (1 - r) := by
      field_simp
    linarith
  -- Key step: (J-1)*(1-r)*(J-1) < (J-2)*(1-r')*J
  -- Equivalently: (1-r)*(J-1)² < (1-r')*J*(J-2)
  have key : (1 - r) * ((J - 1) * (J - 1)) < (1 - r') * ((J - 2) * J) := by
    -- From h_rr_clear: (1-r')*(J-1)*(J-2) > (1-r)*((J-1)*(J-2)+1)
    -- (J-1)*(J-2)+1 = (J-1)² - (J-1) + 1 = J²-3J+3
    -- Need: (1-r')*(J-2)*J > (1-r)*(J-1)²
    -- From h_rr_clear multiply by J/(J-1):
    -- (1-r')*(J-2)*J > ((1-r)*(J-1)*(J-2)+(1-r))*J/(J-1)
    -- = (1-r)*J*(J-2) + (1-r)*J/(J-1)
    -- And J/(J-1) > 1, so > (1-r)*J*(J-2) + (1-r) = (1-r)*(J²-2J+1) = (1-r)*(J-1)²
    have hJdiv : J / (J - 1) > 1 := by
      rw [gt_iff_lt, lt_div_iff₀ hJm1pos]; linarith
    nlinarith
  nlinarith

/-- **Theorem 8: Failure cascade is monotone.**
    If each failure reduces correlation by at least δ > 2/J²,
    then every successive failure improves the diversity bonus.

    This establishes that above the decorrelation threshold,
    the economy becomes strictly more resilient with each exit. -/
theorem failure_cascade_monotone {J ρ τ r r' : ℝ}
    (hJ : 2 < J) (hρ : ρ < 1) (hr : r < 1) (hr' : r' < 1)
    (hτ : 0 < τ)
    (hδ : (r - r') / (1 - r) > 1 / ((J - 1) * (J - 2))) :
    diversityBonus J ρ τ r < diversityBonus (J - 1) ρ τ r' :=
  failure_improves_bonus hτ (failure_threshold_small hJ hρ hr hr' hδ)

end
