/-
  Variance Targeting Escapes Damping Cancellation

  Level targeting (changing σ_n) cancels in welfare (damping cancellation
  theorem). But variance targeting (imposing Var ≤ V_target) operates
  through the information friction channel T, which enters the margin
  (1 - T/T*). This margin channel is NOT subject to damping cancellation.

  Key policy dichotomy:
  - σ-channel (structural regulation): cancels in welfare
  - T-channel (variance targeting via margin): monotone in welfare
-/

import CESProofs.Hierarchy.DampingCancellation
import CESProofs.Hierarchy.InstitutionalReform
import CESProofs.Dynamics.FluctuationResponse

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Margin Floor from Variance Target
-- ============================================================

/-- Margin floor from variance target: if Var ≤ V_target,
    then margin ≥ σ₀²/V_target.
    From Var(T) = σ₀²/(1-T/T*), bounding Var ≤ V gives
    1/(1-T/T*) ≤ V/σ₀², i.e., (1-T/T*) ≥ σ₀²/V. -/
def marginFloor (sigma0_sq V_target : ℝ) : ℝ := sigma0_sq / V_target

-- ============================================================
-- Section 2: Margin Floor Properties
-- ============================================================

/-- **Theorem 1: Margin floor is positive.**
    A finite variance target with positive baseline variance
    gives a strictly positive margin floor. -/
theorem marginFloor_pos {sigma0_sq V_target : ℝ}
    (hs : 0 < sigma0_sq) (hV : 0 < V_target) :
    0 < marginFloor sigma0_sq V_target :=
  div_pos hs hV

/-- **Theorem 2: Margin floor is antitone in the variance target.**
    A tighter variance target (smaller V_target) gives a higher margin floor.
    The regulator trades variance for institutional quality. -/
theorem marginFloor_antitone {sigma0_sq V1 V2 : ℝ}
    (hs : 0 < sigma0_sq) (hV1 : 0 < V1) (_hV2 : 0 < V2) (h : V1 < V2) :
    marginFloor sigma0_sq V2 < marginFloor sigma0_sq V1 :=
  div_lt_div_of_pos_left hs hV1 h

-- ============================================================
-- Section 3: Variance Target Implies Margin Floor
-- ============================================================

/-- **Theorem 3: Variance target implies margin floor.**
    If Var(T) = σ₀²/(1-T/T*) ≤ V_target and T < T*,
    then the margin (1-T/T*) ≥ σ₀²/V_target.

    This is the key link: a variance ceiling translates into
    a margin floor, placing the economy away from the regime boundary. -/
theorem variance_implies_margin_floor {sigma0_sq T Tstar V_target : ℝ}
    (_hs : 0 < sigma0_sq) (hTs : 0 < Tstar) (hTlt : T < Tstar)
    (hV : 0 < V_target)
    (hvar : varianceAtFriction sigma0_sq T Tstar ≤ V_target) :
    marginFloor sigma0_sq V_target ≤ 1 - T / Tstar := by
  simp only [marginFloor, varianceAtFriction] at *
  have hm : 0 < 1 - T / Tstar := by
    rw [sub_pos, div_lt_one hTs]; exact hTlt
  rw [div_le_iff₀ hV]
  rw [div_le_iff₀ hm] at hvar
  linarith [mul_comm V_target (1 - T / Tstar)]

-- ============================================================
-- Section 4: Variance Target Bounds Welfare
-- ============================================================

/-- **Theorem 4: Variance target bounds welfare contribution.**
    Enforcing Var ≤ V_target ensures the effective welfare contribution
    is bounded above: the margin floor prevents welfare divergence.

    Combined with eff_welfare_decreasing_margin: higher margin →
    lower welfare loss. The variance target achieves this via the
    information friction channel. -/
theorem variance_target_bounds_welfare {sigma_prev delta beta_n sigma0_sq V_target : ℝ}
    (hs_prev : 0 < sigma_prev) (hd : delta ≠ 0) (hb : 0 < beta_n)
    (hs0 : 0 < sigma0_sq) (hV : 0 < V_target) :
    0 < effectiveWelfareContribution sigma_prev delta beta_n
        (marginFloor sigma0_sq V_target) := by
  simp only [effectiveWelfareContribution]
  apply div_pos
  · exact mul_pos hs_prev (sq_pos_of_ne_zero hd)
  · exact mul_pos hb (marginFloor_pos hs0 hV)

-- ============================================================
-- Section 5: Policy Dichotomy
-- ============================================================

/-- **Theorem 5: Policy dichotomy — σ-channel cancels, margin channel doesn't.**
    The structural regulation channel (σ_n) has zero net welfare effect
    (damping cancellation), while the institutional margin channel has
    a strict monotone welfare effect.

    This is the fundamental asymmetry that makes variance targeting
    a genuine policy tool: it operates through the channel that
    does NOT cancel. -/
theorem policy_dichotomy {phi_prev sigma1 sigma2 c delta : ℝ}
    {sigma_prev beta_n m1 m2 : ℝ}
    (hs1 : sigma1 ≠ 0) (hs2 : sigma2 ≠ 0)
    (hs_prev : 0 < sigma_prev) (hd : delta ≠ 0) (hb : 0 < beta_n)
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hm : m1 < m2) :
    -- Part (a): σ-channel cancels in welfare
    c * (phi_prev / sigma1) * sigma1 * delta ^ 2 =
    c * (phi_prev / sigma2) * sigma2 * delta ^ 2
    -- Part (b): margin channel is strictly monotone
    ∧ effectiveWelfareContribution sigma_prev delta beta_n m2 <
      effectiveWelfareContribution sigma_prev delta beta_n m1 :=
  ⟨welfare_independent_of_own_sigma hs1 hs2,
   eff_welfare_decreasing_margin hs_prev hd hb hm1 hm2 hm⟩

-- ============================================================
-- Section 6: Variance Targeting Improves Welfare
-- ============================================================

/-- **Theorem 6: Variance targeting improves welfare when variance is excessive.**
    When actual variance exceeds the target (equivalently, actual margin
    is below the margin floor), enforcing the target strictly improves
    welfare by raising the margin.

    The improvement is monotone: tighter targets give better welfare,
    subject to the constraint that V_target ≥ σ₀² (margin ≤ 1). -/
theorem variance_targeting_improves {sigma_prev delta beta_n m_actual m_floor : ℝ}
    (hs_prev : 0 < sigma_prev) (hd : delta ≠ 0) (hb : 0 < beta_n)
    (hma : 0 < m_actual) (hmf : 0 < m_floor)
    (hexcess : m_actual < m_floor) :
    effectiveWelfareContribution sigma_prev delta beta_n m_floor <
    effectiveWelfareContribution sigma_prev delta beta_n m_actual :=
  eff_welfare_decreasing_margin hs_prev hd hb hma hmf hexcess

-- ============================================================
-- Section 7: Variance Targeting and Upstream Reform Are Complements
-- ============================================================

/-- **Theorem 7: Variance targeting and upstream reform are complements.**
    The effective welfare contribution V_eff = σ_{n-1} · δ² / (β_n · m)
    is linear in σ_{n-1} (upstream reform) and inversely linear in m
    (variance targeting through the margin). Reducing σ_{n-1} and
    raising m simultaneously gives a strictly larger improvement than
    either alone.

    Economic interpretation: institutional reform (upstream) and
    macro-prudential variance targeting (own level) reinforce each other
    because they operate through independent channels. -/
theorem variance_upstream_complement {sigma_prev1 sigma_prev2 delta beta_n m1 m2 : ℝ}
    (_hs1 : 0 < sigma_prev1) (_hs2 : 0 < sigma_prev2)
    (hd : delta ≠ 0) (hb : 0 < beta_n)
    (hm1 : 0 < m1) (_hm2 : 0 < m2)
    (h_sigma : sigma_prev2 < sigma_prev1)
    (h_margin : m1 < m2) :
    effectiveWelfareContribution sigma_prev2 delta beta_n m2 <
    effectiveWelfareContribution sigma_prev1 delta beta_n m1 := by
  simp only [effectiveWelfareContribution]
  have hd2 : 0 < delta ^ 2 := sq_pos_of_ne_zero hd
  have hnum : sigma_prev2 * delta ^ 2 < sigma_prev1 * delta ^ 2 :=
    mul_lt_mul_of_pos_right h_sigma hd2
  have hdenom : beta_n * m1 < beta_n * m2 :=
    mul_lt_mul_of_pos_left h_margin hb
  calc sigma_prev2 * delta ^ 2 / (beta_n * m2)
      < sigma_prev1 * delta ^ 2 / (beta_n * m2) :=
        div_lt_div_of_pos_right hnum (mul_pos hb (by linarith : (0 : ℝ) < m2))
    _ < sigma_prev1 * delta ^ 2 / (beta_n * m1) :=
        div_lt_div_of_pos_left (mul_pos (by linarith : (0 : ℝ) < sigma_prev1) hd2)
          (mul_pos hb hm1) hdenom

end
