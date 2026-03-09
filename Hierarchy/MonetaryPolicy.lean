/-
  Monetary Policy and the Liquidity Trap
  (Paper 4, Section 10)

  Applies the effective curvature framework to monetary policy transmission.
  Four results:

  1. Policy response: reducing friction increases effective curvature
  2. Liquidity trap: at T ≥ T*, marginal friction reductions have no effect
  3. Monetary transmission ordering: complementary sectors respond more to policy
  4. Policy margin: the space for policy narrows as friction approaches T*

  Key insight: monetary policy works by reducing information friction T.
  Its effectiveness depends on K_eff = K·(1-T/T*)⁺. At the regime
  boundary T = T*, the economy is in a liquidity trap: K_eff = 0 and
  marginal friction reductions are impotent until T drops below T*.
-/

import CESProofs.Potential.BilateralTrade

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Policy Response
-- ============================================================

/-- **The policy response**: the change in effective curvature from
    reducing information friction from T_old to T_new (T_new ≤ T_old).

    Monetary policy works by reducing information friction: lowering
    transaction costs, improving transparency, enhancing contract
    enforcement. The output gain is the increase in K_eff. -/
def policyResponse (J : ℕ) (ρ T_new T_old Tstar : ℝ) : ℝ :=
  effectiveCurvatureKeff J ρ T_new Tstar - effectiveCurvatureKeff J ρ T_old Tstar

/-- **Policy response is non-negative when friction decreases.**
    Reducing information friction never hurts—it either increases
    effective curvature or leaves it unchanged. -/
theorem policyResponse_nonneg {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T_new T_old Tstar : ℝ} (hTs : 0 < Tstar) (h : T_new ≤ T_old) :
    0 ≤ policyResponse J ρ T_new T_old Tstar := by
  simp only [policyResponse]
  linarith [bilateral_Keff_decreasing hJ hρ hTs h]

/-- **Policy response is strictly positive when crossing the boundary.**
    Reducing friction from above T* to below T* generates a discrete
    jump in effective curvature. This is the economy "escaping" the
    liquidity trap—crossing the regime boundary is a discontinuous event. -/
theorem policyResponse_pos_crossing {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T_new T_old Tstar : ℝ} (hTs : 0 < Tstar)
    (hNew_nn : 0 ≤ T_new) (hNew : T_new < Tstar) (hOld : Tstar ≤ T_old) :
    0 < policyResponse J ρ T_new T_old Tstar := by
  simp only [policyResponse]
  rw [effectiveCurvatureKeff_above_critical J ρ T_old Tstar hTs hOld]
  simp only [sub_zero]
  exact effectiveCurvatureKeff_pos hJ hρ hNew_nn hTs hNew

-- ============================================================
-- Section 2: The Liquidity Trap
-- ============================================================

/-- **The liquidity trap.**
    When both the new and old friction levels are above T*,
    reducing friction has no effect: the economy remains at K_eff = 0.

    This is the CES formalization of the liquidity trap: the economy
    is stuck in the super-critical regime where complementarity
    benefits have vanished, and marginal policy adjustments are impotent. -/
theorem liquidity_trap {J : ℕ} {ρ : ℝ}
    {T_new T_old Tstar : ℝ} (hTs : 0 < Tstar)
    (hNew : Tstar ≤ T_new) (hOld : Tstar ≤ T_old) :
    policyResponse J ρ T_new T_old Tstar = 0 := by
  simp only [policyResponse]
  rw [effectiveCurvatureKeff_above_critical J ρ T_new Tstar hTs hNew,
      effectiveCurvatureKeff_above_critical J ρ T_old Tstar hTs hOld]
  ring

/-- **Escaping the liquidity trap.**
    To restore positive effective curvature, friction must be reduced
    below T*. Once T < T*, K_eff = K·(1-T/T*) > 0 and the economy
    regains complementarity benefits.

    The discontinuity at T* is the key prediction: recovery is not
    gradual but requires crossing a threshold. -/
theorem liquidity_trap_escape {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T Tstar : ℝ} (hTs : 0 < Tstar) (hT_nn : 0 ≤ T) (hT : T < Tstar) :
    0 < effectiveCurvatureKeff J ρ T Tstar :=
  effectiveCurvatureKeff_pos hJ hρ hT_nn hTs hT

/-- **Policy ineffectiveness above the critical threshold.**
    Even a large reduction in friction is useless if the economy
    remains above T*. Any T ≥ T* gives K_eff = 0. -/
theorem policy_ineffective_above_critical {J : ℕ} {ρ : ℝ}
    {T Tstar : ℝ} (hTs : 0 < Tstar) (hT : Tstar ≤ T) :
    effectiveCurvatureKeff J ρ T Tstar = 0 :=
  effectiveCurvatureKeff_above_critical J ρ T Tstar hTs hT

-- ============================================================
-- Section 3: Monetary Transmission Ordering
-- ============================================================

/-- **Monetary transmission ordering: complementary sectors respond more.**
    For two sectors with ρ₁ < ρ₂ receiving the same friction reduction:
    the more complementary sector (ρ₁) has a larger policy response.

    This implies that monetary policy is most effective in sectors with
    complementary inputs (manufacturing, construction) and least
    effective in sectors with substitutable inputs (digital services).

    **Proof.** policyResponse = K(ρ) · Δm, where Δm is the change in the
    degradation factor (common across sectors). Since K(ρ₁) > K(ρ₂),
    the response is proportionally larger. -/
theorem monetary_transmission_ordering {J : ℕ} (hJ : 2 ≤ J)
    {ρ1 ρ2 : ℝ} (hρ : ρ1 < ρ2)
    {T_new T_old Tstar : ℝ} (hTs : 0 < Tstar) (h : T_new ≤ T_old) :
    policyResponse J ρ2 T_new T_old Tstar ≤
    policyResponse J ρ1 T_new T_old Tstar := by
  simp only [policyResponse, effectiveCurvatureKeff]
  -- Factor: K(ρ) * m_new - K(ρ) * m_old = K(ρ) * (m_new - m_old)
  rw [(mul_sub (curvatureK J ρ1) _ _).symm, (mul_sub (curvatureK J ρ2) _ _).symm]
  -- K(ρ₂) * dm ≤ K(ρ₁) * dm where dm = m_new - m_old ≥ 0
  exact mul_le_mul_of_nonneg_right
    (le_of_lt (curvatureK_decreasing_in_rho hJ hρ))
    (by linarith [degradation_monotone hTs h])

/-- **Institutional amplification.**
    Better institutions (higher T*) amplify the effect of monetary policy
    at any given friction level T. The effective curvature is monotone
    in T*: K_eff(T, T*₁) ≤ K_eff(T, T*₂) when T*₁ ≤ T*₂.

    Countries with stronger institutions (higher T*) get more output
    per unit of friction reduction. This formalizes the empirical finding
    that monetary policy is more effective in countries with better
    institutions. -/
theorem institutional_amplification {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T Tstar1 Tstar2 : ℝ} (hTs1 : 0 < Tstar1) (hTs2 : 0 < Tstar2)
    (h : Tstar1 ≤ Tstar2) (hT : 0 ≤ T) :
    effectiveCurvatureKeff J ρ T Tstar1 ≤ effectiveCurvatureKeff J ρ T Tstar2 := by
  simp only [effectiveCurvatureKeff]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (curvatureK_pos hJ hρ))
  -- max 0 (1 - T/T*₁) ≤ max 0 (1 - T/T*₂)
  apply max_le_max_left 0
  suffices T / Tstar2 ≤ T / Tstar1 by linarith
  rw [div_le_div_iff₀ hTs2 hTs1]
  exact mul_le_mul_of_nonneg_left h hT

-- ============================================================
-- Section 4: Policy Space
-- ============================================================

/-- **The policy margin**: T* - T, the remaining space before the
    economy crosses the regime boundary. Positive in the sub-critical
    regime, zero or negative above T*.

    The policy margin determines how much additional friction the
    economy can absorb before complementarity benefits vanish. -/
def policyMargin (T Tstar : ℝ) : ℝ := Tstar - T

/-- Policy margin is positive in the sub-critical regime. -/
theorem policyMargin_pos_subcritical {T Tstar : ℝ} (hT : T < Tstar) :
    0 < policyMargin T Tstar := by
  simp only [policyMargin]; linarith

/-- **Policy margin narrows as friction rises.**
    Rising friction inexorably shrinks the distance to the regime
    boundary. The economy's buffer against shocks decreases. -/
theorem policyMargin_narrowing {T1 T2 Tstar : ℝ} (h : T1 ≤ T2) :
    policyMargin T2 Tstar ≤ policyMargin T1 Tstar := by
  simp only [policyMargin]; linarith

/-- Policy margin vanishes at the critical threshold. -/
theorem policyMargin_zero_at_critical {Tstar : ℝ} :
    policyMargin Tstar Tstar = 0 := by
  simp only [policyMargin]; ring

/-- **Complementary sectors have smaller policy margins.**
    Since T*(ρ₁) < T*(ρ₂) when ρ₁ < ρ₂, more complementary sectors
    are closer to the regime boundary at any given friction level.
    They have less room before losing complementarity benefits.

    This is the fragility side of the efficiency-fragility tradeoff:
    sectors that benefit most from low friction are most vulnerable
    to friction increases. -/
theorem complementary_sectors_smaller_margin {J : ℕ} (hJ : 2 ≤ J)
    {ρ1 ρ2 : ℝ} (hρ1 : ρ1 < 1) (hρ2 : ρ2 < 1) (hρ : ρ1 < ρ2)
    {c d_sq : ℝ} (hc : 0 < c) (hd : 0 < d_sq) :
    policyMargin T (criticalFriction J ρ1 c d_sq) <
    policyMargin T (criticalFriction J ρ2 c d_sq) := by
  simp only [policyMargin]
  linarith [complementary_goods_more_fragile hJ hρ1 hρ2 hρ hc hd]

end
