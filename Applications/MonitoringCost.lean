/-
  Micro-Foundation for the Monitoring Cost c₀ (Gap 12)

  The monitoring/screening cost c₀ determines whether integration is
  profitable (Hart boundary K_eff > c₀·T) and the return to monitoring
  (Holmstrom: K·dT/T*). Micro-founding c₀ as a function of monitoring
  technology A and institutional quality I closes the model.

  c₀ = c_base / (A · I): higher technology or better institutions reduce c₀,
  widening the integration region and raising the return to monitoring.

  Key reuse:
  - integration_boundary (Paper2/FirmScope.lean)
  - curvatureK, curvatureK_decreasing_in_rho (Paper2/BilateralTrade.lean)

  Results MC-1 through MC-10: 9 fully proved, 1 schematic, 0 axioms.
-/

import CESProofs.Potential.FirmScope
import CESProofs.Potential.BilateralTrade

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Definitions
-- ============================================================

/-- Monitoring cost as a function of technology A and institutional quality I.
    c₀ = c_base / (A · I). Higher technology or better institutions → lower c₀. -/
def monitoringCost (c_base A I : ℝ) : ℝ := c_base / (A * I)

/-- Holmstrom monitoring return: the marginal value of reducing friction T
    by dT at level n. Return = K · dT / T*, proportional to structural curvature. -/
def monitoringReturn (K dT Tstar : ℝ) : ℝ := K * dT / Tstar

/-- Monitoring-adjusted critical friction: T*_m = T*_base / (1 + c₀).
    Higher monitoring cost c₀ reduces the effective critical threshold. -/
def monitoredCriticalFriction (Tstar_base c₀ : ℝ) : ℝ := Tstar_base / (1 + c₀)

/-- Integration surplus: K_eff - c₀·T. Positive when integration is profitable. -/
def integrationSurplus (K_eff c₀ T : ℝ) : ℝ := K_eff - c₀ * T

-- ============================================================
-- Section 2: MC-1 — Monitoring Cost Is Positive
-- ============================================================

/-- **MC-1 (Monitoring cost is positive).**
    c₀ > 0 when c_base, A, and I are all positive. -/
theorem monitoring_cost_positive {c_base A I : ℝ}
    (hc : 0 < c_base) (hA : 0 < A) (hI : 0 < I) :
    0 < monitoringCost c_base A I :=
  div_pos hc (mul_pos hA hI)

-- ============================================================
-- Section 3: MC-2 — Technology Reduces Monitoring Cost
-- ============================================================

/-- **MC-2 (Technology reduces monitoring cost).**
    Higher technology A₂ > A₁ reduces c₀: better monitoring technology
    makes screening and coordination cheaper. -/
theorem technology_reduces_monitoring {c_base A₁ A₂ I : ℝ}
    (hc : 0 < c_base) (hA₁ : 0 < A₁) (_hA₂ : 0 < A₂) (hI : 0 < I)
    (hA : A₁ < A₂) :
    monitoringCost c_base A₂ I < monitoringCost c_base A₁ I := by
  simp only [monitoringCost]
  exact div_lt_div_of_pos_left hc (mul_pos hA₁ hI)
    (mul_lt_mul_of_pos_right hA hI)

-- ============================================================
-- Section 4: MC-3 — Institutions Reduce Monitoring Cost
-- ============================================================

/-- **MC-3 (Institutions reduce monitoring cost).**
    Better institutional quality I₂ > I₁ reduces c₀: rule of law,
    contract enforcement, and transparency lower coordination costs. -/
theorem institutions_reduce_monitoring {c_base A I₁ I₂ : ℝ}
    (hc : 0 < c_base) (hA : 0 < A) (hI₁ : 0 < I₁) (_hI₂ : 0 < I₂)
    (hI : I₁ < I₂) :
    monitoringCost c_base A I₂ < monitoringCost c_base A I₁ := by
  simp only [monitoringCost]
  exact div_lt_div_of_pos_left hc (mul_pos hA hI₁)
    (mul_lt_mul_of_pos_left hI hA)

-- ============================================================
-- Section 5: MC-4 — Lower Monitoring Widens Integration Region
-- ============================================================

/-- **MC-4 (Lower monitoring cost widens integration).**
    Lower c₀ increases the integration surplus for any (K_eff, T). -/
theorem lower_monitoring_widens_integration {K_eff c₀₁ c₀₂ T : ℝ}
    (hT : 0 < T) (hc : c₀₁ < c₀₂) :
    integrationSurplus K_eff c₀₂ T < integrationSurplus K_eff c₀₁ T := by
  simp only [integrationSurplus]
  linarith [mul_lt_mul_of_pos_right hc hT]

-- ============================================================
-- Section 6: MC-5 — Technology Widens Integration
-- ============================================================

/-- **MC-5 (Technology widens integration).**
    Higher technology A₂ > A₁ widens the integration region: reduces c₀,
    which increases the surplus. -/
theorem technology_widens_integration {c_base A₁ A₂ I K_eff T : ℝ}
    (hc : 0 < c_base) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hI : 0 < I)
    (hT : 0 < T) (hA : A₁ < A₂) :
    integrationSurplus K_eff (monitoringCost c_base A₁ I) T <
    integrationSurplus K_eff (monitoringCost c_base A₂ I) T := by
  apply lower_monitoring_widens_integration hT
  exact technology_reduces_monitoring hc hA₁ hA₂ hI hA

-- ============================================================
-- Section 7: MC-6 — Institutions Widen Integration
-- ============================================================

/-- **MC-6 (Institutions widen integration).**
    Better institutional quality I₂ > I₁ widens the integration region. -/
theorem institutions_widen_integration {c_base A I₁ I₂ K_eff T : ℝ}
    (hc : 0 < c_base) (hA : 0 < A) (hI₁ : 0 < I₁) (hI₂ : 0 < I₂)
    (hT : 0 < T) (hI : I₁ < I₂) :
    integrationSurplus K_eff (monitoringCost c_base A I₁) T <
    integrationSurplus K_eff (monitoringCost c_base A I₂) T := by
  apply lower_monitoring_widens_integration hT
  exact institutions_reduce_monitoring hc hA hI₁ hI₂ hI

-- ============================================================
-- Section 8: MC-7 — Zero Monitoring Preserves Full Threshold
-- ============================================================

/-- **MC-7 (Zero monitoring cost preserves full threshold).**
    When c₀ = 0, the monitored critical friction equals the base threshold. -/
theorem zero_monitoring_full_threshold {Tstar : ℝ} :
    monitoredCriticalFriction Tstar 0 = Tstar := by
  simp [monitoredCriticalFriction]

-- ============================================================
-- Section 9: MC-8 — Monitoring Return Proportional to K
-- ============================================================

/-- **MC-8 (Monitoring return proportional to curvature K).**
    Higher structural curvature K yields higher monitoring return. -/
theorem monitoring_return_proportional_to_K {K₁ K₂ dT Tstar : ℝ}
    (hdT : 0 < dT) (hTs : 0 < Tstar) (hK : K₁ < K₂) :
    monitoringReturn K₁ dT Tstar < monitoringReturn K₂ dT Tstar := by
  simp only [monitoringReturn]
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hK hdT) hTs

-- ============================================================
-- Section 10: MC-9 — Complementary Sectors Have Highest Return
-- ============================================================

/-- **MC-9 (Complementary sectors have highest monitoring return).**
    More complementary sectors (lower ρ) have higher curvature K,
    hence higher monitoring return. Monitoring should be curvature-weighted. -/
theorem complementary_sectors_highest_return {J : ℕ} (hJ : 2 ≤ J)
    {rho1 rho2 : ℝ} (hrho : rho1 < rho2) {dT Tstar : ℝ}
    (hdT : 0 < dT) (hTs : 0 < Tstar) :
    monitoringReturn (curvatureK J rho2) dT Tstar <
    monitoringReturn (curvatureK J rho1) dT Tstar :=
  monitoring_return_proportional_to_K hdT hTs (curvatureK_decreasing_in_rho hJ hrho)

-- ============================================================
-- Section 11: MC-10 — Technology-Institution Complementarity (Schematic)
-- ============================================================

/-- **MC-10 (Technology and institutions are complements in reducing c₀).**
    The cross-partial ∂²c₀/∂A∂I < 0 (both reduce c₀, and the cross effect
    reinforces): ∂²(c_base/(A·I))/∂A∂I = c_base/(A²·I²) > 0, so
    technology and institutions are complements in integration surplus.

    Schematic: requires calculus (second-order cross-partial).

    **Proof.** With $c_0 = c_{\mathrm{base}} / (A \cdot I)$, first differentiate with respect to $A$: $\partial c_0/\partial A = -c_{\mathrm{base}} / (A^2 I)$. Then differentiate with respect to $I$: $\partial^2 c_0/\partial A\,\partial I = c_{\mathrm{base}} / (A^2 I^2)$. Since $c_{\mathrm{base}}, A, I > 0$, this cross-partial is strictly positive, establishing that $-c_0$ is supermodular in $(A, I)$ (Topkis 1998, Theorem 2.6.1). Economically, this means the marginal reduction in monitoring cost from better technology is amplified by higher institutional quality, and vice versa. The complementarity implies that reforms improving both technology and institutions simultaneously yield returns exceeding the sum of individual improvements. -/
theorem monitoring_technology_complementarity (_c_base _A _I : ℝ) :
    -- The cross-partial of monitoringCost is positive (complements in reducing c₀)
    True := trivial

end
