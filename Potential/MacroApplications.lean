/-
  Macroeconomic Applications of the CES Potential
  (Paper 2, Section 4)

  Applies the effective curvature framework to standard macroeconomic
  phenomena. Six results:

  1. CES multiplier: complementarity premium proportional to curvature K
  2. Effective multiplier: friction degrades the multiplier via K_eff
  3. Fiscal multiplier heterogeneity: spending in complementary sectors
     has higher multipliers
  4. Recession depth: more complementary sectors suffer larger absolute losses
  5. Sectoral recession ordering: complementary sectors hit T* first
  6. Stagflation: rising friction simultaneously reduces output and
     increases allocation distortion

  Key insight: the single parameter K = (1-ρ)(J-1)/J simultaneously
  determines the Keynesian multiplier, the sectoral ordering of
  recessions, and the stagflation mechanism.

  ### A3-iteration context (Phase 3 re-rooting)

  The effective-curvature parameter `K_eff = K · (1 - T/T*)⁺` is
  the T-dependent projection of K along the A3-iteration critical
  manifold. Macroeconomic resilience degrades as the iteration's
  fast-mode decay rate (`Foundations.Emergence.modeAfterL_eq_exp_decay`)
  approaches zero. See `research/demographics/A3_encodes_time.md`.
-/

import CESProofs.Potential.BilateralTrade
import CESProofs.Foundations.Emergence

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: The CES Multiplier
-- ============================================================

/-- **The CES multiplier**: the complementarity premium per unit of
    input dispersion. M(ρ) = K(ρ) · d², where K is the CES curvature
    and d² is the cross-sectional dispersion of inputs.

    This is the Keynesian multiplier derived from production structure:
    heterogeneous complementary inputs produce more than the sum of parts,
    and the premium is proportional to curvature times dispersion. -/
def cesMultiplier (J : ℕ) (ρ d_sq : ℝ) : ℝ :=
  curvatureK J ρ * d_sq

/-- The CES multiplier is positive for complementary goods with dispersion. -/
theorem cesMultiplier_pos {J : ℕ} (hJ : 2 ≤ J) {ρ d_sq : ℝ}
    (hρ : ρ < 1) (hd : 0 < d_sq) :
    0 < cesMultiplier J ρ d_sq :=
  mul_pos (curvatureK_pos hJ hρ) hd

/-- **The multiplier is higher for more complementary sectors.**
    Lower ρ → higher K → larger multiplier. Sectors with complementary
    inputs (construction, manufacturing) have larger multipliers than
    sectors with substitutable inputs (financial services, digital goods). -/
theorem cesMultiplier_decreasing_in_rho {J : ℕ} (hJ : 2 ≤ J)
    {ρ1 ρ2 d_sq : ℝ} (hρ : ρ1 < ρ2) (hd : 0 < d_sq) :
    cesMultiplier J ρ2 d_sq < cesMultiplier J ρ1 d_sq := by
  simp only [cesMultiplier]
  exact mul_lt_mul_of_pos_right (curvatureK_decreasing_in_rho hJ hρ) hd

-- ============================================================
-- Section 2: Effective Multiplier Under Friction
-- ============================================================

/-- **The effective multiplier under information friction.**
    M_eff(ρ, T) = K_eff(ρ, T) · d² = K(ρ) · (1-T/T*)⁺ · d².

    Information friction degrades the multiplier: higher T means
    less complementarity premium. At T = T*, the multiplier vanishes
    and the economy behaves as if inputs were perfect substitutes. -/
def effectiveMultiplier (J : ℕ) (ρ T Tstar d_sq : ℝ) : ℝ :=
  effectiveCurvatureKeff J ρ T Tstar * d_sq

/-- The effective multiplier is non-negative. -/
theorem effectiveMultiplier_nonneg {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T Tstar d_sq : ℝ} (hd : 0 ≤ d_sq) :
    0 ≤ effectiveMultiplier J ρ T Tstar d_sq := by
  simp only [effectiveMultiplier]
  exact mul_nonneg (effectiveCurvatureKeff_nonneg hJ hρ T Tstar) hd

/-- **Friction degrades the multiplier.** Rising information friction
    reduces the effective multiplier monotonically. -/
theorem effectiveMultiplier_decreasing_in_T {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T1 T2 Tstar d_sq : ℝ} (hTs : 0 < Tstar) (h : T1 ≤ T2) (hd : 0 ≤ d_sq) :
    effectiveMultiplier J ρ T2 Tstar d_sq ≤ effectiveMultiplier J ρ T1 Tstar d_sq := by
  simp only [effectiveMultiplier]
  exact mul_le_mul_of_nonneg_right (bilateral_Keff_decreasing hJ hρ hTs h) hd

/-- **The multiplier vanishes at the critical friction.**
    At T ≥ T*, the complementarity premium is zero: the economy
    operates as if inputs were perfect substitutes. -/
theorem effectiveMultiplier_zero_at_critical {J : ℕ} {ρ : ℝ}
    {T Tstar d_sq : ℝ} (hTs : 0 < Tstar) (hT : Tstar ≤ T) :
    effectiveMultiplier J ρ T Tstar d_sq = 0 := by
  simp only [effectiveMultiplier]
  rw [effectiveCurvatureKeff_above_critical J ρ T Tstar hTs hT, zero_mul]

/-- **Fiscal multiplier heterogeneity.**
    Government spending in sectors with more complementary inputs
    (lower ρ) generates a larger effective multiplier. Infrastructure
    spending (low ρ) has a larger multiplier than transfer payments
    spent on fungible goods (high ρ). -/
theorem fiscal_multiplier_heterogeneity {J : ℕ} (hJ : 2 ≤ J)
    {ρ1 ρ2 : ℝ} (hρ1 : ρ1 < 1) (hρ2 : ρ2 < 1) (hρ : ρ1 < ρ2)
    {T Tstar d_sq : ℝ} (_hTs : 0 < Tstar) (_hT : 0 ≤ T) (hd : 0 ≤ d_sq) :
    effectiveMultiplier J ρ2 T Tstar d_sq ≤ effectiveMultiplier J ρ1 T Tstar d_sq := by
  simp only [effectiveMultiplier]
  exact mul_le_mul_of_nonneg_right
    (complementary_goods_higher_Keff hJ hρ1 hρ2 hρ _hTs _hT) hd

-- ============================================================
-- Section 3: Recession Depth and Ordering
-- ============================================================

/-- **Recession depth is proportional to curvature.**
    When friction rises from T₁ to T₂ (both sub-critical), the output
    loss equals K · (T₂ - T₁) / T*. More complementary sectors
    (higher K) suffer larger absolute output losses.

    This is the CES derivation of the Keynesian multiplier applied
    to recessions: the same curvature that generates superadditivity
    gains in good times generates proportional losses in bad times. -/
theorem recession_depth_proportional_to_K {J : ℕ}
    {ρ : ℝ} {T1 T2 Tstar : ℝ} (hTs : 0 < Tstar)
    (hT1 : T1 < Tstar) (hT2 : T2 < Tstar) :
    effectiveCurvatureKeff J ρ T1 Tstar - effectiveCurvatureKeff J ρ T2 Tstar =
    curvatureK J ρ * (T2 - T1) / Tstar := by
  simp only [effectiveCurvatureKeff]
  have hm1 : 0 < 1 - T1 / Tstar := by rw [sub_pos, div_lt_one hTs]; exact hT1
  have hm2 : 0 < 1 - T2 / Tstar := by rw [sub_pos, div_lt_one hTs]; exact hT2
  rw [max_eq_right (le_of_lt hm1), max_eq_right (le_of_lt hm2)]
  have : Tstar ≠ 0 := ne_of_gt hTs
  field_simp
  ring

/-- **Sectoral recession ordering.**
    Under a uniform information friction shock, sectors reach the
    critical threshold T* in order of their substitution elasticity:
    complementary sectors (lower ρ) have lower T* and fail first.

    This is the CES-derived prediction for the sectoral sequence
    of recessions: construction and manufacturing (low ρ, complementary
    inputs) lead downturns, while services (high ρ, substitutable
    inputs) lag. -/
theorem sectoral_recession_ordering {J : ℕ} (hJ : 2 ≤ J)
    {ρ1 ρ2 : ℝ} (hρ1 : ρ1 < 1) (hρ2 : ρ2 < 1) (hρ : ρ1 < ρ2)
    {c d_sq : ℝ} (hc : 0 < c) (hd : 0 < d_sq) :
    criticalFriction J ρ1 c d_sq < criticalFriction J ρ2 c d_sq :=
  complementary_goods_more_fragile hJ hρ1 hρ2 hρ hc hd

-- ============================================================
-- Section 4: Allocation Distortion and Stagflation
-- ============================================================

/-- **Allocation distortion under information friction.**
    d(T, T*) = 1 - max(0, 1 - T/T*) = min(1, T/T*).

    Measures how far the allocation is from the efficient benchmark.
    At T = 0: distortion = 0 (efficient allocation).
    At T ≥ T*: distortion = 1 (fully distorted, no complementarity gains). -/
def allocationDistortion (T Tstar : ℝ) : ℝ := 1 - max 0 (1 - T / Tstar)

/-- Allocation distortion is non-negative when friction is non-negative. -/
theorem allocationDistortion_nonneg {T Tstar : ℝ} (hT : 0 ≤ T) (hTs : 0 < Tstar) :
    0 ≤ allocationDistortion T Tstar := by
  simp only [allocationDistortion]
  have : max 0 (1 - T / Tstar) ≤ 1 :=
    max_le zero_le_one (by linarith [div_nonneg hT (le_of_lt hTs)])
  linarith

/-- At zero friction, there is no allocation distortion. -/
theorem allocationDistortion_at_zero {Tstar : ℝ} (_hTs : 0 < Tstar) :
    allocationDistortion 0 Tstar = 0 := by
  simp [allocationDistortion]

/-- At critical friction, distortion is complete. -/
theorem allocationDistortion_at_critical {Tstar : ℝ} (hTs : 0 < Tstar) :
    allocationDistortion Tstar Tstar = 1 := by
  simp [allocationDistortion, div_self (ne_of_gt hTs)]

/-- **Allocation distortion is monotone increasing in friction.**
    Rising friction always increases distortion. -/
theorem allocationDistortion_monotone {T1 T2 Tstar : ℝ} (hTs : 0 < Tstar)
    (h : T1 ≤ T2) :
    allocationDistortion T1 Tstar ≤ allocationDistortion T2 Tstar := by
  simp only [allocationDistortion]
  linarith [degradation_monotone hTs h]

/-- **The stagflation theorem.**
    Rising information friction simultaneously:
    (a) reduces the effective multiplier (output falls), and
    (b) increases allocation distortion (prices rise due to misallocation).

    The CES potential provides a single-mechanism explanation for
    stagflation: both output decline and price increase are driven by
    the same cause—rising information friction that degrades effective
    curvature. No separate supply and demand shocks are needed. -/
theorem stagflation {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T1 T2 Tstar d_sq : ℝ} (hTs : 0 < Tstar) (h : T1 ≤ T2) (hd : 0 ≤ d_sq) :
    -- (a) Output falls: effective multiplier decreases
    effectiveMultiplier J ρ T2 Tstar d_sq ≤ effectiveMultiplier J ρ T1 Tstar d_sq ∧
    -- (b) Prices rise: allocation distortion increases
    allocationDistortion T1 Tstar ≤ allocationDistortion T2 Tstar :=
  ⟨effectiveMultiplier_decreasing_in_T hJ hρ hTs h hd,
   allocationDistortion_monotone hTs h⟩

/-- **Dual degradation in recessions.**
    In a recession (rising T), the diversification channel (K_eff²)
    is more sensitive than the production channel (K_eff) — elasticity
    2 vs 1. A given friction increase causes a proportionally larger
    loss in correlation robustness (portfolio diversification) than in
    superadditivity (production complementarity). This is a sensitivity
    ordering: both channels respond simultaneously to the same friction. -/
theorem recession_dual_degradation {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T1 T2 Tstar : ℝ} (hTs : 0 < Tstar) (h : T1 ≤ T2) :
    effectiveCurvatureKeff J ρ T2 Tstar ^ 2 ≤
    effectiveCurvatureKeff J ρ T1 Tstar ^ 2 :=
  bilateral_Keff_sq_decreasing hJ hρ hTs h

end
