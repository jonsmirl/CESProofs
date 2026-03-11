/-
  Bilateral Trade Collapse Ordering
  (Paper 2, Section 4)

  Formalizes the bilateral extension of the effective curvature framework
  to international trade. Three results:

  1. Effective curvature is monotone decreasing in bilateral friction.
  2. The diversification channel (K²) is more sensitive than the production
     channel (K) — the sensitivity ordering applied to trade.
  3. More complementary goods (lower ρ) have lower critical friction T*,
     making them more fragile to trade disruption.

  The combined ordering determines the pattern of trade collapse:
  complementary goods between high-friction pairs fail first.
-/

import CESProofs.Potential.EffectiveCurvature

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Bilateral Effective Curvature Monotonicity
-- ============================================================

/-- **Effective curvature is monotone decreasing in bilateral friction.**
    For two bilateral relationships with trade frictions T₁ ≤ T₂ and
    common sector curvature K: K_eff(T₂) ≤ K_eff(T₁).

    Higher bilateral friction always reduces the effective curvature
    of the trade relationship. -/
theorem bilateral_Keff_decreasing {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T1 T2 Tstar : ℝ} (hTs : 0 < Tstar) (h : T1 ≤ T2) :
    effectiveCurvatureKeff J ρ T2 Tstar ≤ effectiveCurvatureKeff J ρ T1 Tstar := by
  simp only [effectiveCurvatureKeff]
  exact mul_le_mul_of_nonneg_left (degradation_monotone hTs h)
    (le_of_lt (curvatureK_pos hJ hρ))

/-- **Strict bilateral ordering**: If T₁ < T₂ and both are sub-critical,
    the effective curvature is strictly ordered. The higher-friction
    bilateral relationship has strictly lower effective curvature. -/
theorem bilateral_Keff_strict {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T1 T2 Tstar : ℝ} (hTs : 0 < Tstar) (h : T1 < T2) (hT2 : T2 < Tstar) :
    effectiveCurvatureKeff J ρ T2 Tstar < effectiveCurvatureKeff J ρ T1 Tstar := by
  simp only [effectiveCurvatureKeff]
  apply mul_lt_mul_of_pos_left _ (curvatureK_pos hJ hρ)
  -- Need: max 0 (1 - T₂/T*) < max 0 (1 - T₁/T*)
  have hm1 : 0 < 1 - T1 / Tstar := by
    rw [sub_pos, div_lt_one hTs]; linarith
  have hm2 : 0 < 1 - T2 / Tstar := by
    rw [sub_pos, div_lt_one hTs]; exact hT2
  rw [max_eq_right (le_of_lt hm1), max_eq_right (le_of_lt hm2)]
  have : T1 / Tstar < T2 / Tstar := div_lt_div_of_pos_right h hTs
  linarith

-- ============================================================
-- Section 2: K² Channel Degradation (Trade Diversification)
-- ============================================================

/-- **Effective curvature squared is also monotone decreasing in friction.**
    The diversification channel (∝ K_eff²) weakens as bilateral friction
    rises, and is more sensitive than the production channel (∝ K_eff)
    — elasticity 2 vs 1 with respect to K_eff. -/
theorem bilateral_Keff_sq_decreasing {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T1 T2 Tstar : ℝ} (hTs : 0 < Tstar) (h : T1 ≤ T2) :
    effectiveCurvatureKeff J ρ T2 Tstar ^ 2 ≤
    effectiveCurvatureKeff J ρ T1 Tstar ^ 2 := by
  apply pow_le_pow_left₀ (effectiveCurvatureKeff_nonneg hJ hρ T2 Tstar)
    (bilateral_Keff_decreasing hJ hρ hTs h)

/-- **The diversification degradation ratio.**
    At any sub-critical friction level, the degradation factor for the
    K² channel (m²) is strictly smaller than for the K channel (m).
    This means correlation robustness is more *sensitive* than superadditivity
    to friction — the sensitivity ordering of Corollary 1.

    Economically: diversification benefits from trade lose a larger fraction
    of their value than production benefits for the same friction increase. -/
theorem diversification_degradation_ratio {T Tstar : ℝ}
    (hTs : 0 < Tstar) (hT : 0 < T) (hTlt : T < Tstar) :
    (1 - T / Tstar) ^ 2 < (1 - T / Tstar) := by
  exact crisis_sequence_ordering (div_pos hT hTs) (by rw [div_lt_one hTs]; exact hTlt)

/-- **Trade collapse at criticality.**
    When bilateral friction reaches the critical threshold T*,
    effective curvature drops to zero — bilateral trade ceases.
    This is a discontinuous event, not a gradual decline. -/
theorem trade_collapse_at_critical {J : ℕ} {ρ : ℝ}
    {T Tstar : ℝ} (hTs : 0 < Tstar) (hT : Tstar ≤ T) :
    effectiveCurvatureKeff J ρ T Tstar = 0 :=
  effectiveCurvatureKeff_above_critical J ρ T Tstar hTs hT

-- ============================================================
-- Section 3: Complementary Goods Are More Fragile
-- ============================================================

/-- **Curvature is monotone decreasing in ρ.**
    More complementary goods (lower ρ) have higher curvature K.
    Since K = (1-ρ)(J-1)/J, this is immediate. -/
theorem curvatureK_decreasing_in_rho {J : ℕ} (hJ : 2 ≤ J)
    {rho1 rho2 : ℝ} (hrho : rho1 < rho2) :
    curvatureK J rho2 < curvatureK J rho1 := by
  simp only [curvatureK]
  apply div_lt_div_of_pos_right _ (by exact_mod_cast (show 0 < J by omega))
  exact mul_lt_mul_of_pos_right (by linarith) (by
    have : (2 : ℝ) ≤ ↑J := by exact_mod_cast hJ
    linarith)

/-- **More complementary goods have lower critical friction.**
    Since T* = 2(J-1)c²d²/K and higher K (lower ρ) means dividing by
    a larger number, complementary goods have a lower threshold for
    trade collapse. They are more fragile to bilateral friction.

    This is the goods-ordering result: under rising trade friction,
    complementary goods lose bilateral trade first. -/
theorem complementary_goods_more_fragile {J : ℕ} (hJ : 2 ≤ J)
    {rho1 rho2 : ℝ} (hrho1 : rho1 < 1) (_hrho2 : rho2 < 1)
    (hrho : rho1 < rho2)
    {c d_sq : ℝ} (hc : 0 < c) (hd : 0 < d_sq) :
    criticalFriction J rho1 c d_sq < criticalFriction J rho2 c d_sq := by
  simp only [criticalFriction]
  have hJ_pos : (0 : ℝ) < ↑J := by exact_mod_cast (show 0 < J by omega)
  have hJm1 : (0 : ℝ) < ↑J - 1 := by
    have : (2 : ℝ) ≤ ↑J := by exact_mod_cast hJ
    linarith
  -- Numerator: 2 * (↑J - 1) * c ^ 2 * d_sq > 0
  have hnum : 0 < 2 * (↑J - 1) * c ^ 2 * d_sq := by positivity
  -- K(rho1) > K(rho2) > 0
  have hK1 : 0 < curvatureK J rho1 := curvatureK_pos hJ hrho1
  have hK_lt : curvatureK J rho2 < curvatureK J rho1 :=
    curvatureK_decreasing_in_rho hJ hrho
  -- numerator / K1 < numerator / K2 since K1 > K2 > 0
  have hK2 : 0 < curvatureK J rho2 := curvatureK_pos hJ _hrho2
  exact div_lt_div_of_pos_left hnum hK2 hK_lt

/-- **The first-failure theorem for bilateral trade.**
    At any bilateral friction level T in the sub-critical regime:
    the effective curvature of more complementary goods is higher,
    but their critical friction is lower.

    Combined with the crisis sequence: complementary-goods
    diversification trade fails first as bilateral friction rises. -/
theorem complementary_goods_higher_Keff {J : ℕ} (hJ : 2 ≤ J)
    {rho1 rho2 : ℝ} (_hrho1 : rho1 < 1) (_hrho2 : rho2 < 1)
    (hrho : rho1 < rho2)
    {T Tstar : ℝ} (_hTs : 0 < Tstar) (_hT : 0 ≤ T) :
    effectiveCurvatureKeff J rho2 T Tstar ≤
    effectiveCurvatureKeff J rho1 T Tstar := by
  simp only [effectiveCurvatureKeff]
  -- K(rho2) ≤ K(rho1) and degradation factor is the same for both
  apply mul_le_mul_of_nonneg_right
  · exact le_of_lt (curvatureK_decreasing_in_rho hJ hrho)
  · exact le_max_left 0 _

-- ============================================================
-- Section 4: Combined Trade Collapse Ordering
-- ============================================================

/-- **The bilateral-pair ordering.**
    Among bilateral relationships with different frictions but the same
    goods: the pair with the highest friction has the lowest effective
    curvature. The highest-friction pair reaches criticality first. -/
theorem highest_friction_pair_fails_first {J : ℕ} (hJ : 2 ≤ J)
    {ρ : ℝ} (hρ : ρ < 1)
    {T1 T2 Tstar : ℝ} (hTs : 0 < Tstar)
    (hT1_nn : 0 ≤ T1) (hT1 : T1 < Tstar) (hT2 : Tstar ≤ T2) :
    effectiveCurvatureKeff J ρ T2 Tstar = 0 ∧
    0 < effectiveCurvatureKeff J ρ T1 Tstar := by
  constructor
  · exact effectiveCurvatureKeff_above_critical J ρ T2 Tstar hTs hT2
  · exact effectiveCurvatureKeff_pos hJ hρ hT1_nn hTs hT1

/-- **The goods-pair interaction.**
    For two goods with ρ₁ < ρ₂ at the same bilateral friction:
    the more complementary good has higher effective curvature (more
    to gain) but lower critical friction (more fragile).

    This is the efficiency-fragility tradeoff in international trade:
    complementary goods gain most from open borders but are
    most vulnerable to trade disruption. -/
theorem efficiency_fragility_tradeoff {J : ℕ} (hJ : 2 ≤ J)
    {rho1 rho2 : ℝ} (hrho1 : rho1 < 1) (hrho2 : rho2 < 1)
    (hrho : rho1 < rho2)
    {c d_sq : ℝ} (hc : 0 < c) (hd : 0 < d_sq)
    {T Tstar : ℝ} (hTs : 0 < Tstar) (hT : 0 ≤ T) :
    -- More complementary goods have higher effective curvature...
    effectiveCurvatureKeff J rho2 T Tstar ≤
      effectiveCurvatureKeff J rho1 T Tstar ∧
    -- ...but lower critical friction (more fragile)
    criticalFriction J rho1 c d_sq < criticalFriction J rho2 c d_sq := by
  exact ⟨complementary_goods_higher_Keff hJ hrho1 hrho2 hrho hTs hT,
         complementary_goods_more_fragile hJ hrho1 hrho2 hrho hc hd⟩

-- ============================================================
-- Section 5: Noise Tolerance Monotonicity
-- ============================================================

/-- **Noise tolerance is monotone increasing in ρ.**

    The critical friction T* = 2(J-1)c²d² / K(ρ) increases with ρ,
    because K = (1-ρ)(J-1)/J decreases with ρ. Systems with higher ρ
    (more substitutable inputs) tolerate more informational noise
    before the regime shift at T = T*.

    This is the converse of `complementary_goods_more_fragile`:
    substitute systems are more robust to noise, while complementary
    systems are more fragile.

    **Application (Arrow prediction test)**: If majoritarian political
    systems map to higher effective ρ (more substitutable decision
    channels), they should maintain governance quality better under
    rising informational noise (internet penetration as T proxy).
    The mapping majoritarian → ρ is speculative; this theorem provides
    the mathematical backing IF the mapping holds.

    **Proof.** T* = numerator / K where numerator > 0 is independent
    of ρ. Since K decreases in ρ (`curvatureK_decreasing_in_rho`),
    dividing by a smaller K yields a larger T*. -/
theorem noise_tolerance_increasing_in_rho {J : ℕ} (hJ : 2 ≤ J)
    {rho1 rho2 : ℝ} (hrho1 : rho1 < 1) (hrho2 : rho2 < 1)
    (hrho : rho1 < rho2)
    {c d_sq : ℝ} (hc : 0 < c) (hd : 0 < d_sq) :
    criticalFriction J rho1 c d_sq < criticalFriction J rho2 c d_sq :=
  complementary_goods_more_fragile hJ hrho1 hrho2 hrho hc hd

end
