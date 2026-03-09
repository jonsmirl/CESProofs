/-
  Institutional Reform Equivalence, Adjustment Timescale, and Fragility Ordering
  (Paper 4, Section 10)

  Three propositions extending the damping cancellation and upstream reform principle:
  1. Reform equivalence: the two reform channels have unit elasticity and are
     perfectly substitutable.
  2. Institutional adjustment timescale: connects structural convergence speed
     (Paper 4) with pre-crisis deceleration (Paper 2).
  3. Fragility ordering: the level with smallest critical friction fails first,
     regardless of its position in the timescale hierarchy.

  Key insight: structural regulation cancels (damping cancellation);
  institutional degradation does not.

  Imports from Paper 4 (welfare contribution, damping cancellation) and
  Paper 2 (adjustment timescale, effective curvature).
-/

import CESProofs.Hierarchy.Defs
import CESProofs.Potential.EffectiveCurvature

open Real Finset BigOperators

noncomputable section

variable {N : ℕ}

-- ============================================================
-- Section 1: Reform Equivalence (Scaling Properties)
-- ============================================================

/-- **Reform scaling (upstream depreciation)**: The welfare contribution
    V_n = σ_{n-1} · δ² / β_n is linear in upstream depreciation.
    Rescaling σ_{n-1} by factor λ rescales V_n by λ.

    This is part (i) of the Reform Equivalence proposition. -/
theorem reform_scaling_sigma {sigma_prev delta beta_n lambda : ℝ} :
    welfareContribution (lambda * sigma_prev) delta beta_n =
    lambda * welfareContribution sigma_prev delta beta_n := by
  simp only [welfareContribution]
  rw [mul_assoc, mul_div_assoc]

/-- **Reform scaling (gain elasticity)**: The welfare contribution is
    inverse-linear in gain elasticity. Rescaling β_n by factor λ
    rescales V_n by 1/λ.

    This is part (ii) of the Reform Equivalence proposition. -/
theorem reform_scaling_beta {sigma_prev delta beta_n lambda : ℝ}
    (hl : lambda ≠ 0) (hb : beta_n ≠ 0) :
    welfareContribution sigma_prev delta (lambda * beta_n) =
    (1 / lambda) * welfareContribution sigma_prev delta beta_n := by
  simp only [welfareContribution]
  field_simp

/-- **Reform substitutability**: Doubling gain elasticity has exactly
    the same welfare effect as halving upstream depreciation.
    The two reform channels have a precise exchange rate.

    Corollary of the two scaling theorems: V(σ/2, δ, β) = V(σ, δ, 2β). -/
theorem reform_substitutability {sigma_prev delta beta_n : ℝ} (hb : beta_n ≠ 0) :
    welfareContribution (sigma_prev / 2) delta beta_n =
    welfareContribution sigma_prev delta (2 * beta_n) := by
  simp only [welfareContribution]
  field_simp

-- ============================================================
-- Section 2: Institutional Margin and Adjustment Timescale
-- ============================================================

/-- The institutional margin: m = max(0, 1 - T/T*).
    Measures the distance from the regime boundary.
    At m = 1: full institutional quality (T = 0).
    At m = 0: criticality (T = T*).
    Connects to effectiveCurvatureKeff via K_eff = K · m. -/
def institutionalMargin (T Tstar : ℝ) : ℝ := max 0 (1 - T / Tstar)

/-- The institutional margin is non-negative. -/
theorem institutionalMargin_nonneg {T Tstar : ℝ} :
    0 ≤ institutionalMargin T Tstar :=
  le_max_left 0 _

/-- At zero friction, the institutional margin is 1 (full quality). -/
theorem institutionalMargin_at_zero {Tstar : ℝ} (_hTs : 0 < Tstar) :
    institutionalMargin 0 Tstar = 1 := by
  simp [institutionalMargin]

/-- At critical friction, the institutional margin is 0. -/
theorem institutionalMargin_at_critical {Tstar : ℝ} (hTs : 0 < Tstar) :
    institutionalMargin Tstar Tstar = 0 := by
  simp [institutionalMargin, div_self (ne_of_gt hTs)]

/-- The institutional adjustment timescale: τ = ε/(σ·m).
    Combines structural convergence speed (σ/ε from Paper 4, Proposition 6)
    with institutional quality (m from Paper 2, Theorem 4).

    When m = 1 (no friction): τ = ε/σ (base timescale).
    As m → 0 (approaching criticality): τ diverges (pre-crisis deceleration). -/
def institutionalAdjustmentTime (eps sigma margin : ℝ) : ℝ :=
  eps / (sigma * margin)

/-- **Connection to Paper 2's adjustment timescale.**
    With base timescale τ₀ = ε/σ and margin m = 1 - T/T*:
    the institutional adjustment timescale equals Paper 2's formula.

    This bridges the structural model (Paper 4) with the information
    friction model (Paper 2). -/
theorem adjustmentTimescale_connection {eps sigma T Tstar : ℝ} :
    institutionalAdjustmentTime eps sigma (1 - T / Tstar) =
    adjustmentTimescale (eps / sigma) T Tstar := by
  simp only [institutionalAdjustmentTime, adjustmentTimescale]
  rw [div_div]

/-- Institutional adjustment timescale is positive for sub-critical levels. -/
theorem institutionalAdjustmentTime_pos {eps sigma margin : ℝ}
    (heps : 0 < eps) (hsigma : 0 < sigma) (hm : 0 < margin) :
    0 < institutionalAdjustmentTime eps sigma margin :=
  div_pos heps (mul_pos hsigma hm)

/-- **Institutional adjustment timescale is decreasing in the margin.**
    A larger margin (further from the regime boundary) gives a shorter
    timescale (faster adjustment). As the margin shrinks toward zero,
    the timescale diverges—this is pre-crisis deceleration applied
    at each level of the hierarchy. -/
theorem inst_adjustment_decreasing_margin {eps sigma m1 m2 : ℝ}
    (heps : 0 < eps) (hsigma : 0 < sigma) (hm1 : 0 < m1) (_hm2 : 0 < m2)
    (hm : m1 < m2) :
    institutionalAdjustmentTime eps sigma m2 <
    institutionalAdjustmentTime eps sigma m1 := by
  simp only [institutionalAdjustmentTime]
  exact div_lt_div_of_pos_left heps (mul_pos hsigma hm1)
    (mul_lt_mul_of_pos_left hm hsigma)

-- ============================================================
-- Section 3: Effective Welfare Contribution Under Friction
-- ============================================================

/-- **Effective welfare contribution under information friction.**
    V_{n,eff} = σ_{n-1} · δ² / (β_n · m_n).

    When the institutional margin m_n < 1, the effective gain elasticity
    is β_{n,eff} = β_n · m_n, increasing the welfare cost of deviations.
    As m_n → 0, the effective welfare cost diverges: any perturbation
    near the regime boundary has unbounded welfare impact.

    This contrasts with the damping cancellation (DampingCancellation.lean):
    structural regulation σ_n cancels in welfare, but the institutional
    margin m_n does NOT cancel. -/
def effectiveWelfareContribution (sigma_prev delta beta_n margin : ℝ) : ℝ :=
  sigma_prev * delta ^ 2 / (beta_n * margin)

/-- **At full institutional quality (m = 1), effective welfare equals
    standard welfare.** The effective welfare contribution reduces to the
    ordinary welfare contribution when there is no information friction. -/
theorem eff_welfare_at_full_margin {sigma_prev delta beta_n : ℝ} :
    effectiveWelfareContribution sigma_prev delta beta_n 1 =
    welfareContribution sigma_prev delta beta_n := by
  simp only [effectiveWelfareContribution, welfareContribution, mul_one]

/-- **Effective welfare is strictly decreasing in the margin** (for
    nonzero deviation at a positive level). A larger margin means
    lower welfare loss—institutions matter.

    This is the fundamental asymmetry: structural regulation σ_n
    cancels in welfare (damping_cancellation_algebraic), but the
    institutional margin m_n does not.
    The regulator can freely adjust depreciation rates without net
    welfare cost, but institutional degradation (rising T, falling m)
    worsens welfare with no offsetting benefit. -/
theorem eff_welfare_decreasing_margin {sigma_prev delta beta_n m1 m2 : ℝ}
    (hs : 0 < sigma_prev) (hd : delta ≠ 0) (hb : 0 < beta_n)
    (hm1 : 0 < m1) (_hm2 : 0 < m2) (hm : m1 < m2) :
    effectiveWelfareContribution sigma_prev delta beta_n m2 <
    effectiveWelfareContribution sigma_prev delta beta_n m1 := by
  simp only [effectiveWelfareContribution]
  apply div_lt_div_of_pos_left
  · exact mul_pos hs (sq_pos_of_ne_zero hd)
  · exact mul_pos hb hm1
  · exact mul_lt_mul_of_pos_left hm hb

/-- **Effective welfare is non-negative** for positive inputs. -/
theorem eff_welfare_nonneg {sigma_prev delta beta_n margin : ℝ}
    (hs : 0 ≤ sigma_prev) (hb : 0 < beta_n) (hm : 0 < margin) :
    0 ≤ effectiveWelfareContribution sigma_prev delta beta_n margin := by
  simp only [effectiveWelfareContribution]
  apply div_nonneg
  · exact mul_nonneg hs (sq_nonneg _)
  · exact le_of_lt (mul_pos hb hm)

-- ============================================================
-- Section 4: Hierarchical Fragility Ordering
-- ============================================================

/-- **Fragility ordering (at criticality)**: If T*₁ < T*₂, then at the
    moment level 1 hits criticality (T = T*₁), level 2 is still
    sub-critical. The weaker institution fails first.

    This is part (i) of the Hierarchical Fragility Ordering proposition.
    Combined with the ceiling cascade (Activation.lean), failure at
    the weaker level propagates upward through the hierarchy. -/
theorem fragility_at_critical {Tstar1 Tstar2 : ℝ}
    (hTs1 : 0 < Tstar1) (_hTs2 : 0 < Tstar2) (h : Tstar1 < Tstar2) :
    institutionalMargin Tstar1 Tstar1 = 0 ∧
    0 < institutionalMargin Tstar1 Tstar2 := by
  constructor
  · -- At T = T*₁: margin₁ = max(0, 1 - 1) = 0
    simp [institutionalMargin, div_self (ne_of_gt hTs1)]
  · -- At T = T*₁: margin₂ = max(0, 1 - T*₁/T*₂) > 0 since T*₁ < T*₂
    simp only [institutionalMargin]
    apply lt_max_of_lt_right
    have hlt : Tstar1 / Tstar2 < 1 := by
      rw [div_lt_one (by linarith)]
      exact h
    linarith

/-- **Margin monotonicity in critical friction**: The level with the
    smaller critical friction T* always has the smaller institutional
    margin, regardless of the current friction level T.

    If T*₁ ≤ T*₂, then m(T, T*₁) ≤ m(T, T*₂) for all T ≥ 0.
    The institutionally weaker level is always closer to criticality.

    This determines the crisis ordering within the hierarchy: levels
    fail in order of their critical frictions, not in order of their
    timescales. -/
theorem margin_monotone_in_Tstar {T Tstar1 Tstar2 : ℝ}
    (hTs1 : 0 < Tstar1) (hTs2 : 0 < Tstar2) (h : Tstar1 ≤ Tstar2) (hT : 0 ≤ T) :
    institutionalMargin T Tstar1 ≤ institutionalMargin T Tstar2 := by
  simp only [institutionalMargin]
  apply max_le_max_left 0
  -- Goal: 1 - T / Tstar1 ≤ 1 - T / Tstar2
  -- Suffices: T / Tstar2 ≤ T / Tstar1
  suffices T / Tstar2 ≤ T / Tstar1 by linarith
  rw [div_le_div_iff₀ hTs2 hTs1]
  exact mul_le_mul_of_nonneg_left h hT

/-- **Strict fragility ordering**: If T*₁ < T*₂ and friction is positive,
    the margin gap is strict: level 1 is strictly closer to criticality. -/
theorem margin_strict_in_Tstar {T Tstar1 Tstar2 : ℝ}
    (hTs1 : 0 < Tstar1) (hTs2 : 0 < Tstar2)
    (h : Tstar1 < Tstar2) (hT : 0 < T)
    (hTlt : T < Tstar1) :
    institutionalMargin T Tstar1 < institutionalMargin T Tstar2 := by
  simp only [institutionalMargin]
  -- Both margins are positive (T < T*₁ < T*₂)
  have hm1 : 0 < 1 - T / Tstar1 := by
    rw [sub_pos, div_lt_one hTs1]; exact hTlt
  have hm2 : 0 < 1 - T / Tstar2 := by
    rw [sub_pos, div_lt_one hTs2]; linarith
  rw [max_eq_right (le_of_lt hm1), max_eq_right (le_of_lt hm2)]
  -- Goal: 1 - T / Tstar1 < 1 - T / Tstar2
  -- Suffices: T / Tstar2 < T / Tstar1
  suffices T / Tstar2 < T / Tstar1 by linarith
  rw [div_lt_div_iff₀ hTs2 hTs1]
  exact mul_lt_mul_of_pos_left h hT

end
