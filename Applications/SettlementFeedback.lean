/-
  Paper 7: Settlement Feedback and Monetary Policy in a Mesh Economy

  Formalizes the settlement reproduction number R₀^settle from the
  (φ,S) subsystem Jacobian, bank intermediation friction, the CBDC
  Acceleration Proposition, displacement dominance, monetary policy
  degradation, and dollarization threshold.

  Results (all 0 custom axioms):
  1. settlementR0_pos: R₀ > 0
  2. settlementR0Friction_eq: R₀(λ) = λ · R₀(1)  [key factorization]
  3. settlementR0Friction_one: R₀(1) = R₀         [consistency]
  4. cbdc_acceleration: λ < 1 → R₀(λ) < R₀(1)     [Proposition 6]
  5. transition_iff_det_sign: det(J) > 0 ↔ R₀ < 1  [stability criterion]
  6. cbdc_triggers_bifurcation: λ < 1, R₀(λ) < 1 < R₀(1) possible
  7. displacement_dominance: Corollary 2 (India calibration)
  8. friction_monotone: higher friction → lower R₀
  9. cbdc_acceleration_reinforced: both channels strengthen result
  10. mp_effectiveness_decreasing: FG(phi) monotonicity [Proposition 5]
  11. safety_zone_shrinking: c(phi) decreasing        [Proposition 4]
  12. triffinTime / triffin_time_pos: t_triffin > 0   [Corollary 1]
  13. dollarizationThreshold / threshold_decreasing    [Proposition 3]
  14. threshold_ratio_invariant: scale invariance
  15. fr_nonneg: FR ≥ 0
  16. fr_zero_above_critical: FR = 0 for S ≥ S_crit   [Definition 3]
  17. fr_below_critical: FR simplification for S < S_crit
  18. fr_decreasing: FR monotone decreasing in S
  19. fr_continuous: FR continuous everywhere incl. S_crit [resolves prop:mp]
  20. fr_hasDerivAt: HasDerivAt for FR when S < S_crit
  21. fr_deriv_diverges: |FR'| → ∞ as S → S_crit⁻ when α < 1  [the cusp]
  22. compositeMP_decreasing_S: MP decreasing in S    [prop:mp part ii]
  23. compositeMP_decreasing_phi: MP decreasing in φ  [prop:mp part i]
  24. compositeMP_continuous_S: MP continuous in S     [prop:mp part iii]
-/

import CESProofs.Hierarchy.Activation
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Order.Field

open Real Finset BigOperators Filter Topology

noncomputable section

-- ============================================================
-- Section 1: Settlement Economy Structure
-- ============================================================

/-- The (φ,S) subsystem Jacobian entries at the low-mesh steady state.

    The 4-ODE system (equations 5–8 of Paper 7) has state variables
    (φ, S, b, η). At the low-mesh steady state, the fast subsystem
    (φ, S) decouples from the slow variables (b, η) by timescale
    separation. The Jacobian of the (φ,S) subsystem has:
    - Positive off-diagonal entries (mutual reinforcement)
    - Negative diagonal entries (self-damping)

    We store the absolute values of the diagonal entries as `self_phi`
    and `self_S` (both positive) to avoid sign bookkeeping. -/
structure SettlementEconomy where
  /-- |∂f_φ/∂S| > 0: settlement infrastructure attracts mesh adoption.
      From eq. (5): ∂f_φ/∂S = γ_φ · φ(1-φ) · ∂μ_φ/∂S. -/
  cross_phi_S : ℝ
  h_cross_phi_S : 0 < cross_phi_S
  /-- |∂f_S/∂φ| > 0: mesh participation generates settlement demand.
      From eq. (6): ∂f_S/∂φ = γ_S · S · g'_mesh(φ). -/
  cross_S_phi : ℝ
  h_cross_S_phi : 0 < cross_S_phi
  /-- |∂f_φ/∂φ| > 0: logistic self-damping of mesh adoption.
      Negative eigenvalue contribution at stable equilibrium. -/
  self_phi : ℝ
  h_self_phi : 0 < self_phi
  /-- |∂f_S/∂S| > 0: stablecoin depreciation and attrition (δ_S).
      Negative eigenvalue contribution at stable equilibrium. -/
  self_S : ℝ
  h_self_S : 0 < self_S

-- ============================================================
-- Section 2: Settlement Reproduction Number
-- ============================================================

/-- **Definition 2 (Settlement Reproduction Number).**

    R₀^settle = (∂f_φ/∂S · ∂f_S/∂φ) / (|∂f_φ/∂φ| · |∂f_S/∂S|)

    This is the spectral radius of the next-generation matrix for
    the 2D (φ,S) subsystem. When R₀ > 1, the feedback loop is
    self-reinforcing: mesh growth → settlement demand → better
    infrastructure → more mesh adoption. -/
def settlementR0 (e : SettlementEconomy) : ℝ :=
  (e.cross_phi_S * e.cross_S_phi) / (e.self_phi * e.self_S)

/-- R₀ is strictly positive (positive cross-couplings, positive self-damping). -/
theorem settlementR0_pos (e : SettlementEconomy) : 0 < settlementR0 e :=
  div_pos (mul_pos e.h_cross_phi_S e.h_cross_S_phi)
          (mul_pos e.h_self_phi e.h_self_S)

-- ============================================================
-- Section 3: Bank Intermediation Friction
-- ============================================================

/-- R₀ with bank intermediation friction λ_B ∈ (0,1] attenuating
    the φ→S channel.

    In the status quo, mesh-generated capital flows reach the
    stablecoin ecosystem through bank intermediaries who impose
    compliance costs, settlement delays, and capital requirements.
    The effective coupling is λ_B · (∂f_S/∂φ), where λ_B < 1.

    A CBDC provides direct central bank liabilities on digital
    devices, bypassing bank intermediation: λ_B → 1. -/
def settlementR0Friction (e : SettlementEconomy) (lambda_B : ℝ) : ℝ :=
  (e.cross_phi_S * (lambda_B * e.cross_S_phi)) / (e.self_phi * e.self_S)

/-- **Key factorization**: R₀(λ) = λ · R₀(1).

    Bank friction enters the numerator of R₀ linearly (through
    the φ→S channel only) and does not affect the denominator
    (self-damping rates are intrinsic to each variable). -/
theorem settlementR0Friction_eq (e : SettlementEconomy) (lambda_B : ℝ) :
    settlementR0Friction e lambda_B = lambda_B * settlementR0 e := by
  simp only [settlementR0Friction, settlementR0]
  ring

/-- Consistency: R₀ at full coupling (λ = 1) equals the base R₀. -/
theorem settlementR0Friction_one (e : SettlementEconomy) :
    settlementR0Friction e 1 = settlementR0 e := by
  rw [settlementR0Friction_eq]; ring

-- ============================================================
-- Section 4: CBDC Acceleration — Proposition 6
-- ============================================================

/-- **Proposition 6 (CBDC Acceleration).**

    Let R₀^CBDC denote the settlement reproduction number when bank
    intermediation friction is eliminated (λ_B = 1), and R₀^SQ
    denote the status quo reproduction number (λ_B < 1). Then:

      R₀^CBDC > R₀^SQ

    The CBDC accelerates rather than prevents the settlement feedback.

    **Proof.** By the factorization R₀(λ) = λ · R₀(1), the status quo
    R₀ is a fraction λ_B < 1 of the frictionless R₀. Since R₀(1) > 0:

      R₀^SQ = λ_B · R₀(1) < 1 · R₀(1) = R₀^CBDC.  □

    Two reinforcing channels (not modeled here) strengthen the
    inequality: (i) the CBDC validates digital settlement, increasing
    ∂μ_φ/∂S (the S→φ cross-coupling), and (ii) the CBDC reduces
    stablecoin attrition δ_S, making ∂f_S/∂S less negative. -/
theorem cbdc_acceleration (e : SettlementEconomy) {lambda_B : ℝ}
    (_hlambda_pos : 0 < lambda_B) (hlambda_lt : lambda_B < 1) :
    settlementR0Friction e lambda_B < settlementR0 e := by
  rw [settlementR0Friction_eq]
  exact mul_lt_of_lt_one_left (settlementR0_pos e) hlambda_lt

/-- R₀ is monotonically increasing in the coupling parameter λ_B.
    More bank friction (lower λ_B) means lower R₀. -/
theorem friction_monotone (e : SettlementEconomy) {lambda_1 lambda_2 : ℝ}
    (_h1 : 0 < lambda_1) (_h2 : 0 < lambda_2) (hle : lambda_1 ≤ lambda_2) :
    settlementR0Friction e lambda_1 ≤ settlementR0Friction e lambda_2 := by
  simp only [settlementR0Friction]
  apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos e.h_self_phi e.h_self_S))
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul_of_nonneg_right hle (le_of_lt e.h_cross_S_phi)
  · exact le_of_lt e.h_cross_phi_S

-- ============================================================
-- Section 5: Transition Condition
-- ============================================================

/-- **Transition condition.** The low-mesh equilibrium is stable
    iff det(J_{φ,S}) > 0, which is equivalent to R₀ < 1.

    det(J) = (-self_φ)(-self_S) - cross_φS · cross_Sφ
           = self_φ · self_S · (1 - R₀)

    So det(J) > 0 ⟺ 1 - R₀ > 0 ⟺ R₀ < 1. -/
theorem transition_iff_det_sign (e : SettlementEconomy) :
    0 < e.self_phi * e.self_S - e.cross_phi_S * e.cross_S_phi ↔
    settlementR0 e < 1 := by
  simp only [settlementR0]
  rw [div_lt_one (mul_pos e.h_self_phi e.h_self_S)]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **CBDC can trigger the bifurcation.** If R₀(1) > 1 but R₀(λ) < 1,
    the economy is stable under bank intermediation but unstable
    once the CBDC removes friction. The bifurcation is triggered
    by financial infrastructure modernization, not by a technology
    shock. -/
theorem cbdc_triggers_bifurcation (e : SettlementEconomy) {lambda_B : ℝ}
    (_hlambda_pos : 0 < lambda_B) (_hlambda_lt : lambda_B < 1)
    (h_sub : settlementR0Friction e lambda_B < 1)
    (h_super : 1 < settlementR0 e) :
    settlementR0Friction e lambda_B < 1 ∧
    1 < settlementR0Friction e 1 := by
  constructor
  · exact h_sub
  · rwa [settlementR0Friction_one]

-- ============================================================
-- Section 6: Displacement Dominance — Corollary 2
-- ============================================================

/-- **Corollary 2 (Displacement Dominance).**

    If the displacement ratio θ_displace/θ_restrict exceeds the
    offshore decay ratio δ_off/g_mesh_off, then government
    restriction of onshore settlement increases total offshore
    settlement volume.

    At the India-calibrated ratio θ_d/θ_r ≈ 0.84 (Smirl 2026b),
    this holds for any δ_off < 0.84 · g_off. -/
theorem displacement_dominance {theta_disp theta_rest delta_off g_off : ℝ}
    (hg : 0 < g_off) (hrest : 0 < theta_rest)
    (h_ratio : delta_off / g_off < theta_disp / theta_rest) :
    delta_off * theta_rest < theta_disp * g_off := by
  rwa [div_lt_div_iff₀ hg hrest] at h_ratio

-- ============================================================
-- Section 7: Reinforced CBDC Acceleration
-- ============================================================

/-- **Reinforced acceleration.** If the cross-coupling product
    strictly increases and self-damping does not increase, R₀
    strictly increases.

    This captures both CBDC channels: (i) bank friction removal
    increases ∂f_S/∂φ, and (ii) settlement validation increases
    ∂f_φ/∂S. The denominator (self-damping product) is unchanged
    or decreases, strengthening the inequality further. -/
theorem cbdc_acceleration_reinforced
    {num_sq num_cbdc denom_sq denom_cbdc : ℝ}
    (hnum_sq : 0 < num_sq)
    (hdenom_sq : 0 < denom_sq) (hdenom_cbdc : 0 < denom_cbdc)
    (h_num : num_sq < num_cbdc)
    (h_denom : denom_cbdc ≤ denom_sq) :
    num_sq / denom_sq < num_cbdc / denom_cbdc := by
  rw [div_lt_div_iff₀ hdenom_sq hdenom_cbdc]
  calc num_sq * denom_cbdc
      ≤ num_sq * denom_sq :=
        mul_le_mul_of_nonneg_left h_denom (le_of_lt hnum_sq)
    _ < num_cbdc * denom_sq :=
        mul_lt_mul_of_pos_right h_num hdenom_sq

-- ============================================================
-- Section 8: Monetary Policy Degradation (Proposition 5)
-- ============================================================

/-- **Monetary policy effectiveness decreases with mesh adoption.**

    FG(phi) = (1 - phi) * f(phi) represents the fraction of the economy
    responsive to monetary policy, where phi is mesh adoption and f
    is the per-capita policy effectiveness (also decreasing in phi
    as mesh agents route around monetary channels).

    Both factors (1-phi) and f(phi) decline, so FG is decreasing. -/
theorem mp_effectiveness_decreasing {phi1 phi2 f1 f2 : ℝ}
    (_hphi1 : 0 ≤ phi1) (_hphi2 : phi2 ≤ 1)
    (hphi : phi1 < phi2) (hf_pos : 0 < f1) (hf : f2 ≤ f1) :
    (1 - phi2) * f2 ≤ (1 - phi1) * f1 := by
  have h1 : 1 - phi2 ≤ 1 - phi1 := by linarith
  calc (1 - phi2) * f2
      ≤ (1 - phi2) * f1 := by nlinarith
    _ ≤ (1 - phi1) * f1 := by nlinarith

/-- **Safety zone shrinking**: the safe-asset capacity c(phi) = (1-phi)*c_0
    is strictly decreasing in mesh adoption phi. As more economic
    activity moves to mesh settlement, the fraction of settlement
    that uses fiat-denominated safe assets shrinks. -/
theorem safety_zone_shrinking {c_0 phi1 phi2 : ℝ}
    (hc : 0 < c_0) (hphi : phi1 < phi2) :
    (1 - phi2) * c_0 < (1 - phi1) * c_0 := by
  nlinarith

-- ============================================================
-- Section 9: Triffin Time (Corollary 1)
-- ============================================================

/-- **Triffin time**: the time at which settlement demand S(t)
    exceeds the safe-asset supply ceiling S_max.
    t_triffin = S_max / g_settle, where g_settle is the settlement
    growth rate. After this point, the Triffin contradiction binds:
    the settlement layer cannot be fully backed by sovereign safe assets. -/
def triffinTime (S_max g_settle : ℝ) : ℝ := S_max / g_settle

/-- Triffin time is positive when supply and growth rate are positive. -/
theorem triffin_time_pos {S_max g_settle : ℝ}
    (hS : 0 < S_max) (hg : 0 < g_settle) :
    0 < triffinTime S_max g_settle :=
  div_pos hS hg

-- ============================================================
-- Section 10: Dollarization Threshold (Proposition 3)
-- ============================================================

/-- **Dollarization threshold**: phi* = delta_S / (gamma_S * s_mesh).
    The mesh adoption fraction at which stablecoin settlement becomes
    self-sustaining: above phi*, settlement demand growth exceeds
    stablecoin attrition. -/
def dollarizationThreshold (delta_S gamma_S s_mesh : ℝ) : ℝ :=
  delta_S / (gamma_S * s_mesh)

/-- Higher settlement growth rate gamma_S lowers the dollarization
    threshold: more responsive settlement infrastructure requires
    less mesh adoption to become self-sustaining. -/
theorem threshold_decreasing {delta_S gamma1 gamma2 s : ℝ}
    (hd : 0 < delta_S) (hg1 : 0 < gamma1) (_hg2 : 0 < gamma2)
    (hs : 0 < s) (hg : gamma1 < gamma2) :
    dollarizationThreshold delta_S gamma2 s <
    dollarizationThreshold delta_S gamma1 s := by
  unfold dollarizationThreshold
  apply div_lt_div_of_pos_left hd (mul_pos hg1 hs)
    (mul_lt_mul_of_pos_right hg hs)

/-- The threshold ratio is scale-invariant: doubling s_mesh in both
    scenarios preserves the ratio of thresholds. -/
theorem threshold_ratio_invariant {delta gamma s1 s2 : ℝ}
    (_hg : 0 < gamma) (hs1 : 0 < s1) (hs2 : 0 < s2)
    (hdelta : 0 < delta) :
    dollarizationThreshold delta gamma s1 /
    dollarizationThreshold delta gamma s2 = s2 / s1 := by
  unfold dollarizationThreshold
  have hd : delta ≠ 0 := ne_of_gt hdelta
  field_simp

-- ============================================================
-- Section 11: Financial Repression Effectiveness (Proposition prop:mp)
-- ============================================================

/-- **Definition (Financial Repression Effectiveness).**

    FR(S) = FR₀ · (1 - min(1, S/S_crit))^α_FR

    Below S_crit, financial repression effectiveness declines as the
    stablecoin ecosystem grows.  Above S_crit, captive savers have a
    viable exit and financial repression is zero.

    This function is continuous everywhere including at S_crit, but
    its derivative diverges as S → S_crit⁻ when α_FR < 1 (a cusp). -/
def financialRepression (FR₀ S S_crit α_FR : ℝ) : ℝ :=
  FR₀ * (1 - min 1 (S / S_crit)) ^ α_FR

/-- The inner term 1 - min(1, S/S_crit) ∈ [0, 1] for S ≥ 0. -/
lemma fr_inner_nonneg {S S_crit : ℝ} (_hS : 0 ≤ S) (_hSc : 0 < S_crit) :
    0 ≤ 1 - min 1 (S / S_crit) := by
  simp [sub_nonneg]

/-- FR is nonneg when FR₀ ≥ 0. -/
theorem fr_nonneg {FR₀ S S_crit α_FR : ℝ}
    (hFR₀ : 0 ≤ FR₀) (hS : 0 ≤ S) (hSc : 0 < S_crit) :
    0 ≤ financialRepression FR₀ S S_crit α_FR := by
  unfold financialRepression
  exact mul_nonneg hFR₀ (rpow_nonneg (fr_inner_nonneg hS hSc) _)

/-- **FR = 0 when S ≥ S_crit.**

    Once the stablecoin ecosystem exceeds the critical threshold,
    captive savers have a viable exit and financial repression
    effectiveness drops to zero. -/
theorem fr_zero_above_critical {FR₀ S S_crit α_FR : ℝ}
    (hS_crit : 0 < S_crit) (hα : α_FR ≠ 0) (hS : S_crit ≤ S) :
    financialRepression FR₀ S S_crit α_FR = 0 := by
  unfold financialRepression
  have h1 : 1 ≤ S / S_crit := le_div_iff₀ hS_crit |>.mpr (by linarith)
  simp [min_eq_left h1, Real.zero_rpow hα, mul_zero]

/-- **For S < S_crit, FR simplifies to FR₀ · (1 - S/S_crit)^α_FR.**

    Below the critical threshold, min(1, S/S_crit) = S/S_crit. -/
lemma fr_below_critical {FR₀ S S_crit α_FR : ℝ}
    (hSc : 0 < S_crit) (_hS_nn : 0 ≤ S) (hS : S < S_crit) :
    financialRepression FR₀ S S_crit α_FR = FR₀ * (1 - S / S_crit) ^ α_FR := by
  unfold financialRepression
  congr 1
  have : S / S_crit < 1 := by rwa [div_lt_one hSc]
  simp [min_eq_right (le_of_lt this)]

/-- **FR is monotonically decreasing in S.**

    Larger stablecoin ecosystem → lower financial repression effectiveness.
    This is the core mechanism: as the exit becomes more accessible,
    the captivity that financial repression depends on erodes. -/
theorem fr_decreasing {FR₀ S₁ S₂ S_crit α_FR : ℝ}
    (hFR₀ : 0 ≤ FR₀) (hα : 0 < α_FR) (hSc : 0 < S_crit)
    (_hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) (hS : S₁ ≤ S₂) :
    financialRepression FR₀ S₂ S_crit α_FR ≤ financialRepression FR₀ S₁ S_crit α_FR := by
  unfold financialRepression
  apply mul_le_mul_of_nonneg_left _ hFR₀
  apply rpow_le_rpow (fr_inner_nonneg hS₂ hSc)
  · linarith [min_le_min_left (1 : ℝ) (div_le_div_of_nonneg_right hS (le_of_lt hSc))]
  · exact le_of_lt hα

-- ============================================================
-- Section 12: FR Continuity (resolves "discontinuity" issue)
-- ============================================================

/-- Auxiliary: min(1, S/S_crit) is continuous in S. -/
private lemma continuous_min_div (S_crit : ℝ) :
    Continuous (fun S : ℝ => min 1 (S / S_crit)) :=
  continuous_const.min (continuous_id.div_const S_crit)

/-- **FR is continuous as a function of S.**

    This is the key result resolving the "discontinuity" issue in
    Proposition prop:mp.  The function FR(S) is continuous everywhere,
    including at the critical threshold S = S_crit.  The transition from
    positive to zero is continuous (not discontinuous), but sharp: the
    derivative diverges when α_FR < 1 (see fr_deriv_diverges).

    The proof: FR is a composition of continuous functions—min, subtraction,
    rpow (with positive exponent), and scalar multiplication. -/
theorem fr_continuous {FR₀ S_crit α_FR : ℝ}
    (_hSc : 0 < S_crit) (hα : 0 < α_FR) :
    Continuous (fun S => financialRepression FR₀ S S_crit α_FR) := by
  unfold financialRepression
  apply Continuous.mul continuous_const
  apply Continuous.rpow _ continuous_const (fun x => Or.inr hα)
  exact continuous_const.sub (continuous_min_div S_crit)

-- ============================================================
-- Section 13: FR Derivative and the Cusp (α_FR < 1)
-- ============================================================

/-- **HasDerivAt for FR when S < S_crit.**

    For S in the sub-critical regime, the derivative of FR with respect
    to S is: FR₀ · (-1/S_crit) · α_FR · (1 - S/S_crit)^(α_FR - 1).

    When α_FR < 1, the exponent α_FR - 1 < 0, so the derivative
    magnitude grows without bound as S approaches S_crit from below. -/
theorem fr_hasDerivAt {FR₀ S S_crit α_FR : ℝ}
    (hSc : 0 < S_crit) (_hS_nn : 0 ≤ S) (hS : S < S_crit) :
    HasDerivAt (fun s => FR₀ * (1 - s / S_crit) ^ α_FR)
      (FR₀ * ((-1 / S_crit) * α_FR * (1 - S / S_crit) ^ (α_FR - 1))) S := by
  have h_inner : HasDerivAt (fun s => 1 - s / S_crit) (-1 / S_crit) S := by
    have := (hasDerivAt_id S).div_const S_crit
    exact (hasDerivAt_const S 1).sub this |>.congr_deriv (by ring)
  have h_pos : (1 - S / S_crit) ≠ 0 := by
    have : S / S_crit < 1 := by rwa [div_lt_one hSc]
    linarith
  have h_rpow : HasDerivAt (fun y => (1 - y / S_crit) ^ α_FR)
      ((-1 / S_crit) * α_FR * (1 - S / S_crit) ^ (α_FR - 1)) S :=
    h_inner.rpow_const (p := α_FR) (Or.inl h_pos)
  exact ((hasDerivAt_const S FR₀).mul h_rpow).congr_deriv (by ring)

/-- The magnitude of FR's derivative with respect to S. -/
def frDerivMagnitude (FR₀ α_FR S_crit S : ℝ) : ℝ :=
  FR₀ * α_FR / S_crit * (1 - S / S_crit) ^ (α_FR - 1)

/-- Auxiliary: 1 - S/S_crit → 0⁺ as S → S_crit⁻.

    This is the substitution step: the approach of S to S_crit from
    below corresponds to the inner term approaching zero from above. -/
private lemma tendsto_one_minus_div_nhdsWithin {S_crit : ℝ} (hSc : 0 < S_crit) :
    Tendsto (fun S : ℝ => 1 - S / S_crit) (nhdsWithin S_crit (Set.Iio S_crit))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : Tendsto (fun S : ℝ => 1 - S / S_crit) (nhds S_crit) (nhds 0) := by
      have h1 : (fun S : ℝ => 1 - S / S_crit) = (fun S => 1 - S * S_crit⁻¹) := by
        ext; simp [div_eq_mul_inv]
      rw [h1]
      have h2 : 1 - S_crit * S_crit⁻¹ = 0 := by
        rw [mul_inv_cancel₀ (ne_of_gt hSc)]; ring
      rw [← h2]
      exact (tendsto_const_nhds.sub (tendsto_id.mul_const _))
    exact this.mono_left nhdsWithin_le_nhds
  · apply eventually_nhdsWithin_of_forall
    intro S hS
    simp only [Set.mem_Ioi]
    linarith [div_lt_one hSc |>.mpr hS]

/-- **The cusp theorem: FR derivative magnitude diverges as S → S_crit⁻
    when α_FR < 1.**

    This is the machine-verified proof that the transition at S_crit is
    a cusp (continuous function with divergent derivative), not a
    discontinuity.  The function value goes smoothly to zero, but the
    slope becomes infinite.

    Economically: the rate of financial repression collapse accelerates
    without bound as the stablecoin ecosystem approaches the critical
    threshold—operationally indistinguishable from a discontinuity over
    any finite observation interval. -/
theorem fr_deriv_diverges {FR₀ α_FR S_crit : ℝ}
    (hFR₀ : 0 < FR₀) (hα_pos : 0 < α_FR) (hα_lt : α_FR < 1) (hSc : 0 < S_crit) :
    Tendsto (fun S => frDerivMagnitude FR₀ α_FR S_crit S)
      (nhdsWithin S_crit (Set.Iio S_crit)) atTop := by
  unfold frDerivMagnitude
  have hc : 0 < FR₀ * α_FR / S_crit := div_pos (mul_pos hFR₀ hα_pos) hSc
  apply Filter.Tendsto.const_mul_atTop hc
  have hexp : α_FR - 1 < 0 := by linarith
  exact (tendsto_rpow_neg_nhdsGT_zero hexp).comp
    (tendsto_one_minus_div_nhdsWithin hSc)

-- ============================================================
-- Section 14: Composite Monetary Policy (Proposition prop:mp complete)
-- ============================================================

/-- **Composite monetary policy effectiveness.**

    MP(φ, S) = w_FG · FG(φ) + w_QE · QE(φ) + w_FR · FR(φ, S)

    where FG and QE are decreasing in φ (Proposition 5, already
    formalized as mp_effectiveness_decreasing above) and FR is
    decreasing in S (fr_decreasing). -/
def compositeMP (FG QE : ℝ) (FR₀ S S_crit α_FR w_FG w_QE w_FR : ℝ) : ℝ :=
  w_FG * FG + w_QE * QE + w_FR * financialRepression FR₀ S S_crit α_FR

/-- **MP is decreasing in S** (through the FR channel).

    This completes part (ii) of Proposition prop:mp. -/
theorem compositeMP_decreasing_S {FG QE FR₀ S₁ S₂ S_crit α_FR w_FG w_QE w_FR : ℝ}
    (hw : 0 ≤ w_FR) (hFR₀ : 0 ≤ FR₀) (hα : 0 < α_FR) (hSc : 0 < S_crit)
    (hS₁ : 0 ≤ S₁) (hS₂ : 0 ≤ S₂) (hS : S₁ ≤ S₂) :
    compositeMP FG QE FR₀ S₂ S_crit α_FR w_FG w_QE w_FR ≤
    compositeMP FG QE FR₀ S₁ S_crit α_FR w_FG w_QE w_FR := by
  unfold compositeMP
  linarith [mul_le_mul_of_nonneg_left (fr_decreasing hFR₀ hα hSc hS₁ hS₂ hS) hw]

/-- **MP is decreasing in φ** (through FG and QE channels).

    This formalizes part (i) of Proposition prop:mp using
    the monotonicity of FG and QE established as inputs. -/
theorem compositeMP_decreasing_phi {FG₁ FG₂ QE₁ QE₂ FR₀ S S_crit α_FR w_FG w_QE w_FR : ℝ}
    (hwFG : 0 ≤ w_FG) (hwQE : 0 ≤ w_QE)
    (hFG : FG₂ ≤ FG₁) (hQE : QE₂ ≤ QE₁) :
    compositeMP FG₂ QE₂ FR₀ S S_crit α_FR w_FG w_QE w_FR ≤
    compositeMP FG₁ QE₁ FR₀ S S_crit α_FR w_FG w_QE w_FR := by
  unfold compositeMP
  linarith [mul_le_mul_of_nonneg_left hFG hwFG, mul_le_mul_of_nonneg_left hQE hwQE]

/-- **MP is continuous in S** (for fixed φ).

    This formalizes part (iii) of Proposition prop:mp—resolving the
    contradiction between "potentially discontinuous" (old claim) and
    the proof that FR is continuous.  MP is a weighted sum of continuous
    functions, hence continuous. -/
theorem compositeMP_continuous_S {FR₀ S_crit α_FR w_FG w_QE w_FR FG QE : ℝ}
    (hSc : 0 < S_crit) (hα : 0 < α_FR) :
    Continuous (fun S => compositeMP FG QE FR₀ S S_crit α_FR w_FG w_QE w_FR) := by
  unfold compositeMP
  exact continuous_const.add (continuous_const.mul (fr_continuous hSc hα))

end
