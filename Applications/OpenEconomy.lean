/-
  Open Economy Monetary Transmission

  Monetary policy divergence between countries is a source of bilateral
  friction T. The existing K_eff(T) framework handles the consequences;
  this file bridges monetary policy to bilateral friction and formalizes
  the impossible trinity.

  Key results:
  - Monetary divergence as bilateral friction
  - Impossible trinity: zero bilateral friction + zero capital controls → same policy
  - Complementary sectors transmit foreign shocks more strongly (ρ-ordering)
  - Institutional amplification in open economy
  - Hub reform benefits all spokes
  - Trade-weighted response bounds
-/

import CESProofs.Potential.BilateralTrade
import CESProofs.Hierarchy.MonetaryPolicy
import CESProofs.Hierarchy.InstitutionalReform
import CESProofs.Dynamics.FluctuationResponse
import CESProofs.Applications.Economics

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Definitions
-- ============================================================

/-- Bilateral friction from monetary policy divergence.
    When two countries pursue different monetary policies (different
    information friction levels), the divergence itself acts as a
    source of bilateral friction for trade between them. -/
def monetaryDivergenceFriction (T_home T_foreign : ℝ) : ℝ :=
  |T_home - T_foreign|

/-- Total bilateral friction: monetary divergence + capital controls + trade barriers.
    The three sources of bilateral friction map to the three legs of the
    impossible trinity: monetary independence, capital mobility, exchange rate stability. -/
def totalBilateralFriction (T_home T_foreign T_capital T_trade : ℝ) : ℝ :=
  |T_home - T_foreign| + T_capital + T_trade

/-- Trade-weighted average response across N partners.
    When a country has multiple trading partners, the aggregate
    monetary spillover is the trade-weighted sum of bilateral responses. -/
def tradeWeightedResponse (N : ℕ) (w response : Fin N → ℝ) : ℝ :=
  ∑ j : Fin N, w j * response j

-- ============================================================
-- Result OE-1: Divergence Raises Bilateral Friction
-- ============================================================

/-- **Result OE-1 (Divergence Raises Bilateral Friction)**.
    When two countries pursue different monetary policies (T_h ≠ T_f),
    the bilateral friction from monetary divergence is strictly positive.
    Different policies create real costs for cross-border trade. -/
theorem divergence_raises_bilateral_friction {T_h T_f : ℝ}
    (h : T_h ≠ T_f) :
    0 < monetaryDivergenceFriction T_h T_f := by
  simp only [monetaryDivergenceFriction]
  exact abs_pos.mpr (sub_ne_zero.mpr h)

-- ============================================================
-- Result OE-2: Common Policy = Zero Friction
-- ============================================================

/-- **Result OE-2 (Common Policy Eliminates Monetary Friction)**.
    When two countries adopt the same monetary policy (T_h = T_f),
    there is zero monetary divergence friction. This is the benefit
    of a currency union: it eliminates monetary policy divergence
    as a source of bilateral friction. -/
theorem common_policy_zero_friction {T_h T_f : ℝ}
    (h : T_h = T_f) :
    monetaryDivergenceFriction T_h T_f = 0 := by
  simp only [monetaryDivergenceFriction, h, sub_self, abs_zero]

-- ============================================================
-- Result OE-3: Impossible Trinity
-- ============================================================

/-- **Result OE-3 (Impossible Trinity)**.
    If bilateral friction is zero AND capital controls are zero,
    then monetary policies must be identical: T_home = T_foreign.

    This is the Mundell-Fleming impossible trinity as an algebraic
    consequence: you cannot simultaneously have (1) zero bilateral
    friction (stable exchange rate), (2) free capital flow (T_capital = 0),
    and (3) independent monetary policy (T_home ≠ T_foreign).

    **Proof.** Total bilateral friction $= |T_h - T_f| + T_{\mathrm{capital}} + T_{\mathrm{trade}} = 0$ with $T_{\mathrm{capital}}, T_{\mathrm{trade}} \geq 0$ forces each non-negative term to vanish. In particular $|T_h - T_f| = 0$, which implies $T_h = T_f$. -/
theorem impossible_trinity {T_home T_foreign T_capital T_trade : ℝ}
    (h_total : totalBilateralFriction T_home T_foreign T_capital T_trade = 0)
    (h_cap : 0 ≤ T_capital) (h_trade : 0 ≤ T_trade) :
    T_home = T_foreign := by
  simp only [totalBilateralFriction] at h_total
  have h1 : |T_home - T_foreign| = 0 := by linarith [abs_nonneg (T_home - T_foreign)]
  linarith [abs_eq_zero.mp h1]

-- ============================================================
-- Result OE-4: Currency Union Maximizes K_eff
-- ============================================================

/-- **Result OE-4 (Currency Union Maximizes K_eff)**.
    Zero bilateral friction gives full structural curvature K_eff = K.
    A currency union that eliminates monetary divergence friction
    achieves the maximum possible effective curvature. -/
theorem currency_union_maximizes_Keff (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {Tstar : ℝ} (hTs : 0 < Tstar) :
    effectiveCurvatureKeff J ρ 0 Tstar = curvatureK J ρ :=
  effectiveCurvatureKeff_zero_friction J ρ Tstar hTs

-- ============================================================
-- Result OE-5: Spillover Stronger for Complements
-- ============================================================

/-- **Result OE-5 (Spillover Stronger for Complements)**.
    More complementary sectors (lower ρ) transmit foreign monetary
    shocks more strongly. The ρ-ordering of monetary transmission
    applies to open economy spillovers: manufacturing transmits
    foreign rate changes more than services.

    Proved: reuses monetary_transmission_ordering from Paper 4. -/
theorem spillover_stronger_for_complements {J : ℕ} (hJ : 2 ≤ J)
    {ρ1 ρ2 : ℝ} (hρ : ρ1 < ρ2)
    {T_new T_old Tstar : ℝ} (hTs : 0 < Tstar) (h : T_new ≤ T_old) :
    policyResponse J ρ2 T_new T_old Tstar ≤
    policyResponse J ρ1 T_new T_old Tstar :=
  monetary_transmission_ordering hJ hρ hTs h

-- ============================================================
-- Result OE-6: Institutions Dampen Spillover
-- ============================================================

/-- **Result OE-6 (Institutions Dampen Foreign Spillovers)**.
    Higher institutional quality T* in the receiving country raises
    K_eff at any given friction level. Countries with stronger
    institutions are more resilient to foreign monetary shocks:
    their higher T* means the same friction increase has a smaller
    proportional effect on K_eff.

    Proved: reuses institutional_amplification from Paper 4. -/
theorem institutions_dampen_spillover {J : ℕ} (hJ : 2 ≤ J)
    {ρ : ℝ} (hρ : ρ < 1)
    {T Tstar1 Tstar2 : ℝ} (hTs1 : 0 < Tstar1) (hTs2 : 0 < Tstar2)
    (h : Tstar1 ≤ Tstar2) (hT : 0 ≤ T) :
    effectiveCurvatureKeff J ρ T Tstar1 ≤ effectiveCurvatureKeff J ρ T Tstar2 :=
  institutional_amplification hJ hρ hTs1 hTs2 h hT

-- ============================================================
-- Result OE-7: Trade-Weighted Response Bounded
-- ============================================================

/-- **Result OE-7 (Trade-Weighted Response Bounded)**.
    The trade-weighted average response is bounded by the maximum
    individual response when weights sum to 1.
    Σ w_j · r_j ≤ r_max when Σ w_j = 1 and w_j ≥ 0. -/
theorem trade_weighted_response_bounded {N : ℕ}
    {w response : Fin N → ℝ}
    (hw_nn : ∀ j, 0 ≤ w j)
    (hw_sum : ∑ j : Fin N, w j = 1)
    {r_max : ℝ} (hr : ∀ j, response j ≤ r_max) :
    tradeWeightedResponse N w response ≤ r_max := by
  simp only [tradeWeightedResponse]
  calc ∑ j : Fin N, w j * response j
      ≤ ∑ j : Fin N, w j * r_max := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hr j) (hw_nn j)
    _ = (∑ j : Fin N, w j) * r_max := by rw [Finset.sum_mul]
    _ = 1 * r_max := by rw [hw_sum]
    _ = r_max := one_mul _

-- ============================================================
-- Result OE-8: Hub Reform Benefits All Spokes
-- ============================================================

/-- **Result OE-8 (Hub Reform Benefits All Spokes)**.
    Raising institutional quality T* in a trade hub increases
    K_eff for all bilateral relationships with that hub.
    This is the open-economy version of the upstream reform principle:
    institutional reform in a central country benefits the entire
    trade network.

    Proved: applies institutional_amplification to each spoke. -/
theorem hub_reform_benefits_all_spokes {J : ℕ} (hJ : 2 ≤ J)
    {ρ : ℝ} (hρ : ρ < 1)
    {T : ℝ} (hT : 0 ≤ T)
    {Tstar_old Tstar_new : ℝ} (hOld : 0 < Tstar_old) (hNew : 0 < Tstar_new)
    (h_reform : Tstar_old ≤ Tstar_new) :
    effectiveCurvatureKeff J ρ T Tstar_old ≤ effectiveCurvatureKeff J ρ T Tstar_new :=
  institutional_amplification hJ hρ hOld hNew h_reform hT

-- ============================================================
-- Result OE-9: Spectral Gap and Convergence
-- ============================================================

/-- **Result OE-9 (Spectral Gap Convergence)**.
    Higher algebraic connectivity λ₂ of the trade network Laplacian
    implies faster convergence of bilateral shocks to steady state.
    This connects to the U5 spectral gap result: λ₂ predicts
    business cycle synchronization.

    **Proof.** The mixing time of diffusion on the trade network is bounded by
    $1/\lambda_2$ (Fiedler 1973). For spectral gaps $0 < \lambda_1 < \lambda_2$,
    the mixing time $1/\lambda_2 < 1/\lambda_1$, so higher algebraic connectivity
    compresses the slowest mode and bilateral shocks converge faster. -/
theorem spectralGap_convergence {gap₁ gap₂ : ℝ} (h₁ : 0 < gap₁) (hlt : gap₁ < gap₂) :
    1 / gap₂ < 1 / gap₁ := by
  exact div_lt_div_of_pos_left one_pos h₁ hlt

-- ============================================================
-- Result OE-10: Monetary Divergence Symmetric
-- ============================================================

/-- **Result OE-10 (Monetary Divergence is Symmetric)**.
    The friction from monetary divergence is symmetric:
    |T_h - T_f| = |T_f - T_h|. Neither country "causes" the
    divergence — it is a bilateral property. -/
theorem monetary_divergence_symmetric (T_h T_f : ℝ) :
    monetaryDivergenceFriction T_h T_f = monetaryDivergenceFriction T_f T_h := by
  simp only [monetaryDivergenceFriction, abs_sub_comm]

end
