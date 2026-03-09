/-
  Time Inconsistency Resolution via Upstream Reform (Gap 11)

  Damping cancellation makes the discretionary equilibrium degenerate:
  changing own-level regulation σ_n has zero welfare effect, creating an
  incentive to *appear* active. Under commitment, the bank pre-commits to
  upstream reform (reducing σ_{n-1} or increasing β_n), which has real
  positive welfare effects. The policy bias (commitment minus discretion)
  is strictly positive whenever K > 0.

  Key reuse:
  - welfare_independent_of_own_sigma (Paper4/DampingCancellation.lean)
  - upstream_reform_beta (Paper4/InstitutionalReform.lean → via Defs)
  - welfareContribution (Paper4/Defs.lean)
  - complementary_goods_more_fragile (Paper2/BilateralTrade.lean)

  Results TI-1 through TI-10: 10 fully proved, 0 schematic, 0 axioms.
-/

import CESProofs.Hierarchy.DampingCancellation
import CESProofs.Hierarchy.InstitutionalReform
import CESProofs.Potential.BilateralTrade

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Definitions
-- ============================================================

/-- Discretionary welfare gain from changing own-level regulation σ_n.
    By damping cancellation, this is always zero regardless of σ_n values.
    The bank adjusts σ_n from sigma_old to sigma_new; the welfare effect is
    the difference in c · Fbar · σ · δ² terms. -/
def discretionaryGain (c phi_prev sigma_old sigma_new delta : ℝ) : ℝ :=
  c * (phi_prev / sigma_new) * sigma_new * delta ^ 2 -
  c * (phi_prev / sigma_old) * sigma_old * delta ^ 2

/-- Commitment welfare gain from upstream reform (increasing β_n).
    Welfare contribution V = σ_{n-1}·δ²/β, so increasing β reduces V
    (welfare loss), yielding a positive gain. -/
def commitmentGain (sigma_prev delta beta_old beta_new : ℝ) : ℝ :=
  welfareContribution sigma_prev delta beta_old -
  welfareContribution sigma_prev delta beta_new

/-- Policy bias: the welfare gap between commitment and discretion.
    Positive bias means commitment strictly dominates. -/
def policyBias (c phi_prev sigma_old sigma_new sigma_prev delta beta_old beta_new : ℝ) : ℝ :=
  commitmentGain sigma_prev delta beta_old beta_new -
  discretionaryGain c phi_prev sigma_old sigma_new delta

-- ============================================================
-- Section 2: TI-1 — Discretionary Gain Is Zero
-- ============================================================

/-- **TI-1 (Discretionary gain is zero).**
    The discretionary welfare gain from changing σ_n is exactly zero,
    because both terms equal c · phi_prev · δ² by the damping cancellation
    identity (div_mul_cancel). -/
theorem discretionary_gain_zero {c phi_prev sigma_old sigma_new delta : ℝ}
    (hs1 : sigma_old ≠ 0) (hs2 : sigma_new ≠ 0) :
    discretionaryGain c phi_prev sigma_old sigma_new delta = 0 := by
  simp only [discretionaryGain]
  have h1 := welfare_independent_of_own_sigma (phi_prev := phi_prev) (c := c)
    (delta := delta) hs2 hs1
  linarith

-- ============================================================
-- Section 3: TI-2 — Commitment Gain Is Positive
-- ============================================================

/-- **TI-2 (Commitment gain is positive).**
    When β_old < β_new, the commitment welfare gain is strictly positive:
    V(β_old) > V(β_new), so the difference is positive. -/
theorem commitmentGain_positive {sigma_prev delta beta_old beta_new : ℝ}
    (hs : 0 < sigma_prev) (hdelta : delta ≠ 0)
    (hb1 : 0 < beta_old) (hb2 : 0 < beta_new) (h12 : beta_old < beta_new) :
    0 < commitmentGain sigma_prev delta beta_old beta_new := by
  simp only [commitmentGain]
  linarith [upstream_reform_beta hs hdelta hb1 hb2 h12]

-- ============================================================
-- Section 4: TI-3 — Policy Bias Is Positive
-- ============================================================

/-- **TI-3 (Policy bias is positive).**
    The policy bias (commitment minus discretion) is strictly positive
    when β_old < β_new. Discretion contributes zero; commitment
    contributes a strictly positive welfare improvement. -/
theorem policyBias_positive {c phi_prev sigma_old sigma_new sigma_prev delta
    beta_old beta_new : ℝ}
    (hs_old : sigma_old ≠ 0) (hs_new : sigma_new ≠ 0)
    (hs_prev : 0 < sigma_prev) (hdelta : delta ≠ 0)
    (hb1 : 0 < beta_old) (hb2 : 0 < beta_new) (h12 : beta_old < beta_new) :
    0 < policyBias c phi_prev sigma_old sigma_new sigma_prev delta beta_old beta_new := by
  simp only [policyBias]
  have hd := discretionary_gain_zero hs_old hs_new
    (c := c) (phi_prev := phi_prev) (delta := delta)
  have hc := commitmentGain_positive hs_prev hdelta hb1 hb2 h12
    (sigma_prev := sigma_prev)
  linarith

-- ============================================================
-- Section 5: TI-4 — Discretion Zero Cost of Appearing Active
-- ============================================================

/-- **TI-4 (Zero cost of appearing active).**
    Restatement of TI-1: the discretionary equilibrium has zero welfare
    cost for any σ_n adjustment, making it costless to appear active. -/
theorem discretion_zero_cost_of_appearing {c phi_prev sigma_old sigma_new delta : ℝ}
    (hs1 : sigma_old ≠ 0) (hs2 : sigma_new ≠ 0) :
    discretionaryGain c phi_prev sigma_old sigma_new delta = 0 :=
  discretionary_gain_zero hs1 hs2

-- ============================================================
-- Section 6: TI-5 — Commitment Resolves Inconsistency
-- ============================================================

/-- **TI-5 (Commitment resolves inconsistency).**
    Positive commitment gain means no incentive to deviate from upstream
    reform: reverting β to a lower value would reduce welfare. -/
theorem commitment_resolves_inconsistency {sigma_prev delta beta_old beta_new : ℝ}
    (hs : 0 < sigma_prev) (hdelta : delta ≠ 0)
    (hb1 : 0 < beta_old) (hb2 : 0 < beta_new) (h12 : beta_old < beta_new) :
    welfareContribution sigma_prev delta beta_new <
    welfareContribution sigma_prev delta beta_old :=
  upstream_reform_beta hs hdelta hb1 hb2 h12

-- ============================================================
-- Section 7: TI-6 — ρ Drift Shifts T*
-- ============================================================

/-- **TI-6 (ρ drift shifts T*).**
    Different ρ values yield different critical frictions T*.
    Under endogenous ρ drift, the target T* is a moving target. -/
theorem rho_drift_shifts_Tstar {J : ℕ} (hJ : 2 ≤ J)
    {rho1 rho2 : ℝ} (hrho1 : rho1 < 1) (hrho2 : rho2 < 1)
    (hrho : rho1 < rho2) {c d_sq : ℝ} (hc : 0 < c) (hd : 0 < d_sq) :
    criticalFriction J rho1 c d_sq ≠ criticalFriction J rho2 c d_sq :=
  ne_of_lt (complementary_goods_more_fragile hJ hrho1 hrho2 hrho hc hd)

-- ============================================================
-- Section 8: TI-7 — Discretion Robust to ρ Drift
-- ============================================================

/-- **TI-7 (Discretion robust to ρ drift).**
    The discretionary gain is zero regardless of ρ: the σ_n cancellation
    is purely algebraic and does not depend on the curvature parameter. -/
theorem discretion_robust_to_drift {c phi_prev sigma_old sigma_new delta : ℝ}
    (hs1 : sigma_old ≠ 0) (hs2 : sigma_new ≠ 0)
    (_ρ : ℝ) :
    discretionaryGain c phi_prev sigma_old sigma_new delta = 0 :=
  discretionary_gain_zero hs1 hs2

-- ============================================================
-- Section 9: TI-8 — Commitment Robust to ρ Drift
-- ============================================================

/-- **TI-8 (Commitment robust to ρ drift).**
    The commitment gain is positive regardless of ρ: the β comparison
    is structural (welfare contribution V = σ_{n-1}·δ²/β is independent of ρ). -/
theorem commitment_robust_to_drift {sigma_prev delta beta_old beta_new : ℝ}
    (hs : 0 < sigma_prev) (hdelta : delta ≠ 0)
    (hb1 : 0 < beta_old) (hb2 : 0 < beta_new) (h12 : beta_old < beta_new)
    (_ρ : ℝ) :
    0 < commitmentGain sigma_prev delta beta_old beta_new :=
  commitmentGain_positive hs hdelta hb1 hb2 h12

-- ============================================================
-- Section 10: TI-9 — Phillips Flat Under Discretion
-- ============================================================

/-- **TI-9 (Phillips flat under discretion).**
    The discretionary response to σ_n change is zero: the damping
    cancellation algebraic identity holds for any sigma values.
    This is a direct restatement of damping_cancellation_algebraic. -/
theorem phillips_flat_discretion {phi_prev sigma_n c_n : ℝ}
    (hsigma : sigma_n ≠ 0) :
    c_n * (phi_prev / sigma_n) * sigma_n = c_n * phi_prev :=
  damping_cancellation_algebraic hsigma

-- ============================================================
-- Section 11: TI-10 — Commitment Dominates Discretion
-- ============================================================

/-- **TI-10 (Commitment dominates discretion).**
    For any σ_n choice, commitment to upstream reform weakly dominates
    discretion: discretion gain = 0 ≤ commitment gain > 0. -/
theorem commitment_dominates_discretion {c phi_prev sigma_old sigma_new sigma_prev delta
    beta_old beta_new : ℝ}
    (hs_old : sigma_old ≠ 0) (hs_new : sigma_new ≠ 0)
    (hs_prev : 0 < sigma_prev) (hdelta : delta ≠ 0)
    (hb1 : 0 < beta_old) (hb2 : 0 < beta_new) (h12 : beta_old < beta_new) :
    discretionaryGain c phi_prev sigma_old sigma_new delta ≤
    commitmentGain sigma_prev delta beta_old beta_new := by
  rw [discretionary_gain_zero hs_old hs_new]
  exact le_of_lt (commitmentGain_positive hs_prev hdelta hb1 hb2 h12)

end
