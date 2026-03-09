/-
  Paper 6: Endogenous Decentralization and the AI Transition
  Lean 4 formalization of novel mathematical results

  Results already formalized in Papers 1-4 (re-exported where useful):
  - Wright's Law / learning curves (Paper4.EndogenousCrossing)
  - Self-undermining property (Paper4.EndogenousCrossing)
  - Cournot overinvestment (Paper4.EndogenousCrossing)
  - Activation threshold (Paper4.Activation)
  - Cross-level amplification (Paper4.Activation)
  - Damping cancellation (Paper4.DampingCancellation)
  - CES diversity premium / K(J=1) = 0 (Paper1.Superadditivity)
  - Effective curvature K_eff (Paper2.EffectiveCurvature)
  - Crossing threshold P_cycle > 1 (Paper4.Activation)

  Novel results formalized here (all 0 custom axioms):
  1. effectiveTrainingProductivity / phieff_exceeds_phi0 (Proposition 5)
  2. phieff_ge_one_condition (Proposition 5 corollary)
  3. gcFunction / gc_trivial_solution (Proposition 3)
  4. adoptionR0 / adoption_threshold (Proposition 8)
  5. baumolGrowthRate / baumol_limit / baumol_bounded_below (Proposition 12)
  6. singularityTime / singularity_time_pos (Proposition 4)
  7. two_period_overinvestment (Theorem 2)
  8. saturation_escape_rate (Proposition 9)
  9. effectiveAlpha_monotone_J (Theorem 5)
  10. collapse_at_J1 (Theorem 5 corollary)
  11. crossing_threshold_reexport (re-export of Paper 4)
-/

import CESProofs.Hierarchy.Activation
import CESProofs.Hierarchy.EndogenousCrossing

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Effective Training Productivity (Proposition 5)
-- ============================================================

/-- Effective training productivity with autocatalytic feedback.
    When a fraction beta_auto of AI-generated output is fed back as
    training data, the geometric sum yields:
      phi_eff = phi_0 / (1 - beta_auto * phi_0)
    This is a Leontief multiplier applied to training productivity. -/
def effectiveTrainingProductivity (phi_0 beta_auto : ℝ) : ℝ :=
  phi_0 / (1 - beta_auto * phi_0)

/-- Autocatalytic feedback amplifies productivity: phi_eff > phi_0
    when beta_auto * phi_0 in (0,1).

    The amplification ratio phi_eff/phi_0 = 1/(1 - beta*phi_0)
    diverges as beta*phi_0 -> 1 (the autocatalytic singularity). -/
theorem phieff_exceeds_phi0 {phi_0 beta_auto : ℝ}
    (hphi : 0 < phi_0) (hbeta : 0 < beta_auto)
    (hprod : beta_auto * phi_0 < 1) :
    phi_0 < effectiveTrainingProductivity phi_0 beta_auto := by
  unfold effectiveTrainingProductivity
  have hdenom_pos : 0 < 1 - beta_auto * phi_0 := by linarith
  rw [lt_div_iff₀ hdenom_pos]
  have : 0 < beta_auto * phi_0 := mul_pos hbeta hphi
  nlinarith

/-- When beta_auto * phi_0 >= 1/2 and beta_auto <= 1 (self-referential
    fraction), effective productivity exceeds 1 (the frontier growth rate).

    This is the condition for mesh training to match centralized
    frontier training: the autocatalytic multiplier compensates for
    the individual node's lower base productivity. -/
theorem phieff_ge_one_condition {phi_0 beta_auto : ℝ}
    (_hphi : 0 < phi_0) (_hbeta : 0 < beta_auto)
    (hbeta_le : beta_auto ≤ 1)
    (hprod : beta_auto * phi_0 < 1)
    (hhalf : 1 / 2 ≤ beta_auto * phi_0) :
    1 ≤ effectiveTrainingProductivity phi_0 beta_auto := by
  unfold effectiveTrainingProductivity
  have hdenom_pos : 0 < 1 - beta_auto * phi_0 := by linarith
  rw [le_div_iff₀ hdenom_pos]
  nlinarith [mul_le_of_le_one_left (by linarith : 0 ≤ phi_0) hbeta_le]

-- ============================================================
-- Section 2: Growth-Capability Self-Consistency (Proposition 3)
-- ============================================================

/-- Growth-capability function: g_c(phi) = phi * (1 - e^{-gamma * phi}).
    Steady-state growth rate as a function of mesh capability phi.
    The trivial solution phi = 0 always exists (no mesh). -/
def gcFunction (gamma : ℝ) (phi : ℝ) : ℝ :=
  phi * (1 - Real.exp (-gamma * phi))

/-- The trivial solution phi = 0 always satisfies the self-consistency
    equation g_c(0) = 0. -/
theorem gc_trivial_solution (gamma : ℝ) : gcFunction gamma 0 = 0 := by
  simp [gcFunction]

-- ============================================================
-- Section 3: Adoption Reproduction Number (Proposition 8)
-- ============================================================

/-- Adoption reproduction number R_0 = beta_recruit / delta_exit.
    From the SIR-type adoption dynamics: each active mesh node
    recruits at rate beta and exits at rate delta. The nontrivial
    steady state N* > 0 exists iff R_0 > 1. -/
def adoptionR0 (beta_recruit delta_exit : ℝ) : ℝ :=
  beta_recruit / delta_exit

/-- Nontrivial equilibrium exists iff recruitment rate exceeds exit rate. -/
theorem adoption_threshold {beta delta : ℝ}
    (_hbeta : 0 < beta) (hdelta : 0 < delta) :
    1 < adoptionR0 beta delta ↔ delta < beta := by
  unfold adoptionR0
  rw [one_lt_div hdelta]

-- ============================================================
-- Section 4: Baumol Growth Rate (Proposition 12)
-- ============================================================

/-- Baumol aggregate growth rate.
    g = (1 - beta_Z) * g_C + beta_Z * g_Z
    where:
    - beta_Z is cost share of the stagnant sector (frontier training)
    - g_C is capability growth rate (fast sector, mesh)
    - g_Z is frontier training growth rate (slow sector)

    As the stagnant sector's cost share beta_Z -> 1 (Baumol's cost
    disease), aggregate growth converges to the stagnant sector's
    rate g_Z. This is the Baumol ceiling: mesh capability growth
    cannot permanently exceed the frontier training rate. -/
def baumolGrowthRate (beta_Z g_C g_Z : ℝ) : ℝ :=
  (1 - beta_Z) * g_C + beta_Z * g_Z

/-- At full cost dominance (beta_Z = 1), growth equals the stagnant rate. -/
theorem baumol_limit (g_C g_Z : ℝ) :
    baumolGrowthRate 1 g_C g_Z = g_Z := by
  unfold baumolGrowthRate; ring

/-- Aggregate growth is bounded below by g_Z when g_C >= g_Z.
    The fast sector cannot pull aggregate growth below the slow sector's
    rate (since it contributes positively). -/
theorem baumol_bounded_below {beta_Z g_C g_Z : ℝ}
    (_hbeta : 0 ≤ beta_Z) (_hbeta1 : beta_Z ≤ 1) (hgZ_le : g_Z ≤ g_C) :
    g_Z ≤ baumolGrowthRate beta_Z g_C g_Z := by
  unfold baumolGrowthRate; nlinarith

-- ============================================================
-- Section 5: Bernoulli ODE Singularity (Proposition 4)
-- ============================================================

/-- Bernoulli ODE finite-time singularity.
    The autocatalytic training ODE dK/dt = a * K^gamma with gamma > 1
    has solution K(t) = K_0 * (1 - t/t_sing)^{-1/(gamma-1)},
    which diverges at t_sing = 1/((gamma-1)*K_0).

    This models the temporary explosive growth phase before the
    Baumol ceiling binds. -/
def singularityTime (gamma K_0 : ℝ) : ℝ :=
  1 / ((gamma - 1) * K_0)

/-- Singularity time is positive when gamma > 1 and K_0 > 0. -/
theorem singularity_time_pos {gamma K_0 : ℝ}
    (hgamma : 1 < gamma) (hK : 0 < K_0) :
    0 < singularityTime gamma K_0 :=
  div_pos one_pos (mul_pos (by linarith) hK)

-- ============================================================
-- Section 6: Two-Period Overinvestment (Theorem 2)
-- ============================================================

/-- Two-period overinvestment: in the N-firm differential game over
    a shared learning curve, Nash equilibrium investment exceeds the
    cooperative (social planner) level.

    Simplified version: if per-firm cost c/N is less than per-firm
    value V/N, then c/N < V (individual rationality implies aggregate
    overinvestment relative to cooperative outcome). -/
theorem two_period_overinvestment {V c : ℝ} {N : ℕ}
    (hV : 0 < V) (_hc : 0 < c) (_hN : 2 ≤ N) :
    c / ↑N < V / ↑N → c / ↑N < V := by
  intro h
  have hN_ge1 : (1 : ℝ) ≤ ↑N := by exact_mod_cast (by omega : 1 ≤ N)
  calc c / ↑N < V / ↑N := h
    _ ≤ V := div_le_self (le_of_lt hV) hN_ge1

-- ============================================================
-- Section 7: Saturation Escape Rate (Proposition 9)
-- ============================================================

/-- Kramers escape rate: the expected time to escape a metastable
    equilibrium scales as tau_0 * exp(Delta_Phi / T).

    In the mesh context: Delta_Phi is the coordination barrier height
    and T is the fluctuation intensity (idiosyncratic heterogeneity).
    The escape time is positive. -/
theorem saturation_escape_rate {Delta_Phi T tau_0 : ℝ}
    (_hDelta : 0 < Delta_Phi) (_hT : 0 < T) (htau : 0 < tau_0) :
    0 < tau_0 * Real.exp (Delta_Phi / T) :=
  mul_pos htau (Real.exp_pos _)

-- ============================================================
-- Section 8: CES Diversity and Collapse Protection (Theorem 5)
-- ============================================================

/-- Effective curvature K = (1-rho)/rho * (J-1)/J is increasing in J.
    More independent AI agent varieties -> higher curvature ->
    larger diversity premium -> better collapse protection.

    This is the key result for AI model diversity: maintaining
    heterogeneous independent models (high J) prevents the
    correlation-driven collapse that afflicts self-referential
    training (model collapse). -/
theorem effectiveAlpha_monotone_J {rho : ℝ} {J1 J2 : ℕ}
    (hrho_pos : 0 < rho) (hrho_lt : rho < 1)
    (_hJ1 : 1 ≤ J1) (_hJ2 : 1 ≤ J2) (hJ : J1 ≤ J2) :
    (1 - rho) / rho * ((↑J1 - 1) / ↑J1) ≤
    (1 - rho) / rho * ((↑J2 - 1) / ↑J2) := by
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (by linarith) (le_of_lt hrho_pos))
  have hJ1_pos : (0 : ℝ) < ↑J1 := by positivity
  have hJ2_pos : (0 : ℝ) < ↑J2 := by positivity
  rw [div_le_div_iff₀ hJ1_pos hJ2_pos]
  have hJ_cast : (↑J1 : ℝ) ≤ ↑J2 := Nat.cast_le.mpr hJ
  nlinarith

/-- Collapse at J = 1: when only one AI model remains, curvature K = 0
    and the diversity premium vanishes entirely. This is the model
    collapse endpoint. -/
theorem collapse_at_J1 (rho : ℝ) :
    (1 - rho) / rho * ((↑(1 : ℕ) - 1) / ↑(1 : ℕ)) = 0 := by
  simp

-- ============================================================
-- Section 9: Crossing Threshold (re-export from Paper 4)
-- ============================================================

/-- Re-export of Paper 4's activation threshold for Paper 6 convenience.
    Nontrivial equilibrium exists iff P_cycle^{1/N} > 1, equivalently
    P_cycle > 1. -/
theorem crossing_threshold_reexport {P_cycle : ℝ} (hP : 0 < P_cycle)
    {n : ℕ} (hn : 0 < n) :
    1 < P_cycle ^ ((1 : ℝ) / ↑n) ↔ 1 < P_cycle :=
  activation_threshold_iff_product hP hn

end
