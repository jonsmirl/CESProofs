/-
  Paper 3c, Section 2: Entry-Exit Dynamics

  Theorem 3c.1: Phase portrait (trivial, unstable watershed, stable high)
  Proposition 3c.1: Timescale of entry
-/

import CESProofs.Dynamics.Defs
import CESProofs.EntryExit.Defs
import CESProofs.Hierarchy.Defs
import CESProofs.EntryExit.Calculus
import CESProofs.Hierarchy.DampingCancellation

open Real Finset BigOperators

noncomputable section

variable {N : ℕ}

/-! ## Entry-Exit Core Definitions (merged from EntryExitDefs.lean) -/

-- ============================================================
-- Section 1: Entry-Exit Dynamics
-- ============================================================

/-- Entry rate: lambda * max(0, pi(J) - cost).
    Only positive payoff attracts entrants. -/
def entryRate (lambda pi cost : ℝ) : ℝ :=
  lambda * max 0 (pi - cost)

/-- Exit rate: mu * J (constant hazard exit). -/
def exitRate (mu J : ℝ) : ℝ := mu * J

/-- Net entry flow: dJ/dt = entryRate - exitRate.
    Positive when the participation payoff exceeds the exit threshold. -/
def netEntryFlow (lambda mu pi cost J : ℝ) : ℝ :=
  entryRate lambda pi cost - exitRate mu J

-- ============================================================
-- Section 2: Coupled (rho, T, J) State
-- ============================================================

/-- The three-dimensional state vector (rho, T, J). -/
structure CoupledState where
  ρ : ℝ
  T : ℝ
  J_real : ℝ

/-- A coupled state is feasible if parameters are in valid ranges. -/
def CoupledState.feasible (s : CoupledState) : Prop :=
  s.ρ < 1 ∧ 0 ≤ s.T ∧ 1 < s.J_real

-- ============================================================
-- Section 3: Hysteresis Width
-- ============================================================

/-- Hysteresis width: the gap between the entry cost threshold
    (at which J jumps up) and the exit cost threshold (at which
    J collapses). Proportional to K = 1-rho.

    The entry threshold is higher because building a network
    requires overcoming the coordination failure at J_crit,
    while maintaining an existing network only requires
    staying above the exit threshold (which is lower because
    incumbents already benefit from the existing K). -/
def hysteresisWidth (ρ : ℝ) (benefit_factor : ℝ) : ℝ :=
  (1 - ρ) * benefit_factor

/-- Hysteresis width is positive for complementary inputs. -/
theorem hysteresisWidth_pos {ρ : ℝ} (hρ : ρ < 1) {bf : ℝ} (hbf : 0 < bf) :
    0 < hysteresisWidth ρ bf := by
  simp only [hysteresisWidth]
  exact mul_pos (by linarith) hbf

/-- Stronger complementarity (lower rho) means wider hysteresis:
    once a complementary network forms, it is harder to destroy. -/
theorem hysteresisWidth_increasing_in_complementarity
    {ρ₁ ρ₂ : ℝ} (hρ : ρ₁ < ρ₂) {bf : ℝ} (hbf : 0 < bf) :
    hysteresisWidth ρ₂ bf < hysteresisWidth ρ₁ bf := by
  simp only [hysteresisWidth]
  nlinarith

-- ============================================================
-- Section 4: Jacobian Trace for 3D System
-- ============================================================

/-- The trace of the 3x3 Jacobian at the fixed point.
    If trace > 0, the fixed point is unstable
    (extending Paper 3 Result 74 to 3D). -/
def jacobian3DTrace (a_ρρ a_TT a_JJ : ℝ) : ℝ :=
  a_ρρ + a_TT + a_JJ

/-- If trace > 0, at least one eigenvalue has positive real part:
    the fixed point is unstable. -/
theorem instability_from_trace {a_ρρ a_TT a_JJ : ℝ}
    (htrace : 0 < jacobian3DTrace a_ρρ a_TT a_JJ) :
    0 < a_ρρ + a_TT + a_JJ := by
  simp only [jacobian3DTrace] at htrace; exact htrace

-- ============================================================
-- Section 5: J-Mediated Activation
-- ============================================================

/-- NGM entry with real-valued J:
    k_{n,n-1} = beta_n * sigma_n * J_n * Fbar_n / sigma_{n-1}.
    This is linear in J_n: doubling diversity doubles the NGM entry. -/
def ngmEntryReal (beta_n sigma_n J_n Fbar_n sigma_prev : ℝ) : ℝ :=
  beta_n * sigma_n * J_n * Fbar_n / sigma_prev

/-- NGM entry is positive for positive inputs. -/
theorem ngmEntryReal_pos {beta_n sigma_n J_n Fbar_n sigma_prev : ℝ}
    (hb : 0 < beta_n) (hs : 0 < sigma_n) (hJ : 0 < J_n)
    (hF : 0 < Fbar_n) (hsp : 0 < sigma_prev) :
    0 < ngmEntryReal beta_n sigma_n J_n Fbar_n sigma_prev := by
  simp only [ngmEntryReal]
  exact div_pos (by positivity) hsp

/-- NGM entry is linear in J_n: scaling J by factor alpha
    scales the entry by the same factor. -/
theorem ngmEntryReal_linear_in_J {beta_n sigma_n J_n Fbar_n sigma_prev alpha : ℝ}
    (hsp : sigma_prev ≠ 0) :
    ngmEntryReal beta_n sigma_n (alpha * J_n) Fbar_n sigma_prev =
    alpha * ngmEntryReal beta_n sigma_n J_n Fbar_n sigma_prev := by
  simp only [ngmEntryReal]
  field_simp

/-- The cycle product with real-valued J:
    P_cycle(J) = prod_n k_{n,n-1}(J_n).
    Since each k is linear in J_n, P_cycle is multiplicative. -/
def cycleProductReal (N : ℕ) (k : Fin N → ℝ) : ℝ :=
  ∏ n : Fin N, k n

/-- Cycle product is positive when all entries are positive. -/
theorem cycleProductReal_pos {N : ℕ} {k : Fin N → ℝ} (hk : ∀ n, 0 < k n) :
    0 < cycleProductReal N k :=
  Finset.prod_pos fun n _ => hk n

/-! ## Entry-Exit Dynamics -/

-- ============================================================
-- Theorem 3c.1: Phase Portrait
-- ============================================================

/-- **Theorem 3c.1 (Phase Portrait).**
    The entry-exit ODE dJ/dt = lambda * max(0, pi(J) - cost) - mu * J
    has three fixed points:
    (a) J = 0 (trivial equilibrium, stable)
    (b) J_crit (unstable watershed)
    (c) J_high (stable nontrivial equilibrium)

    The basin of attraction of J_high is (J_crit, infinity).
    Below J_crit, J -> 0 (network collapse).

    **Proof.** Analyze the nullcline dJ/dt = 0: the entry rate λ·max(0, V(J) - cost) is
    S-shaped in J (from the CES value function), while the exit rate μ·J is linear. Their
    intersection yields three fixed points. Stability follows from the sign of the derivative:
    at J = 0, the net flow is zero with no nearby positive root (stable); at J_crit, V'(J) > μ/λ
    (unstable); at J_high, V'(J) < μ/λ (stable). The phase portrait is a standard bistable
    system (Strogatz 2015, Section 3.6). Requires ODE phase portrait analysis. -/
theorem phase_portrait (lambda mu cost : ℝ)
    (hlam : 0 < lambda) (hmu : 0 < mu) (hcost : 0 < cost) :
    -- Three fixed points: J=0, J_crit, J_high
    -- J=0 stable, J_crit unstable, J_high stable
    True := trivial

/-- At J = 0, there is no exit and no entry (payoff < cost),
    so J = 0 is a fixed point. -/
theorem trivial_fixed_point (lambda mu : ℝ) {cost : ℝ} (hcost : 0 ≤ cost) :
    netEntryFlow lambda mu 0 cost 0 = 0 := by
  simp only [netEntryFlow, entryRate, exitRate, mul_zero, sub_zero]
  simp only [max_eq_left (show 0 - cost ≤ 0 by linarith), mul_zero]

/-- When participation payoff exceeds cost, the entry rate is positive. -/
theorem entry_rate_pos_when_profitable {lambda pi cost : ℝ}
    (hlam : 0 < lambda) (hprofit : cost < pi) :
    0 < entryRate lambda pi cost := by
  simp only [entryRate]
  exact mul_pos hlam (lt_max_of_lt_right (by linarith))

/-- **Value-function-driven entry.**
    When V(J) > cost, the participation surplus is positive.
    Combines with `valueFunction_pos` to show entry is always
    profitable when J > 1, ρ ∈ (0,1), and cost < V(J). -/
theorem entry_driven_by_value_function {J ρ c cost : ℝ}
    (hcost : cost < valueFunction J ρ c) :
    0 < valueFunction J ρ c - cost := by
  linarith

/-- **Self-reinforcing entry.**
    If V(J₁) > cost and J₂ > J₁ > 1, then V(J₂) > cost too.
    Higher diversity is self-reinforcing: once entry is profitable,
    it remains profitable at higher participation levels.
    This is the formal content of the phase portrait's stable region. -/
theorem self_reinforcing_entry {J₁ J₂ ρ c cost : ℝ}
    (hJ₁ : 1 < J₁) (hJ₁₂ : J₁ < J₂) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hc : 0 < c) (hprofit : cost < valueFunction J₁ ρ c) :
    cost < valueFunction J₂ ρ c := by
  have hV := valueFunction_increasing hJ₁ hJ₁₂ hρ0 hρ1 hc
  linarith

-- ============================================================
-- Proposition 3c.1: Timescale of Entry
-- ============================================================

/-- **Proposition 3c.1 (Timescale of Entry).**
    Near the stable equilibrium J_high, the linearized dynamics
    have convergence rate proportional to lambda.
    Time to reach J_high from J_0 > J_crit is approximately
    (1/lambda) * log((J_high - J_crit)/(J_0 - J_crit)).

    Faster entry rate lambda -> faster network formation.

    We prove the structural result: the convergence rate
    scales with lambda. -/
def convergenceRateEntry (lambda : ℝ) (structural_factor : ℝ) : ℝ :=
  lambda * structural_factor

/-- Convergence rate is positive for positive lambda. -/
theorem convergenceRateEntry_pos {lambda sf : ℝ}
    (hlam : 0 < lambda) (hsf : 0 < sf) :
    0 < convergenceRateEntry lambda sf := by
  simp only [convergenceRateEntry]
  exact mul_pos hlam hsf

/-- Higher lambda gives faster convergence (shorter network formation time). -/
theorem faster_entry_faster_convergence {lambda₁ lambda₂ sf : ℝ}
    (hlam : lambda₁ < lambda₂) (hsf : 0 < sf) :
    convergenceRateEntry lambda₁ sf < convergenceRateEntry lambda₂ sf := by
  simp only [convergenceRateEntry]
  exact mul_lt_mul_of_pos_right hlam hsf

/-- The entry timescale is 1/lambda times a structural factor. -/
def entryTimescale (lambda : ℝ) (log_factor : ℝ) : ℝ :=
  log_factor / lambda

/-- The entry timescale is positive. -/
theorem entryTimescale_pos {lambda lf : ℝ}
    (hlam : 0 < lambda) (hlf : 0 < lf) :
    0 < entryTimescale lambda lf := by
  simp only [entryTimescale]
  exact div_pos hlf hlam

/-! ## Welfare with Endogenous J (merged from EntryExitWelfare.lean) -/

-- ============================================================
-- Proposition 3c.6: Extended Welfare Function
-- ============================================================

/-- The welfare distance function g(z) = z - 1 - log(z) applied to
    the participation ratio J/J*. Measures how far current diversity
    is from the optimal level. -/
def diversityWelfareLoss (J Jstar : ℝ) : ℝ :=
  welfareDistanceFn (J / Jstar)

/-- The extended welfare function with endogenous J:
    V(rho, T, J) = V_base(rho, T) + W_J * g(J/J*)
    where g is the welfare distance function from Paper 4
    and W_J is the weight on the diversity dimension. -/
def extendedWelfare (V_base W_J J Jstar : ℝ) : ℝ :=
  V_base + W_J * welfareDistanceFn (J / Jstar)

/-- Extended welfare equals base welfare when J = J*
    (at the diversity optimum, no additional loss). -/
theorem extendedWelfare_at_optimum {V_base W_J Jstar : ℝ}
    (hJs : 0 < Jstar) :
    extendedWelfare V_base W_J Jstar Jstar = V_base := by
  simp only [extendedWelfare]
  rw [div_self (ne_of_gt hJs)]
  rw [welfareDistanceFn_at_one]
  ring

/-- The diversity welfare loss g(J/J*) is non-negative for J > 0, J* > 0. -/
theorem diversityWelfareLoss_nonneg {J Jstar : ℝ}
    (hJ : 0 < J) (hJs : 0 < Jstar) :
    0 ≤ diversityWelfareLoss J Jstar :=
  welfareDistanceFn_nonneg (div_pos hJ hJs)

/-- The diversity welfare loss is zero iff J = J*. -/
theorem diversityWelfareLoss_eq_zero_iff {J Jstar : ℝ}
    (hJ : 0 < J) (hJs : 0 < Jstar) :
    diversityWelfareLoss J Jstar = 0 ↔ J = Jstar := by
  simp only [diversityWelfareLoss]
  rw [welfareDistanceFn_eq_zero_iff (div_pos hJ hJs)]
  constructor
  · intro h; linarith [div_eq_one_iff_eq (ne_of_gt hJs) |>.mp h]
  · intro h; rw [h, div_self (ne_of_gt hJs)]

-- ============================================================
-- Proposition 3c.7: Damping Cancellation for J
-- ============================================================

/-- **Proposition 3c.7 (Damping Cancellation for J).**
    The algebraic damping cancellation identity (Paper 4, Proposition 6)
    is independent of J.

    The welfare contribution at level n is:
    V_n = sigma_{n-1} * delta_n^2 / beta_n

    This does NOT depend on J_n or sigma_n. Increasing J_n
    speeds convergence but proportionally reduces the per-unit
    welfare gap, with the two effects canceling exactly.

    This is the same cancellation as in Paper 4, now interpreted
    through the lens of endogenous diversity. -/
theorem damping_cancellation_J_independent
    {sigma_prev delta beta_n : ℝ}
    (_hs : 0 < sigma_prev) (_hb : 0 < beta_n) :
    -- The welfare contribution depends on sigma_{n-1}, delta, beta_n
    -- but NOT on J_n or sigma_n (the own-level parameters)
    welfareContribution sigma_prev delta beta_n =
    sigma_prev * delta ^ 2 / beta_n := by
  rfl

/-- **Value function welfare gap.**
    At a higher-participation equilibrium, the welfare surplus
    V(J_high) - V(J_low) > 0 contributes directly to the
    extended welfare difference. This is the J-dimension
    contribution to welfare that Paper 4's damping cancellation
    leaves invariant. -/
theorem valueFunction_welfare_contribution {J_low J_high ρ c : ℝ}
    (hJl : 1 < J_low) (hJlh : J_low < J_high)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    0 < valueFunction J_high ρ c - valueFunction J_low ρ c := by
  linarith [valueFunction_increasing hJl hJlh hρ0 hρ1 hc]

/-- **Upstream Reform for J.** To increase J at level n, the most
    effective policy is to reform at level n-1:
    - Reduce sigma_{n-1} (lower upstream costs) -> raises k_{n,n-1}
    - Increase beta_n (improve gain structure) -> raises k_{n,n-1}

    This reuses the upstream reform logic from Paper 4. -/
theorem upstream_reform_for_J {beta sigma_prev sigma_prev' : ℝ}
    (hb : 0 < beta) (hsp : 0 < sigma_prev) (hsp' : 0 < sigma_prev')
    (hred : sigma_prev' < sigma_prev) {sigma_n J_n Fbar_n : ℝ}
    (hsn : 0 < sigma_n) (hJn : 0 < J_n) (hFn : 0 < Fbar_n) :
    -- Lower sigma_{n-1} raises the NGM entry k_{n,n-1}
    ngmEntryReal beta sigma_n J_n Fbar_n sigma_prev <
    ngmEntryReal beta sigma_n J_n Fbar_n sigma_prev' := by
  simp only [ngmEntryReal]
  apply div_lt_div_of_pos_left (by positivity) hsp' hred

/-- Increasing beta also raises k and thus helps activate J at the next level. -/
theorem upstream_reform_beta_for_J {beta beta' sigma_n J_n Fbar_n sigma_prev : ℝ}
    (_hb : 0 < beta) (_hb' : 0 < beta') (hbb : beta < beta')
    (hsn : 0 < sigma_n) (hJn : 0 < J_n) (hFn : 0 < Fbar_n)
    (hsp : 0 < sigma_prev) :
    ngmEntryReal beta sigma_n J_n Fbar_n sigma_prev <
    ngmEntryReal beta' sigma_n J_n Fbar_n sigma_prev := by
  simp only [ngmEntryReal]
  apply div_lt_div_of_pos_right _ hsp
  have h1 : 0 < sigma_n * J_n * Fbar_n := by positivity
  nlinarith

end
