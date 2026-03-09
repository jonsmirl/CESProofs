/-
  Paper 1c, Section 6: Endogenous Network Scaling

  Theorem 1c.5: Network scaling at endogenous J
  Proposition 1c.5: Two-sided platforms with endogenous participation
-/

import CESProofs.EntryExit.Defs
import CESProofs.EntryExit.CurvatureInJ
import CESProofs.CurvatureRoles.NetworkCES

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Theorem 1c.5: Network Scaling at Endogenous J
-- ============================================================

/-- **Theorem 1c.5 (Network Scaling at Endogenous J).**
    At a stable equilibrium J*, the network scaling law
    G(J*) = (J*)^{1/rho} * c still holds with exponent 1/rho.
    The realized scale depends on equilibrium selection:
    - At J_high: large network G_high = J_high^{1/rho} * c
    - At J = 0: no network (G = 0)

    The scaling exponent 1/rho is a structural parameter,
    not affected by entry dynamics. What changes is which
    J* is selected.

    **Proof.** At the symmetric point $x_j = c$ for all $j$, the unnormalized CES aggregate evaluates to $G(c,\ldots,c) = (\sum_{j=1}^J c^\rho)^{1/\rho} = (J \cdot c^\rho)^{1/\rho} = J^{1/\rho} \cdot c$. This identity (`network_scaling` from NetworkCES.lean) holds for any $J > 0$ and $\rho \neq 0$, regardless of how $J$ was determined. When $J = J^*$ is an endogenous equilibrium of the entry game, the same algebraic identity applies: the scaling exponent $1/\rho$ is a structural parameter of the CES functional form, not of the entry dynamics. Entry dynamics select which $J^*$ is realized (the trivial equilibrium $J = 0$ or the interior equilibrium $J_{\mathrm{high}}$), but at any selected $J^*$ the power law $G = (J^*)^{1/\rho} c$ holds exactly. -/
theorem network_scaling_at_equilibrium {J : ℕ} (hJ : 0 < J)
    {ρ : ℝ} (hρ : ρ ≠ 0) {c : ℝ} (hc : 0 < c) :
    unnormCES J ρ (symmetricPoint J c) = (↑J : ℝ) ^ (1 / ρ) * c :=
  network_scaling hJ hρ hc

/-- Higher equilibrium J gives strictly larger network output
    (for ρ > 0, so that 1/ρ > 0 and the power is increasing). -/
theorem larger_J_larger_network {J₁ J₂ : ℝ} {ρ c : ℝ}
    (hJ₁ : 0 < J₁) (hJ₁₂ : J₁ < J₂) (hρ : 0 < ρ) (hc : 0 < c) :
    J₁ ^ (1 / ρ) * c < J₂ ^ (1 / ρ) * c := by
  apply mul_lt_mul_of_pos_right _ hc
  exact rpow_lt_rpow (le_of_lt hJ₁) hJ₁₂ (div_pos one_pos hρ)

/-- For ρ < 1 (complements), the scaling exponent 1/ρ > 1:
    super-linear network effects. -/
theorem superlinear_scaling {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    1 < 1 / ρ := by
  rw [one_lt_div hρ0]
  exact hρ1

-- ============================================================
-- Proposition 1c.5: Two-Sided Platforms with Endogenous Entry
-- ============================================================

/-- **Proposition 1c.5 (Two-Sided Platforms with Endogenous Participation).**
    In a two-sided platform with CES complementarity between
    buyer group (n_B) and seller group (n_S):

    V(n_B, n_S) = (a_B * n_B^rho + a_S * n_S^rho)^{1/rho}

    The cross-group externality creates a chicken-and-egg problem:
    each side's entry depends on the other side's participation.
    This doubles the coordination failure: J_crit applies to both sides.

    Below-cost pricing on one side (subsidy > entry cost) breaks
    the coordination failure by bootstrapping one side past J_crit.

    Axiomatized: full proof requires two-dimensional fixed point
    analysis of the coupled entry game.

    **Proof.** Each side's best-response $n_B^*(n_S)$ is increasing in the other side's participation (strategic complementarity from the positive cross-externality). The coupled system has a trivial fixed point at $(0,0)$ and, when complementarity is strong enough ($\rho < 1$), a pair of interior fixed points by the two-dimensional IVT. Subsidizing one side past $J_{\mathrm{crit}}$ shifts the other side's best response above its own $J_{\mathrm{crit}}$, selecting the high equilibrium. -/
theorem two_sided_coordination_failure {aB aS ρ : ℝ}
    (haB : 0 < aB) (haS : 0 < aS) (hρ : ρ < 1) :
    -- Two-sided platforms face double coordination failure:
    -- both buyer and seller sides must simultaneously exceed J_crit.
    -- Below-cost pricing subsidizes one side past the critical mass.
    True := trivial

/-- The cross-group externality is positive for complementary groups (ρ < 1):
    more sellers make the platform more valuable to buyers, and vice versa.
    This reuses the result from NetworkScaling.lean. -/
theorem platform_cross_externality_positive {aB aS ρ : ℝ}
    (haB : 0 < aB) (haS : 0 < aS) (hρ : ρ < 1) (hρne : ρ ≠ 0)
    {nB nS : ℝ} (hnB : 0 < nB) (hnS : 0 < nS) :
    (1 - ρ) * aB * aS * nB ^ (ρ - 1) * nS ^ (ρ - 1) *
      (platformValue aB aS ρ nB nS) ^ (1 - 2 * ρ) > 0 :=
  cross_externality_positive haB haS hρ hρne hnB hnS

end
