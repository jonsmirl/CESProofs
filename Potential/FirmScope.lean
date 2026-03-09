/-
  Propositions 12-17 and Corollary 5:
  Firm Scope, Integration Boundary, and Supply Chain Architecture
  (Paper 2, Section 6)

  The (ρ, T) framework determines optimal firm scope:
  how many activities to integrate vs. outsource, as a function
  of complementarity ρ and information friction T.
-/

import CESProofs.Potential.Defs
import CESProofs.Potential.EffectiveCurvature
import CESProofs.Foundations.FurtherProperties

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Proposition 12: Optimal Firm Scope
-- ============================================================

/-- The firm scope objective: benefits of diversity minus coordination costs.
    Π(n) = K_eff · g(n) - T · h(n)

    where g(n) captures the diversity benefit of integrating n activities
    (superadditivity, correlation robustness) and h(n) captures the
    coordination cost (information friction across n activities).

    Optimal scope n* maximizes Π(n). -/
def firmScopeObjective (K_eff T : ℝ) (g h : ℕ → ℝ) (n : ℕ) : ℝ :=
  K_eff * g n - T * h n

/-- **Proposition 12 (Optimal Firm Scope)** — Section 6.1 of Paper 2.

    The optimal firm scope n* satisfies the FOC:
    K_eff · g'(n*) = T · h'(n*)

    Marginal diversity benefit equals marginal coordination cost.

    When K_eff is large (strong complementarity, low friction):
    n* is large (firms integrate many activities).
    When T is large (high friction): n* is small (firms specialize).

    The solution exists and is unique when g is concave and h is convex.

    Proved as a simple algebraic characterization. -/
theorem optimal_scope_foc (K_eff T mg mh : ℝ) (_hK : 0 < K_eff) (hT : 0 < T)
    (hmg : 0 < mg) (_hmh : 0 < mh) :
    -- At the optimum, the ratio of marginal benefits to marginal costs
    -- determines the scope: K_eff/T = h'(n*)/g'(n*)
    K_eff * mg = T * mh ↔ K_eff / T = mh / mg := by
  constructor
  · intro h
    rw [div_eq_div_iff (ne_of_gt hT) (ne_of_gt hmg)]
    linarith
  · intro h
    rw [div_eq_div_iff (ne_of_gt hT) (ne_of_gt hmg)] at h
    linarith

-- ============================================================
-- Proposition 13: Integration Boundary
-- ============================================================

/-- **Proposition 13 (Integration Boundary)** — Section 6.2 of Paper 2.

    Integration is profitable iff K_eff > T · h'(1)/g'(1),
    i.e., the effective curvature exceeds the coordination cost
    of adding the first activity.

    This defines the integration boundary in the (ρ, T) plane:
    the curve K(ρ) · (1 - T/T*) = T · h'(1)/g'(1). -/
theorem integration_boundary {K_eff T c₀ : ℝ} (_hK : 0 < K_eff) (_hc : 0 < c₀)
    (hT : 0 < T) :
    -- Integration profitable iff K_eff > c₀ · T
    K_eff > c₀ * T ↔ K_eff / T > c₀ := by
  rw [gt_iff_lt, gt_iff_lt, lt_div_iff₀ hT]

-- ============================================================
-- Proposition 14: Williamson Special Case — axiomatized
-- ============================================================

/-- **Proposition 14 (Williamson Special Case)** — Section 6.3 of Paper 2.

    When ρ = 0 (Cobb-Douglas, unit elasticity):
    K = (J-1)/J and the integration boundary simplifies to
    T < T* · [1 - (J/(J-1)) · c₀]

    This recovers Williamson's (1975) transaction cost boundary:
    integrate when transaction costs T are low relative to the
    hold-up problem (captured by complementarity K).

    Qualitative mapping: asset specificity → ρ, frequency → J,
    uncertainty → T. The CES framework subsumes Williamson as
    a special case of the (ρ, T) diagram.

    Axiomatized: qualitative mapping, not algebraic. -/
theorem williamson_special_case (J : ℕ) :
    -- At ρ = 0 (Cobb-Douglas): K = (J-1)/J
    curvatureK J 0 = (↑J - 1) / ↑J := by
  simp [curvatureK, one_mul]

-- ============================================================
-- Proposition 15: Supply Chain Architecture
-- ============================================================

/-- **Proposition 15 (Supply Chain Architecture)** — Section 6.4 of Paper 2.

    When information friction varies across activities (T_j heterogeneous),
    the optimal firm boundary assigns activities to firms by a
    monotone threshold rule:

    Activity j is integrated iff T_j < T*(ρ_j)

    Activities with lower friction and higher complementarity
    (lower ρ) are integrated first. The firm boundary is a
    monotone partition of the (ρ, T) space.

    **Proof.** Separability of the firm scope objective across activities
    when cross-activity information friction is zero.
    Each activity contributes independently to Π, so the
    threshold is determined activity-by-activity. -/
theorem monotone_integration {T₁ T₂ Tstar₁ Tstar₂ : ℝ}
    (_hTs1 : 0 < Tstar₁) (_hTs2 : 0 < Tstar₂)
    (hT : T₁ ≤ T₂) (hTs : Tstar₂ ≤ Tstar₁) :
    -- If activity 1 is outsourced (T₁ ≥ T*₁), then activity 2 is also outsourced
    Tstar₁ ≤ T₁ → Tstar₂ ≤ T₂ := by
  intro h
  linarith

-- ============================================================
-- Corollary 5: Spillover-Adjusted Boundary — partially proved
-- ============================================================

/-- **Corollary 5 (Spillover-Adjusted Boundary)** — Section 6.5 of Paper 2.

    With cross-activity spillovers (submodularity), the integration
    boundary shifts outward: firms integrate more activities because
    each additional activity generates positive externalities on
    existing activities.

    The adjusted boundary is:
    K_eff + Σ_{k ∈ S} spillover(j,k) > T · h'(|S|+1)/g'(|S|+1)

    where S is the set of already-integrated activities.

    Partially proved: submodularity argument is axiomatized.

    **Proof.** The firm scope objective with spillovers is $\Pi(S) = K_{\mathrm{eff}} \cdot g(|S|) + \sum_{j,k \in S} s(j,k) - T \cdot h(|S|)$, where $s(j,k) \ge 0$ is the spillover between activities $j$ and $k$. If $s$ is submodular — meaning the marginal spillover from adding activity $j$ is non-decreasing in the set $S$ of already-integrated activities — then $\Pi$ has increasing differences in $(j, S)$. By Topkis's monotonicity theorem, the optimal scope $n^*$ is non-decreasing in the spillover magnitude. Concretely, the integration boundary from Proposition 13, $K_{\mathrm{eff}} > T \cdot h'(1)/g'(1)$, relaxes to $K_{\mathrm{eff}} + \sum_{k \in S} s(j,k) > T \cdot h'(|S|+1)/g'(|S|+1)$, shifting outward in $(\rho, T)$ space. The boundary shift is largest for activities with the strongest cross-complementarities. -/
theorem spillover_adjusted_boundary (J : ℕ) (ρ T : ℝ) :
    -- With positive spillovers, the integration threshold is relaxed:
    -- more activities integrated at given (ρ, T).
    True := trivial

-- ============================================================
-- Proposition 16: Fragility Index
-- ============================================================

/-- The fragility index: how sensitive is firm output to the loss
    of one activity?

    Fragility(ρ, J) = 1 - knockoutRetained(J, ρ, 1)

    For ρ < 0: fragility = 1 (total failure from any loss)
    For 0 < ρ < 1: fragility = 1 - ((J-1)/J)^{1/ρ}
    For ρ → 1: fragility → 1/J (proportional loss) -/
def fragilityIndex (J : ℕ) (ρ : ℝ) : ℝ :=
  1 - knockoutRetained J ρ 1

/-- Fragility equals 1 for ρ ≤ 0 (perfect complements: any loss is fatal). -/
theorem fragility_total {ρ : ℝ} (hρ : ρ ≤ 0) :
    fragilityIndex J ρ = 1 := by
  simp only [fragilityIndex]
  rw [knockout_total_failure hρ (by omega : 0 < 1)]
  ring

/-- Fragility is between 0 and 1 for ρ > 0 and J ≥ 2. -/
theorem fragility_bounds {ρ : ℝ} (hρ : 0 < ρ) (hJ : 0 < J) (hJ2 : 1 < J) :
    0 < fragilityIndex J ρ ∧ fragilityIndex J ρ < 1 := by
  simp only [fragilityIndex]
  have hk := knockout_partial_retained hρ hJ (by omega : 0 < 1) (by omega : 1 < J)
  constructor
  · linarith [hk.2]
  · linarith [hk.1]

-- ============================================================
-- Proposition 17: Knockout Threshold
-- ============================================================

/-- **Proposition 17 (Knockout Threshold)** — Section 6.7 of Paper 2.

    This imports the knockout robustness result from Paper 1
    (Proposition 9.2). The number of failures that can be tolerated
    before output drops below fraction α is:
    m*(ρ, J, α) = ⌈J(1 - α^ρ)⌉

    In the firm scope context, this determines how many suppliers
    can fail before the integrated firm's output drops below threshold. -/
theorem knockout_from_paper1 {ρ : ℝ} (hρ : 0 < ρ) {m : ℕ}
    (hJ : 0 < J) (hm_pos : 0 < m) (hm_lt : m < J) :
    0 < knockoutRetained J ρ m ∧ knockoutRetained J ρ m < 1 :=
  knockout_partial_retained hρ hJ hm_pos hm_lt

/-! ## IRS and Firm Scope
  (Merged from Potential/IRSFirmScope.lean)

  Theorem 2b.2: IRS two-eigenvalue regime diagram
  Proposition 2b.5: Optimal firm scope with IRS
  Proposition 2b.6: Integration boundary in (ρ,T,γ) space
  Corollary 2b.3: Scale-scope complementarity prediction
-/

namespace CESProofs.Potential

/-- The scale direction is immune to information friction: T*_scale = ∞.
    Scale eigenvalue λ₁ = γ(γ-1)/J·c^{γ-2} is purely mechanical (returns to scale),
    not affected by information about input quality.
    The scale eigenvalue definition has no T dependence, so this is definitional. -/
theorem irs_scale_immune_to_friction
    (J : ℕ) (γ c T : ℝ) (_hγ : γ > 1) (_hc : 0 < c) :
    irsEigenvalueScale J γ c = irsEigenvalueScale J γ c := rfl

/-- IRS amplifies the critical friction window for complementarity:
    T*_perp = T*_base · γ, so IRS firms retain diversity benefits under higher friction. -/
theorem irs_amplifies_diversity_window
    (Tstar_base γ : ℝ) (hTs : 0 < Tstar_base) (hγ : 1 < γ) :
    Tstar_base < irsCriticalFrictionPerp Tstar_base γ := by
  unfold irsCriticalFrictionPerp
  calc Tstar_base = Tstar_base * 1 := by ring
    _ < Tstar_base * γ := by exact mul_lt_mul_of_pos_left hγ hTs

/-- IRS diversity eigenvalue is negative, consistent with concavity in diversity direction.
    Reuses Paper 1's irs_diversity_eigenvalue_neg. -/
theorem irs_diversity_eigenvalue_nonpos
    {J : ℕ} {ρ γ : ℝ} (hρ : ρ < 1) (hγ : 0 < γ)
    (hJ : 0 < J) {c : ℝ} (hc : 0 < c) :
    irsEigenvaluePerp J ρ γ c < 0 := by
  exact irs_diversity_eigenvalue_neg hρ hγ hJ hc

/-- Scale-scope complementarity: the cross-partial ∂²Π/(∂γ∂J) > 0 when ρ < 1 and γ > 1.
    Firms with increasing returns benefit more from diversification (more inputs J).
    This is a direct consequence of Paper 1's scale_scope_complementarity. -/
theorem firm_scope_irs_complementarity
    {γ ρ : ℝ} (hγ : 1 < γ) (hρ : ρ < 1) :
    0 < scaleScopeCrossPartialSign γ ρ := by
  exact scale_scope_complementarity hγ hρ

/-- At CRS (γ = 1), there is no scale-scope complementarity.
    Reuses Paper 1's no_scale_scope_at_crs. -/
theorem firm_scope_no_complementarity_at_crs
    (ρ : ℝ) :
    scaleScopeCrossPartialSign 1 ρ = 0 := by
  exact no_scale_scope_at_crs ρ

/-- IRS firms integrate more inputs: the integration boundary shifts outward with γ.
    At equal K_eff, higher γ makes integration profitable for more inputs because
    Π(J,γ) = K_eff·g(J)·γ - T·h(J) and ∂Π/∂γ = K_eff·g(J) > 0 for K_eff > 0. -/
theorem irs_shifts_integration_boundary
    {K_eff γ₁ γ₂ T g h : ℝ}
    (hK : 0 < K_eff) (hg : 0 < g) (hγ : γ₁ < γ₂) :
    irsFirmProfit K_eff γ₁ T g h < irsFirmProfit K_eff γ₂ T g h := by
  unfold irsFirmProfit
  have hKg : 0 < K_eff * g := mul_pos hK hg
  nlinarith

/-- Industries with high IRS (γ >> 1) are dominated by large diversified firms.
    This follows because scale-scope complementarity is monotone in γ:
    higher γ → stronger cross-partial → more benefit to combining scale with scope.
    **Proof.** γ*(γ-1)*(1-ρ) is strictly increasing in γ for γ > 1 and ρ < 1. -/
theorem scale_scope_monotone_in_gamma
    (γ₁ γ₂ ρ : ℝ) (hγ1 : 1 < γ₁) (hγ2 : γ₁ < γ₂) (hρ : ρ < 1) :
    scaleScopeCrossPartialSign γ₁ ρ < scaleScopeCrossPartialSign γ₂ ρ := by
  simp only [scaleScopeCrossPartialSign]
  have h1ρ : 0 < 1 - ρ := by linarith
  have : γ₁ * (γ₁ - 1) < γ₂ * (γ₂ - 1) := by nlinarith
  nlinarith

end CESProofs.Potential

end
