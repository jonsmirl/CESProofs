/-
  Growth and Dynamic Tax Revenue (Layer 4-5 of Macro Extension)

  Builds on TaxStructure.lean to model the growth effects of taxation
  and the NPV of tax revenue on a balanced growth path.

  Key components:
  - Growth rate under taxation: g(τ) = g₀ · (1 - β·τ)
  - Investment rate declining with tax: s(τ) = s₀ · (1 - ψ·τ)
  - Discount gap: D(τ) = D₀ + δ·τ (NPV convergence condition)
  - NPV of tax revenue: NPV = R(τ) / D(τ)
  - Central result: τ*_NPV < τ*_static (the capstone theorem)

  All proofs are algebraic — no axioms, no sorry.
-/

import CESProofs.Macro.TaxStructure

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Growth and Investment Definitions
-- ============================================================

/-- Growth rate under taxation: g(τ) = g₀ · (1 - β·τ).
    g₀ is the baseline growth rate (at τ=0), and β ∈ [0,1] is the
    growth sensitivity to taxation. β=0 gives the Solow case (tax
    has no growth effect); β>0 gives the endogenous growth case
    where taxation reduces the incentive to invest in innovation. -/
def growthRate (g₀ β τ : ℝ) : ℝ := g₀ * (1 - β * τ)

/-- Investment/savings rate declining with taxation:
    s(τ) = s₀ · (1 - ψ·τ) where ψ is the investment sensitivity
    to the tax rate. ψ=0 means investment is tax-insensitive;
    ψ>0 means higher taxes crowd out private investment. -/
def investmentRate (s₀ ψ τ : ℝ) : ℝ := s₀ * (1 - ψ * τ)

/-- Discount gap: D(τ) = D₀ + δ_gap·τ where D₀ = r₀ - g₀ is the
    baseline gap between the return on capital and the growth rate,
    and δ_gap captures how taxation widens this gap (both by raising
    required returns and by lowering growth).

    NPV of a perpetual revenue stream is well-defined iff D(τ) > 0.
    The subscript distinguishes δ_gap from the depreciation rate δ. -/
def discountGap (D₀ δ_gap τ : ℝ) : ℝ := D₀ + δ_gap * τ

/-- NPV of tax revenue on a balanced growth path:
    NPV(τ) = R(τ) / D(τ) = lafferRevenue(B₀, η, τ) / discountGap(D₀, δ_gap, τ).

    This is the present value of the entire future tax revenue stream
    when both revenue and the discount rate depend on the tax rate.
    The key insight: the denominator increases with τ (wider discount gap),
    so the NPV-maximizing rate is below the static Laffer peak. -/
def npvRevenue (B₀ η D₀ δ_gap τ : ℝ) : ℝ :=
  lafferRevenue B₀ η τ / discountGap D₀ δ_gap τ

/-- Solow level effect: the steady-state capital-output ratio under
    taxation, K/Y = s(τ)/δ, declining in τ. Uses the investment rate
    function and the depreciation rate δ. -/
def levelEffect (s₀ ψ δ τ : ℝ) : ℝ :=
  investmentRate s₀ ψ τ / δ

/-- Growth drag: the marginal reduction in growth rate per unit
    increase in the tax rate. growthDrag = g₀ · β. -/
def growthDrag (g₀ β : ℝ) : ℝ := g₀ * β

/-- Dynamic wedge: the NPV loss from the widening discount gap
    at tax rate τ. This is the additional cost of taxation beyond
    the static Laffer revenue loss.
    dynamicWedge = R(τ) · δ_gap / D(τ)². -/
def dynamicWedge (B₀ η D₀ δ_gap τ : ℝ) : ℝ :=
  lafferRevenue B₀ η τ * δ_gap / (discountGap D₀ δ_gap τ) ^ 2

/-- The explicit bound on how far below the Laffer peak the NPV
    optimum lies. ε = δ_gap / (8 · η² · D*) where D* = D₀ + δ_gap/(2η).
    This gives a constructive witness for the central theorem. -/
def npvOptimalBound (η D₀ δ_gap : ℝ) : ℝ :=
  δ_gap / (8 * η ^ 2 * (D₀ + δ_gap / (2 * η)))

/-- Output at time t on a balanced growth path:
    Y(t) = Y₀ · (1 + g)^t.
    Used for the NPV interpretation: NPV = Σ R(t)/(1+r)^t. -/
def balancedGrowthOutput (Y₀ g : ℝ) (t : ℕ) : ℝ :=
  Y₀ * (1 + g) ^ t

-- ============================================================
-- Section 2: Growth Rate Properties
-- ============================================================

/-- Growth rate is positive when g₀ > 0 and β·τ < 1. -/
theorem growthRate_pos {g₀ β τ : ℝ} (hg : 0 < g₀)
    (hbτ : β * τ < 1) :
    0 < growthRate g₀ β τ := by
  simp only [growthRate]
  exact mul_pos hg (by linarith)

/-- Growth rate at zero tax equals the baseline rate. -/
theorem growthRate_at_zero_tax {g₀ β : ℝ} :
    growthRate g₀ β 0 = g₀ := by
  simp only [growthRate]; ring

/-- Growth rate is decreasing in the tax rate when β > 0 and g₀ > 0.

    **Proof.** The growth rate $g(\tau) = g_0(1 - \beta\tau)$ is affine in $\tau$ with slope $-g_0\beta < 0$. For $\tau_1 < \tau_2$, we have $\beta\tau_1 < \beta\tau_2$, hence $1 - \beta\tau_2 < 1 - \beta\tau_1$, and multiplying by $g_0 > 0$ gives $g(\tau_2) < g(\tau_1)$. -/
theorem growthRate_decreasing {g₀ β τ₁ τ₂ : ℝ}
    (hg : 0 < g₀) (hβ : 0 < β) (hτ : τ₁ < τ₂) :
    growthRate g₀ β τ₂ < growthRate g₀ β τ₁ := by
  simp only [growthRate]
  have h1 : β * τ₁ < β * τ₂ := mul_lt_mul_of_pos_left hτ hβ
  have h2 : 1 - β * τ₂ < 1 - β * τ₁ := by linarith
  exact mul_lt_mul_of_pos_left h2 hg

/-- In the Solow case (β = 0), tax has no growth effect: g(τ) = g₀. -/
theorem growthRate_solow_constant {g₀ τ : ℝ} :
    growthRate g₀ 0 τ = g₀ := by
  simp only [growthRate]; ring

/-- Investment rate is positive when s₀ > 0 and ψ·τ < 1. -/
theorem investmentRate_pos {s₀ ψ τ : ℝ} (hs : 0 < s₀)
    (hψτ : ψ * τ < 1) :
    0 < investmentRate s₀ ψ τ := by
  simp only [investmentRate]
  exact mul_pos hs (by linarith)

/-- Investment rate is decreasing in the tax rate when ψ > 0 and s₀ > 0. -/
theorem investmentRate_decreasing {s₀ ψ τ₁ τ₂ : ℝ}
    (hs : 0 < s₀) (hψ : 0 < ψ) (hτ : τ₁ < τ₂) :
    investmentRate s₀ ψ τ₂ < investmentRate s₀ ψ τ₁ := by
  simp only [investmentRate]
  have h1 : ψ * τ₁ < ψ * τ₂ := mul_lt_mul_of_pos_left hτ hψ
  have h2 : 1 - ψ * τ₂ < 1 - ψ * τ₁ := by linarith
  exact mul_lt_mul_of_pos_left h2 hs

/-- Level effect (K/Y) is decreasing in the tax rate when ψ > 0. -/
theorem levelEffect_decreasing {s₀ ψ δ τ₁ τ₂ : ℝ}
    (hs : 0 < s₀) (hψ : 0 < ψ) (hδ : 0 < δ) (hτ : τ₁ < τ₂) :
    levelEffect s₀ ψ δ τ₂ < levelEffect s₀ ψ δ τ₁ := by
  simp only [levelEffect]
  exact div_lt_div_of_pos_right (investmentRate_decreasing hs hψ hτ) hδ

/-- Level effect equals the Solow steady-state K/Y with tax-adjusted savings. -/
theorem levelEffect_links_solow {s₀ ψ δ τ : ℝ} :
    levelEffect s₀ ψ δ τ = steadyStateKY (investmentRate s₀ ψ τ) δ := by
  simp only [levelEffect, steadyStateKY]

-- ============================================================
-- Section 3: Discount Gap Properties
-- ============================================================

/-- Discount gap is positive when D₀ > 0, δ_gap ≥ 0, and τ ≥ 0. -/
theorem discountGap_pos {D₀ δ_gap τ : ℝ} (hD : 0 < D₀)
    (hδ : 0 ≤ δ_gap) (hτ : 0 ≤ τ) :
    0 < discountGap D₀ δ_gap τ := by
  simp only [discountGap]
  have : 0 ≤ δ_gap * τ := mul_nonneg hδ hτ
  linarith

/-- Discount gap at zero tax equals the baseline gap. -/
theorem discountGap_at_zero_tax {D₀ δ_gap : ℝ} :
    discountGap D₀ δ_gap 0 = D₀ := by
  simp only [discountGap]; ring

/-- Discount gap is increasing in the tax rate when δ_gap > 0. -/
theorem discountGap_increasing {D₀ δ_gap τ₁ τ₂ : ℝ}
    (hδ : 0 < δ_gap) (hτ : τ₁ < τ₂) :
    discountGap D₀ δ_gap τ₁ < discountGap D₀ δ_gap τ₂ := by
  simp only [discountGap]
  linarith [mul_lt_mul_of_pos_left hτ hδ]

/-- Discount gap sensitivity interpretation: δ_gap = γ + g₀·β
    where γ is the tax effect on required returns and g₀·β is the
    growth drag. Even in the Solow model (β=0), δ_gap > 0 if
    taxes raise required returns (γ > 0). -/
theorem discountGap_sensitivity {γ g₀ β τ : ℝ} :
    discountGap (γ + g₀ * β) (γ + g₀ * β) τ =
    (γ + g₀ * β) * (1 + τ) := by
  simp only [discountGap]; ring

/-- Even in the Solow case (β=0), the discount gap can be dynamic
    if taxes raise required returns (γ > 0). -/
theorem discountGap_solow_still_dynamic {D₀ γ τ : ℝ} (hγ : 0 < γ)
    (hτ : 0 < τ) :
    D₀ < discountGap D₀ γ τ := by
  simp only [discountGap]
  linarith [mul_pos hγ hτ]

-- ============================================================
-- Section 4: NPV Revenue Properties
-- ============================================================

/-- NPV revenue is positive under standard conditions. -/
theorem npvRevenue_pos {B₀ η D₀ δ_gap τ : ℝ}
    (hB : 0 < B₀) (_hη : 0 < η) (hτ : 0 < τ) (hτu : η * τ < 1)
    (hD : 0 < D₀) (hδ : 0 ≤ δ_gap) :
    0 < npvRevenue B₀ η D₀ δ_gap τ := by
  simp only [npvRevenue]
  have hR : 0 < lafferRevenue B₀ η τ := by
    simp only [lafferRevenue]
    have h1 : 0 < 1 - η * τ := by linarith
    have h2 : 0 < τ * B₀ := mul_pos hτ hB
    nlinarith [mul_pos h2 h1]
  exact div_pos hR (discountGap_pos hD hδ (le_of_lt hτ))

/-- NPV of zero tax rate is zero (no revenue). -/
theorem npvRevenue_zero_rate {B₀ η D₀ δ_gap : ℝ} :
    npvRevenue B₀ η D₀ δ_gap 0 = 0 := by
  simp only [npvRevenue, lafferRevenue, discountGap]; ring

/-- NPV is increasing in the tax base (holding discount gap fixed). -/
theorem npvRevenue_increasing_in_base {B₀₁ B₀₂ η D₀ δ_gap τ : ℝ}
    (hD : 0 < discountGap D₀ δ_gap τ)
    (hτ : 0 < τ) (hτu : η * τ < 1) (hB : B₀₁ < B₀₂) :
    npvRevenue B₀₁ η D₀ δ_gap τ < npvRevenue B₀₂ η D₀ δ_gap τ := by
  simp only [npvRevenue]
  apply div_lt_div_of_pos_right _ hD
  simp only [lafferRevenue]
  have h1 : 0 < 1 - η * τ := by linarith
  have h2 : 0 < τ * (1 - η * τ) := mul_pos hτ h1
  nlinarith [mul_lt_mul_of_pos_right hB h2]

/-- NPV is decreasing in the discount gap (holding revenue fixed). -/
theorem npvRevenue_decreasing_in_D {B₀ η D₀ δ₁ δ₂ τ : ℝ}
    (hR : 0 < lafferRevenue B₀ η τ)
    (hD₁ : 0 < discountGap D₀ δ₁ τ)
    (hδ : δ₁ < δ₂) (hτ : 0 < τ) :
    npvRevenue B₀ η D₀ δ₂ τ < npvRevenue B₀ η D₀ δ₁ τ := by
  simp only [npvRevenue]
  apply div_lt_div_of_pos_left hR hD₁
  simp only [discountGap]
  linarith [mul_lt_mul_of_pos_right hδ hτ]

/-- NPV cross-comparison: NPV₁ > NPV₂ iff R₁ · D₂ > R₂ · D₁. -/
theorem npvRevenue_cross_comparison {B₀ η D₀ δ_gap τ₁ τ₂ : ℝ}
    (hD₁ : 0 < discountGap D₀ δ_gap τ₁)
    (hD₂ : 0 < discountGap D₀ δ_gap τ₂)
    (hR₁D₂ : lafferRevenue B₀ η τ₁ * discountGap D₀ δ_gap τ₂ >
              lafferRevenue B₀ η τ₂ * discountGap D₀ δ_gap τ₁) :
    npvRevenue B₀ η D₀ δ_gap τ₂ < npvRevenue B₀ η D₀ δ_gap τ₁ := by
  simp only [npvRevenue]
  rw [div_lt_div_iff₀ hD₂ hD₁]
  linarith

/-- When δ_gap = 0 (no dynamic effect on the discount gap),
    the NPV peak coincides with the static Laffer peak. -/
theorem npv_no_dynamic_equals_static {B₀ η D₀ τ : ℝ} :
    npvRevenue B₀ η D₀ 0 τ = lafferRevenue B₀ η τ / D₀ := by
  simp only [npvRevenue, discountGap]; ring

/-- In the Solow case with no dynamic discount effect,
    NPV is just the static Laffer revenue divided by the constant gap. -/
theorem npv_solow_level_only {B₀ η D₀ τ : ℝ} :
    npvRevenue B₀ η D₀ 0 τ = lafferRevenue B₀ η τ / D₀ :=
  npv_no_dynamic_equals_static

-- ============================================================
-- Section 5: The Central Result — NPV Peak Below Laffer Peak
-- ============================================================

/-- **Laffer symmetry**: Revenue at symmetric points around the peak
    are equal: R(τ* - ε) = R(τ* + ε). This follows because
    R(τ) = B₀·(τ - η·τ²) is a parabola symmetric about τ* = 1/(2η). -/
theorem lafferRevenue_symmetric {B₀ η ε : ℝ} (hη : η ≠ 0) :
    lafferRevenue B₀ η (lafferPeak η - ε) =
    lafferRevenue B₀ η (lafferPeak η + ε) := by
  simp only [lafferRevenue, lafferPeak]
  field_simp
  ring

/-- Laffer revenue at the peak minus ε is positive when
    0 < ε < 1/(2η) and B₀ > 0 and η > 0. -/
theorem lafferRevenue_pos_near_peak {B₀ η ε : ℝ}
    (hB : 0 < B₀) (hη : 0 < η) (hε : 0 < ε) (hε_small : ε < lafferPeak η) :
    0 < lafferRevenue B₀ η (lafferPeak η - ε) := by
  have hτ_pos : 0 < lafferPeak η - ε := by
    have := lafferPeak_pos hη; linarith
  simp only [lafferRevenue, lafferPeak]
  have hη_ne : η ≠ 0 := ne_of_gt hη
  have h_factor : 1 - η * (1 / (2 * η) - ε) = 1 / 2 + η * ε := by field_simp; ring
  rw [h_factor]
  have h1 : 0 < 1 / 2 + η * ε := by positivity
  have h2 : 0 < 1 / (2 * η) - ε := by
    simp only [lafferPeak] at hε_small; linarith
  positivity

/-- **NPV left dominates right**: Among two tax rates equidistant from
    the Laffer peak, the lower one has higher NPV when δ_gap > 0. -/
theorem npv_left_dominates_right {B₀ η D₀ δ_gap ε : ℝ}
    (hB : 0 < B₀) (hη : 0 < η)
    (hε : 0 < ε) (hε_small : ε < lafferPeak η)
    (hD : 0 < D₀) (hδ_nn : 0 ≤ δ_gap) (hδ : 0 < δ_gap) :
    npvRevenue B₀ η D₀ δ_gap (lafferPeak η + ε) <
    npvRevenue B₀ η D₀ δ_gap (lafferPeak η - ε) := by
  simp only [npvRevenue]
  rw [← lafferRevenue_symmetric (ne_of_gt hη)]
  have hR : 0 < lafferRevenue B₀ η (lafferPeak η - ε) :=
    lafferRevenue_pos_near_peak hB hη hε hε_small
  have hD₁ : 0 < discountGap D₀ δ_gap (lafferPeak η - ε) := by
    apply discountGap_pos hD hδ_nn
    linarith [lafferPeak_pos hη]
  exact div_lt_div_of_pos_left hR hD₁
    (discountGap_increasing hδ (by linarith))

/-- The explicit ε bound is positive when η > 0, D₀ > 0, δ_gap > 0. -/
theorem npvOptimalBound_pos {η D₀ δ_gap : ℝ}
    (hη : 0 < η) (hD : 0 < D₀) (hδ : 0 < δ_gap) :
    0 < npvOptimalBound η D₀ δ_gap := by
  simp only [npvOptimalBound]
  apply div_pos hδ
  apply mul_pos (by positivity : (0:ℝ) < 8 * η ^ 2)
  linarith [div_pos hδ (show (0:ℝ) < 2 * η by linarith)]

/-- The NPV optimal rate τ₁ = lafferPeak η - ε is still positive
    (i.e., ε < τ*), ensuring a meaningful interior optimum. -/
theorem npvOptimalBound_below_peak {η D₀ δ_gap : ℝ}
    (hη : 0 < η) (hD : 0 < D₀) (hδ : 0 < δ_gap) :
    npvOptimalBound η D₀ δ_gap < lafferPeak η := by
  simp only [npvOptimalBound, lafferPeak]
  have hη_ne : η ≠ 0 := ne_of_gt hη
  have h2η : (0:ℝ) < 2 * η := by linarith
  have hDstar : (0:ℝ) < D₀ + δ_gap / (2 * η) := by
    linarith [div_pos hδ h2η]
  have hden : (0:ℝ) < 8 * η ^ 2 * (D₀ + δ_gap / (2 * η)) := by positivity
  rw [div_lt_div_iff₀ hden h2η]
  have key : 8 * η ^ 2 * (D₀ + δ_gap / (2 * η)) =
      8 * η ^ 2 * D₀ + 4 * η * δ_gap := by field_simp; ring
  nlinarith [key, mul_pos hη hD, mul_pos hη hδ, sq_pos_of_pos hη]

/-- **THE CENTRAL THEOREM**: The NPV-maximizing tax rate is strictly
    below the static Laffer peak.

    There exists τ₁ < τ* = 1/(2η) such that NPV(τ₁) > NPV(τ*).

    Proof strategy: Take τ₁ = τ* - ε where ε = npvOptimalBound.
    Unfold all definitions to rational expressions, clear denominators
    with field_simp, then close the polynomial inequality with nlinarith. -/
theorem npv_suboptimal_at_laffer_peak {B₀ η D₀ δ_gap : ℝ}
    (hB : 0 < B₀) (hη : 0 < η)
    (hD : 0 < D₀) (hδ : 0 < δ_gap) :
    ∃ τ₁ : ℝ, τ₁ < lafferPeak η ∧
      npvRevenue B₀ η D₀ δ_gap (lafferPeak η) <
      npvRevenue B₀ η D₀ δ_gap τ₁ := by
  use lafferPeak η - npvOptimalBound η D₀ δ_gap
  have hε_pos := npvOptimalBound_pos hη hD hδ
  have hε_small := npvOptimalBound_below_peak hη hD hδ
  refine ⟨by linarith, ?_⟩
  -- Show NPV(τ*) < NPV(τ₁) via cross-multiplication
  simp only [npvRevenue]
  have hη_ne : η ≠ 0 := ne_of_gt hη
  have h2η_pos : (0:ℝ) < 2 * η := by linarith
  have hDstar_pos : (0:ℝ) < D₀ + δ_gap / (2 * η) := by positivity
  have h8η2D_pos : (0:ℝ) < 8 * η ^ 2 * (D₀ + δ_gap / (2 * η)) := by positivity
  -- Positivity of discount gaps
  have hD₁ : 0 < discountGap D₀ δ_gap (lafferPeak η - npvOptimalBound η D₀ δ_gap) := by
    apply discountGap_pos hD (le_of_lt hδ)
    linarith [lafferPeak_pos hη]
  have hD_star : 0 < discountGap D₀ δ_gap (lafferPeak η) := by
    apply discountGap_pos hD (le_of_lt hδ)
    exact le_of_lt (lafferPeak_pos hη)
  rw [div_lt_div_iff₀ hD_star hD₁]
  -- Goal: R(τ*) · D(τ₁) < R(τ₁) · D(τ*)
  -- Unfold everything to rational expressions
  simp only [lafferRevenue, lafferPeak, discountGap, npvOptimalBound]
  -- Clear all denominators
  field_simp
  -- Close the polynomial inequality
  nlinarith [sq_nonneg η, sq_nonneg D₀, sq_nonneg δ_gap, sq_nonneg B₀,
             mul_pos hB hδ, mul_pos hη hD, mul_pos hη hδ, sq_pos_of_pos hη]

/-- Larger δ_gap implies larger gap between NPV peak and Laffer peak. -/
theorem npv_gap_increases_with_delta {η D₀ δ₁ δ₂ : ℝ}
    (hη : 0 < η) (hD : 0 < D₀)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ : δ₁ < δ₂) :
    npvOptimalBound η D₀ δ₁ < npvOptimalBound η D₀ δ₂ := by
  simp only [npvOptimalBound]
  have hη_ne : η ≠ 0 := ne_of_gt hη
  have h2η : (0:ℝ) < 2 * η := by linarith
  have hden₁ : (0:ℝ) < D₀ + δ₁ / (2 * η) := by positivity
  have hden₂ : (0:ℝ) < D₀ + δ₂ / (2 * η) := by positivity
  have h8η2 : (0:ℝ) < 8 * η ^ 2 := by positivity
  rw [div_lt_div_iff₀ (mul_pos h8η2 hden₁) (mul_pos h8η2 hden₂)]
  have key₁ : 8 * η ^ 2 * (D₀ + δ₁ / (2 * η)) = 8 * η ^ 2 * D₀ + 4 * η * δ₁ := by
    field_simp; ring
  have key₂ : 8 * η ^ 2 * (D₀ + δ₂ / (2 * η)) = 8 * η ^ 2 * D₀ + 4 * η * δ₂ := by
    field_simp; ring
  have h_diff : δ₂ * (8 * η ^ 2 * (D₀ + δ₁ / (2 * η))) -
    δ₁ * (8 * η ^ 2 * (D₀ + δ₂ / (2 * η))) =
    8 * η ^ 2 * D₀ * (δ₂ - δ₁) := by
    rw [key₁, key₂]; ring
  linarith [mul_pos (mul_pos h8η2 hD) (sub_pos.mpr hδ)]

/-- Higher growth sensitivity β implies larger gap. -/
theorem npv_gap_increases_with_beta {η D₀ g₀ γ β₁ β₂ : ℝ}
    (hη : 0 < η) (hD : 0 < D₀) (hg : 0 < g₀)
    (hγ : 0 < γ) (_hβ₁ : 0 < β₁) (_hβ₂ : 0 < β₂)
    (hβ : β₁ < β₂) :
    npvOptimalBound η D₀ (γ + g₀ * β₁) < npvOptimalBound η D₀ (γ + g₀ * β₂) := by
  apply npv_gap_increases_with_delta hη hD
  · linarith [mul_pos hg _hβ₁]
  · linarith [mul_pos hg _hβ₂]
  · linarith [mul_lt_mul_of_pos_left hβ hg]

/-- The dynamic wedge (NPV loss from discount widening) is positive. -/
theorem dynamic_wedge_pos {B₀ η D₀ δ_gap τ : ℝ}
    (hR : 0 < lafferRevenue B₀ η τ) (hδ : 0 < δ_gap)
    (hD : 0 < discountGap D₀ δ_gap τ) :
    0 < dynamicWedge B₀ η D₀ δ_gap τ := by
  simp only [dynamicWedge]
  exact div_pos (mul_pos hR hδ) (sq_pos_of_pos hD)

-- ============================================================
-- Section 6: Connecting to Other Layers
-- ============================================================

/-- Tax lowers investment: higher τ with ψ > 0 reduces the savings rate,
    which feeds into lower capital accumulation. -/
theorem tax_lowers_investment {s₀ ψ τ δ Y K : ℝ}
    (hs : 0 < s₀) (hψ : 0 < ψ) (hτ : 0 < τ)
    (hY : 0 < Y)
    (hss : capitalAccumulation (investmentRate s₀ ψ τ) δ Y K = 0) :
    capitalAccumulation (investmentRate s₀ ψ 0) δ Y K > 0 := by
  have hs_τ : investmentRate s₀ ψ τ < investmentRate s₀ ψ 0 :=
    investmentRate_decreasing hs hψ hτ
  have hss_eq := capitalAccumulation_eq_zero_iff.mp hss
  simp only [capitalAccumulation]
  nlinarith [mul_lt_mul_of_pos_right hs_τ hY]

/-- Higher tax widens the discount gap. -/
theorem higher_tax_wider_discount {D₀ δ_gap τ₁ τ₂ : ℝ}
    (hδ : 0 < δ_gap) (hτ : τ₁ < τ₂) :
    discountGap D₀ δ_gap τ₁ < discountGap D₀ δ_gap τ₂ :=
  discountGap_increasing hδ hτ

/-- Growth g > 0 relaxes the debt sustainability condition. -/
theorem debt_sustainable_with_growth {r_B g₁ g₂ b d : ℝ}
    (hb : 0 < b) (hg : g₁ < g₂) :
    debtDynamics r_B g₂ b d < debtDynamics r_B g₁ b d :=
  debtDynamics_decreasing_in_g hb hg

/-- Ramsey inverse elasticity rule: sectors with higher behavioral
    elasticity η should face lower tax rates.

    **Proof.** The Saez optimal rate $\tau^* = 1/(1 + a \cdot e)$ is decreasing in the elasticity $e$: since $e_1 < e_2$ implies $1 + ae_1 < 1 + ae_2$, taking reciprocals reverses the inequality: $1/(1+ae_2) < 1/(1+ae_1)$. -/
theorem ramsey_inverse_elasticity {a e₁ e₂ : ℝ}
    (ha : 0 < a) (he₁ : 0 < e₁) (he₂ : 0 < e₂) (he : e₁ < e₂) :
    saezTopRate a e₂ < saezTopRate a e₁ :=
  saezTopRate_decreasing_in_e ha he₁ he₂ he

-- ============================================================
-- Section 7: Summary Statistics
-- ============================================================

-- Total count: 10 definitions, 32 theorems.
-- Fully proved: 32. Sorry: 0.
-- Axioms: 0.
-- Key theorems:
-- growthRate_pos/decreasing: g > 0 and g ↓ τ
-- discountGap_pos/increasing: D > 0 and D ↑ τ
-- npvRevenue_pos: NPV > 0 under standard conditions
-- npvRevenue_cross_comparison: cross-multiplication tool
-- lafferRevenue_symmetric: R(τ*-ε) = R(τ*+ε)
-- npv_left_dominates_right: lower τ has higher NPV (same R, smaller D)
-- npv_suboptimal_at_laffer_peak: ∃ τ₁ < τ*, NPV(τ₁) > NPV(τ*)
-- npv_gap_increases_with_delta: larger growth effect → larger correction
-- dynamic_wedge_pos: NPV loss from discount widening > 0
-- tax_lowers_investment: connects to capital accumulation
-- debt_sustainable_with_growth: higher growth relaxes debt constraint

end
