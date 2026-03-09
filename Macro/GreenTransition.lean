/-
  Green Energy Transition Extension

  CES substitution between clean and dirty energy with Wright's Law
  learning curves driving cost parity crossing.

  Model: Y = [α·E_c^ρ + (1-α)·E_d^ρ]^{1/ρ}
  Clean cost: p_c(Q) = p₀·Q^{-β} (Wright's Law)
  Dirty cost: p_d + τ (including carbon tax)
  Crossing: Q* = (p₀/(p_d+τ))^{1/β}
  Geometric dimension: β = d·α₀ where d is continuous, not just {1,2}.

  Key subtlety: green energy technologies have effective geometric
  dimension d ∈ (1, 2), not purely d=2. Solar PV cell manufacturing
  is planar (d=2), but the full system cost includes balance-of-system,
  installation, and grid integration — all linear (d=1) processes.
  The empirically observed α ≈ 0.23 for solar PV is consistent with
  d ≈ 1.9, between the pure d=1 (α₀ ≈ 0.12) and d=2 (2α₀ ≈ 0.24)
  benchmarks. Wind turbines are predominantly d=1 (α ≈ 0.12).

  All proofs are algebraic — no axioms, no sorry.
-/

import CESProofs.Macro.TwoFactorCES
import CESProofs.Hierarchy.EndogenousCrossing

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Core Definitions
-- ============================================================

/-- CES inner aggregate for clean and dirty energy: α·E_c^ρ + (1-α)·E_d^ρ.
    Alias for cesInner with energy interpretation. -/
def energyCESInner (α ρ E_c E_d : ℝ) : ℝ := cesInner α ρ E_c E_d

/-- CES energy production: Y = [α·E_c^ρ + (1-α)·E_d^ρ]^{1/ρ}.
    Two-factor CES with TFP = 1. -/
def energyCES (α ρ E_c E_d : ℝ) : ℝ := twoFactorCES 1 α ρ E_c E_d

/-- Clean energy share: s_c = α·E_c^ρ / (α·E_c^ρ + (1-α)·E_d^ρ). -/
def cleanEnergyShare (α ρ E_c E_d : ℝ) : ℝ := capitalShare α ρ E_c E_d

/-- Dirty energy share: s_d = (1-α)·E_d^ρ / (α·E_c^ρ + (1-α)·E_d^ρ). -/
def dirtyEnergyShare (α ρ E_c E_d : ℝ) : ℝ := laborShare α ρ E_c E_d

/-- Wright's Law cost for clean energy: p_c = p₀·Q^{-β}.
    Cost falls as cumulative production Q increases. -/
def cleanEnergyCost (p₀ β Q : ℝ) : ℝ := p₀ * Q ^ (-β)

/-- Effective cost of dirty energy including carbon tax: p_d + τ. -/
def effectiveDirtyCost (p_d τ : ℝ) : ℝ := p_d + τ

/-- Crossing production Q*: cumulative production at which clean cost
    equals effective dirty cost. Derived from p₀·Q*^{-β} = p_d + τ,
    so Q* = (p₀/(p_d+τ))^{1/β}. -/
def crossingProduction (p₀ p_d τ β : ℝ) : ℝ := (p₀ / (p_d + τ)) ^ (1 / β)

/-- Learning rate from geometric dimension: β = d·α₀ where d is the
    geometric dimension of the manufacturing process and α₀ ≈ 0.12
    is the base process learning rate. -/
def geometricLearningRate (d α₀ : ℝ) : ℝ := d * α₀

-- ============================================================
-- Section 2: Bridge Theorems
-- ============================================================

/-- energyCESInner is cesInner by definition. -/
theorem energyCESInner_eq_cesInner {α ρ E_c E_d : ℝ} :
    energyCESInner α ρ E_c E_d = cesInner α ρ E_c E_d := rfl

/-- energyCES is twoFactorCES with TFP = 1 by definition. -/
theorem energyCES_eq_twoFactorCES {α ρ E_c E_d : ℝ} :
    energyCES α ρ E_c E_d = twoFactorCES 1 α ρ E_c E_d := rfl

/-- The energy CES inner aggregate is positive. -/
theorem energyCESInner_pos {α ρ E_c E_d : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hEc : 0 < E_c) (hEd : 0 < E_d) :
    0 < energyCESInner α ρ E_c E_d :=
  cesInner_pos hα hα1 hEc hEd

/-- Clean and dirty energy shares sum to one. -/
theorem energy_shares_sum_one {α ρ E_c E_d : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hEc : 0 < E_c) (hEd : 0 < E_d) :
    cleanEnergyShare α ρ E_c E_d + dirtyEnergyShare α ρ E_c E_d = 1 :=
  capitalShare_plus_laborShare (ρ := ρ) hα hα1 hEc hEd

-- ============================================================
-- Section 3: Wright's Law for Clean Energy
-- ============================================================

/-- cleanEnergyCost unfolds to Wright's Law form. -/
theorem cleanEnergyCost_eq_wright {p₀ β Q : ℝ} :
    cleanEnergyCost p₀ β Q = p₀ * Q ^ (-β) := rfl

/-- Clean energy cost is positive. -/
theorem cleanEnergyCost_pos {p₀ β Q : ℝ}
    (hp₀ : 0 < p₀) (hQ : 0 < Q) :
    0 < cleanEnergyCost p₀ β Q :=
  wright_law_pos hp₀ hQ

/-- **Clean energy cost decreasing**: p_c(Q₂) < p_c(Q₁) when Q₁ < Q₂.
    Direct application of Wright's Law (Axiom 5). -/
theorem cleanEnergyCost_decreasing {p₀ β Q₁ Q₂ : ℝ}
    (hp₀ : 0 < p₀) (hβ : 0 < β) (hQ₁ : 0 < Q₁) (_hQ₂ : 0 < Q₂)
    (hQ : Q₁ < Q₂) :
    cleanEnergyCost p₀ β Q₂ < cleanEnergyCost p₀ β Q₁ :=
  wright_law_decreasing hp₀ hβ hQ₁ _hQ₂ hQ

-- ============================================================
-- Section 4: Crossing Production
-- ============================================================

/-- **Crossing identity**: At Q*, clean energy cost equals effective dirty cost.
    p₀ · Q*^{-β} = p_d + τ where Q* = (p₀/(p_d+τ))^{1/β}.

    **Proof.** (x^{1/β})^{-β} = x^{(1/β)·(-β)} = x^{-1} by rpow_mul,
    then p₀ · (p₀/(p_d+τ))^{-1} = p₀ · (p_d+τ)/p₀ = p_d+τ. -/
theorem crossing_at_Qstar {p₀ p_d τ β : ℝ}
    (hp₀ : 0 < p₀) (hpdτ : 0 < p_d + τ) (hβ : β ≠ 0) :
    cleanEnergyCost p₀ β (crossingProduction p₀ p_d τ β) =
    effectiveDirtyCost p_d τ := by
  simp only [cleanEnergyCost, crossingProduction, effectiveDirtyCost]
  -- Goal: p₀ * ((p₀ / (p_d + τ)) ^ (1 / β)) ^ (-β) = p_d + τ
  have hbase : (0 : ℝ) ≤ p₀ / (p_d + τ) := le_of_lt (div_pos hp₀ hpdτ)
  -- Combine exponents: (x^{1/β})^{-β} = x^{(1/β)·(-β)} = x^{-1}
  rw [← rpow_mul hbase]
  have hexp : (1 / β * (-β) : ℝ) = -1 := by field_simp
  rw [hexp, rpow_neg_one (p₀ / (p_d + τ)), inv_div]
  -- p₀ * ((p_d + τ) / p₀) = p_d + τ
  field_simp

/-- Crossing production is positive. -/
theorem crossingProduction_pos {p₀ p_d τ β : ℝ}
    (hp₀ : 0 < p₀) (hpdτ : 0 < p_d + τ) :
    0 < crossingProduction p₀ p_d τ β :=
  rpow_pos_of_pos (div_pos hp₀ hpdτ) _

/-- **Higher carbon tax lowers crossing production** (transition happens sooner).
    Q* = (p₀/(p_d+τ))^{1/β}. Higher τ increases the denominator,
    decreasing the base, hence decreasing Q* for positive exponent 1/β. -/
theorem crossingProduction_decreasing_in_tax {p₀ p_d τ₁ τ₂ β : ℝ}
    (hp₀ : 0 < p₀) (hpdτ₁ : 0 < p_d + τ₁)
    (hβ : 0 < β) (hτ : τ₁ < τ₂) :
    crossingProduction p₀ p_d τ₂ β < crossingProduction p₀ p_d τ₁ β := by
  simp only [crossingProduction]
  have hpdτ₂ : 0 < p_d + τ₂ := by linarith
  apply rpow_lt_rpow (le_of_lt (div_pos hp₀ hpdτ₂))
  · exact div_lt_div_of_pos_left hp₀ hpdτ₁ (by linarith)
  · exact div_pos one_pos hβ

/-- **Faster learners reach parity sooner**: Q*(β₂) < Q*(β₁) when β₁ < β₂.
    For base > 1 (initially expensive clean energy): smaller exponent
    1/β₂ < 1/β₁ gives smaller result since b^x is increasing for b > 1. -/
theorem crossingProduction_decreasing_in_beta {p₀ p_d τ β₁ β₂ : ℝ}
    (_hp₀ : 0 < p₀) (hpdτ : 0 < p_d + τ)
    (hβ₁ : 0 < β₁) (_hβ₂ : 0 < β₂) (hβ : β₁ < β₂)
    (hexpensive : p_d + τ < p₀) :
    crossingProduction p₀ p_d τ β₂ < crossingProduction p₀ p_d τ β₁ := by
  simp only [crossingProduction]
  have hbase : 1 < p₀ / (p_d + τ) := by rwa [one_lt_div hpdτ]
  exact rpow_lt_rpow_of_exponent_lt hbase (div_lt_div_of_pos_left one_pos hβ₁ hβ)

-- ============================================================
-- Section 5: Clean Share Dynamics
-- ============================================================

/-- **Energy share identity**: log(s_d/s_c) = log((1-α)/α) + ρ·log(E_d/E_c).
    Direct from the factor share identity, with K = E_c and L = E_d. -/
theorem energy_share_identity {α ρ E_c E_d : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hEc : 0 < E_c) (hEd : 0 < E_d) :
    Real.log (dirtyEnergyShare α ρ E_c E_d / cleanEnergyShare α ρ E_c E_d) =
    Real.log ((1 - α) / α) + ρ * Real.log (E_d / E_c) :=
  factorShare_identity hα hα1 hEc hEd

/-- **Clean share increases with clean energy input under substitutes (ρ > 0)**.
    When clean and dirty energy are substitutes, increasing clean energy
    supply raises clean energy's share of the aggregate.

    **Proof.** capitalShare = x/(x+C) where x = α·E_c^ρ and C = (1-α)·E_d^ρ.
    E_c₁ < E_c₂ and ρ > 0 implies x₁ < x₂. Then x₁/(x₁+C) < x₂/(x₂+C)
    because x₁(x₂+C) < x₂(x₁+C) reduces to x₁·C < x₂·C. -/
theorem cleanShare_rises_with_relative_input_substitute {α ρ E_c₁ E_c₂ E_d : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : 0 < ρ)
    (hEc₁ : 0 < E_c₁) (_hEc₂ : 0 < E_c₂) (hEd : 0 < E_d)
    (hEc : E_c₁ < E_c₂) :
    cleanEnergyShare α ρ E_c₁ E_d < cleanEnergyShare α ρ E_c₂ E_d := by
  simp only [cleanEnergyShare, capitalShare, cesInner]
  set C := (1 - α) * E_d ^ ρ
  have hC : 0 < C := mul_pos (by linarith) (rpow_pos_of_pos hEd ρ)
  set x₁ := α * E_c₁ ^ ρ
  set x₂ := α * E_c₂ ^ ρ
  have hx₁ : 0 < x₁ := mul_pos hα (rpow_pos_of_pos hEc₁ ρ)
  have hx_lt : x₁ < x₂ :=
    mul_lt_mul_of_pos_left (rpow_lt_rpow (le_of_lt hEc₁) hEc hρ) hα
  rw [div_lt_div_iff₀ (by linarith : 0 < x₁ + C) (by linarith : 0 < x₂ + C)]
  nlinarith

/-- Clean energy share is strictly between 0 and 1. -/
theorem cleanShare_bounded {α ρ E_c E_d : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hEc : 0 < E_c) (hEd : 0 < E_d) :
    0 < cleanEnergyShare α ρ E_c E_d ∧ cleanEnergyShare α ρ E_c E_d < 1 :=
  ⟨capitalShare_pos (ρ := ρ) hα hα1 hEc hEd,
   capitalShare_lt_one hα hα1 hEc hEd⟩

-- ============================================================
-- Section 6: Geometric Dimension and Transition Duration
-- ============================================================

/-- For purely planar processes (d=2): β = 2α₀.
    Semiconductors (DRAM, NAND Flash) are purely planar (d=2).
    Energy technologies are intermediate: solar PV d ≈ 1.9 (cell is
    planar but system includes 1D components). -/
theorem geometric_learning_rate_planar {α₀ : ℝ} :
    geometricLearningRate 2 α₀ = 2 * α₀ := rfl

/-- For linear processes (d=1): β = α₀.
    Wind turbines, chemical synthesis, logistics are linear (d=1). -/
theorem geometric_learning_rate_linear {α₀ : ℝ} :
    geometricLearningRate 1 α₀ = α₀ := by
  simp [geometricLearningRate]

/-- **Learning rate is monotone in geometric dimension**: d₁ < d₂ → β(d₁) < β(d₂).
    This is the general statement: higher geometric dimension means faster learning.
    The d=1 vs d=2 comparison is a special case. Energy technologies with
    effective d ∈ (1, 2) have learning rates between the two benchmarks. -/
theorem learning_rate_monotone_in_dimension {d₁ d₂ α₀ : ℝ}
    (hα₀ : 0 < α₀) (hd : d₁ < d₂) :
    geometricLearningRate d₁ α₀ < geometricLearningRate d₂ α₀ := by
  simp only [geometricLearningRate]; nlinarith

/-- **Planar processes learn faster**: β(d=2) > β(d=1).
    Special case of learning_rate_monotone_in_dimension.

    **Proof.** The geometric learning rate $\beta(d) = d \cdot \alpha_0$ is linear in dimension $d$, so $\beta(2) = 2\alpha_0 > \alpha_0 = \beta(1)$ whenever $\alpha_0 > 0$. This is the special case $d_1 = 1 < 2 = d_2$ of the monotonicity lemma. -/
theorem planar_learns_faster {α₀ : ℝ} (hα₀ : 0 < α₀) :
    geometricLearningRate 1 α₀ < geometricLearningRate 2 α₀ :=
  learning_rate_monotone_in_dimension hα₀ (by norm_num)

/-- **Intermediate dimension gives intermediate learning rate**:
    d=1 < d < d=2 implies β(1) < β(d) < β(2).
    Solar PV with d ≈ 1.9 has learning rate between wind (d=1) and
    semiconductors (d=2). -/
theorem intermediate_dimension_intermediate_rate {d α₀ : ℝ}
    (hα₀ : 0 < α₀) (hd_lo : 1 < d) (hd_hi : d < 2) :
    geometricLearningRate 1 α₀ < geometricLearningRate d α₀ ∧
    geometricLearningRate d α₀ < geometricLearningRate 2 α₀ :=
  ⟨learning_rate_monotone_in_dimension hα₀ hd_lo,
   learning_rate_monotone_in_dimension hα₀ hd_hi⟩

/-- **Higher-dimensional processes cross sooner**: Q*(d=2) < Q*(d=1).
    More generally, Q*(d₂) < Q*(d₁) for any d₁ < d₂. Energy technologies
    with more planar content (solar, d ≈ 1.9) cross sooner than
    linear technologies (wind, d ≈ 1) for the same initial conditions. -/
theorem planar_crosses_sooner {p₀ p_d τ α₀ : ℝ}
    (hp₀ : 0 < p₀) (hpdτ : 0 < p_d + τ)
    (hα₀ : 0 < α₀) (hexpensive : p_d + τ < p₀) :
    crossingProduction p₀ p_d τ (geometricLearningRate 2 α₀) <
    crossingProduction p₀ p_d τ (geometricLearningRate 1 α₀) :=
  crossingProduction_decreasing_in_beta hp₀ hpdτ
    (by simp [geometricLearningRate]; linarith)
    (by simp [geometricLearningRate]; linarith)
    (planar_learns_faster hα₀) hexpensive

-- ============================================================
-- Section 7: Summary Statistics
-- ============================================================

-- Total count: 8 definitions, 18 theorems.
-- Fully proved: 18. Sorry: 0. Axioms: 0.
--
-- Definitions:
--   energyCESInner, energyCES, cleanEnergyShare, dirtyEnergyShare,
--   cleanEnergyCost, effectiveDirtyCost, crossingProduction, geometricLearningRate
--
-- Key results:
--   energy_shares_sum_one: s_c + s_d = 1 (from capitalShare_plus_laborShare)
--   cleanEnergyCost_decreasing: Wright's Law (from wright_law_decreasing)
--   crossing_at_Qstar: p₀·Q*^{-β} = p_d + τ (rpow algebra)
--   crossingProduction_decreasing_in_tax: higher τ → lower Q* (earlier transition)
--   crossingProduction_decreasing_in_beta: faster learner → lower Q* (rpow monotone)
--   energy_share_identity: log(s_d/s_c) = log((1-α)/α) + ρ·log(E_d/E_c)
--   cleanShare_rises_with_relative_input_substitute: s_c increases with E_c (ρ > 0)
--   planar_crosses_sooner: Q*(d=2) < Q*(d=1) (geometric dimension)

end
