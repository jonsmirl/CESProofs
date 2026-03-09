/-
  Paper 1, §22.5: Market Structure as CES Curvature

  Formalizes:
  - CES Cournot markup μ(J) = J·σ/(J·σ - 1)
  - Lerner index L(J) = 1/(J·σ)
  - Curvature cost of merger ΔK = (1-ρ)/[J(J-1)]
  - Duopoly-to-monopoly merger is maximal curvature loss
-/

import CESProofs.EntryExit.Defs
import CESProofs.EntryExit.CurvatureInJ

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: CES Markup and Lerner Index
-- ============================================================

/-- The CES Cournot markup with J firms and demand elasticity σ:
    μ(J, σ) = J·σ / (J·σ - 1). -/
def cesMarkup (J : ℝ) (σ : ℝ) : ℝ := J * σ / (J * σ - 1)

/-- The Lerner index of market power:
    L(J, σ) = 1 / (J·σ). -/
def lernerIndex (J : ℝ) (σ : ℝ) : ℝ := 1 / (J * σ)

/-- At monopoly (J=1), the markup equals σ/(σ-1) = 1/(1-ρ). -/
theorem cesMarkup_monopoly {σ : ℝ} (_hσ : 1 < σ) :
    cesMarkup 1 σ = σ / (σ - 1) := by
  simp only [cesMarkup, one_mul]

/-- The markup is decreasing in J: more firms → lower markup. -/
theorem cesMarkup_anti {J₁ J₂ σ : ℝ} (_hJ₁ : 0 < J₁) (hσ : 1 < σ)
    (hJ : J₁ < J₂) (hJσ₁ : 1 < J₁ * σ) :
    cesMarkup J₂ σ < cesMarkup J₁ σ := by
  simp only [cesMarkup]
  have hσ₀ : 0 < σ := by linarith
  have hJσ₂ : 1 < J₂ * σ := lt_trans hJσ₁ (by nlinarith)
  have h₁ : 0 < J₁ * σ - 1 := by linarith
  have h₂ : 0 < J₂ * σ - 1 := by linarith
  rw [div_lt_div_iff₀ h₂ h₁]
  nlinarith

/-- At monopoly, the Lerner index equals 1/σ = 1-ρ. -/
theorem lernerIndex_monopoly {σ : ℝ} :
    lernerIndex 1 σ = 1 / σ := by
  simp only [lernerIndex, one_mul]

/-- The Lerner index is decreasing in J. -/
theorem lernerIndex_anti {J₁ J₂ σ : ℝ} (hJ₁ : 0 < J₁) (hσ : 0 < σ)
    (hJ : J₁ < J₂) :
    lernerIndex J₂ σ < lernerIndex J₁ σ := by
  simp only [lernerIndex]
  exact div_lt_div_of_pos_left one_pos (mul_pos hJ₁ hσ) (by nlinarith)

-- ============================================================
-- Section 2: Curvature Cost of Merger
-- ============================================================

/-- The curvature loss when J firms merge to J-1:
    ΔK(J, ρ) = (1-ρ) / [J·(J-1)]. -/
def mergerCurvatureCost (J : ℝ) (ρ : ℝ) : ℝ := (1 - ρ) / (J * (J - 1))

/-- ΔK(J) = K(J) - K(J-1): the merger cost equals the curvature difference. -/
theorem mergerCurvatureCost_eq_diff {J ρ : ℝ} (hJ : 1 < J) (hJne : J ≠ 0) :
    mergerCurvatureCost J ρ = curvatureKReal J ρ - curvatureKReal (J - 1) ρ := by
  simp only [mergerCurvatureCost, curvatureKReal]
  have hJm1 : J - 1 ≠ 0 := by linarith
  have hJJm1 : J * (J - 1) ≠ 0 := mul_ne_zero hJne hJm1
  field_simp [hJne, hJm1, hJJm1]
  ring

/-- The merger cost is positive when ρ < 1 and J > 1. -/
theorem mergerCurvatureCost_pos {J ρ : ℝ} (hJ : 1 < J) (hρ : ρ < 1) :
    0 < mergerCurvatureCost J ρ := by
  simp only [mergerCurvatureCost]
  apply div_pos (by linarith)
  exact mul_pos (by linarith) (by linarith)

/-- The duopoly-to-monopoly merger has maximal curvature cost:
    ΔK(2) = (1-ρ)/2, and for all J > 2, ΔK(J) < ΔK(2). -/
theorem mergerCost_duopoly_maximal {J ρ : ℝ} (hJ : 2 < J) (hρ : ρ < 1) :
    mergerCurvatureCost J ρ < mergerCurvatureCost 2 ρ := by
  simp only [mergerCurvatureCost]
  have h1ρ : 0 < 1 - ρ := by linarith
  apply div_lt_div_of_pos_left h1ρ
  · positivity
  · have : 2 < J * (J - 1) := by nlinarith
    linarith

/-- The duopoly-to-monopoly curvature cost is (1-ρ)/2. -/
theorem mergerCost_duopoly_value {ρ : ℝ} :
    mergerCurvatureCost 2 ρ = (1 - ρ) / 2 := by
  simp only [mergerCurvatureCost]; norm_num

/-- The merger cost is decreasing in J: mergers among many firms
    are less costly than mergers among few. -/
theorem mergerCurvatureCost_anti {J₁ J₂ ρ : ℝ}
    (hJ₁ : 1 < J₁) (hρ : ρ < 1) (hJ : J₁ < J₂) :
    mergerCurvatureCost J₂ ρ < mergerCurvatureCost J₁ ρ := by
  simp only [mergerCurvatureCost]
  have h1ρ : 0 < 1 - ρ := by linarith
  apply div_lt_div_of_pos_left h1ρ
  · exact mul_pos (by linarith) (by linarith)
  · nlinarith

end
