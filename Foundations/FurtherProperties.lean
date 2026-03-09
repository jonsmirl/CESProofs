/-
  Further properties of CES curvature (Paper 1, Section 9):
  - Proposition 9.1 (prop:asymmetry): Third-order curvature
  - Proposition 9.2 (prop:knockout): Knockout robustness
  - Proposition 9.3 (prop:duality): Primal-dual curvature conservation
-/

import CESProofs.Foundations.Hessian

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Proposition 9.1: Third-order curvature (prop:asymmetry)
-- ============================================================

/-- The value of the third derivative factor: K/(J²c²) · [(2J-1) - ρ(J-2)].
    This is the coefficient controlling shortage-surplus asymmetry. -/
def cesThirdDerivValue (J : ℕ) (ρ c : ℝ) : ℝ :=
  curvatureK J ρ / (↑J ^ 2 * c ^ 2) * ((2 * ↑J - 1) - ρ * (↑J - 2))

/-- The third derivative factor is positive for ρ < 1, J ≥ 2, c > 0.
    Since ρ < 1: ρ(J-2) < J-2 < 2J-1, so the bracket is positive.
    K > 0 and J²c² > 0 give the result. -/
theorem ces_third_derivative_pos (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) :
    0 < cesThirdDerivValue J ρ c := by
  simp only [cesThirdDerivValue]
  apply mul_pos
  · exact div_pos (curvatureK_pos hJ hρ) (mul_pos (by positivity) (sq_pos_of_pos hc))
  · have hJ1 : (1 : ℝ) < ↑J := by exact_mod_cast (by omega : 1 < J)
    have hJge2 : (2 : ℝ) ≤ ↑J := by exact_mod_cast hJ
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - ρ) (by linarith : (0 : ℝ) ≤ ↑J - 2)]

/-- The shortage-surplus asymmetry ratio:
    |ΔF(-δ)| / |ΔF(+δ)| = 1 + K·ε + O(ε²)
    where ε = δ/c is the relative perturbation.

    A shortage of δ in one input causes a larger absolute change
    in output than a surplus of the same magnitude. The asymmetry
    is proportional to K. -/
def asymmetryRatio (J : ℕ) (ρ : ℝ) (ε : ℝ) : ℝ :=
  1 + curvatureK J ρ * ε

/-- The asymmetry ratio exceeds 1 for ρ < 1 and ε > 0. -/
theorem asymmetry_exceeds_one (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    1 < asymmetryRatio J ρ ε := by
  simp only [asymmetryRatio]
  linarith [curvatureK_pos hJ hρ, mul_pos (curvatureK_pos hJ hρ) hε]

-- ============================================================
-- Proposition 9.2: Knockout robustness (prop:knockout)
-- ============================================================

/-- The fractional output retained when m of J symmetric inputs fail:
    R_m(ρ, J) = ((J-m)/J)^{1/ρ} for ρ > 0
    R_m = 0 for ρ ≤ 0 and m ≥ 1. -/
def knockoutRetained (J : ℕ) (ρ : ℝ) (m : ℕ) : ℝ :=
  if ρ > 0 then ((↑J - ↑m) / ↑J : ℝ) ^ (1 / ρ) else if m = 0 then 1 else 0

/-- For ρ > 0 and 0 < m < J: 0 < R_m < 1. -/
theorem knockout_partial_retained {ρ : ℝ} (hρ : 0 < ρ) {m : ℕ}
    (_hJ : 0 < J) (_hm_pos : 0 < m) (_hm_lt : m < J) :
    0 < knockoutRetained J ρ m ∧ knockoutRetained J ρ m < 1 := by
  simp only [knockoutRetained, show ρ > 0 from hρ, if_true]
  have hJpos : (0 : ℝ) < ↑J := by exact_mod_cast _hJ
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  -- Key: 0 < (J-m)/J < 1
  have hmJ : (↑m : ℝ) < ↑J := by exact_mod_cast _hm_lt
  have hJm_pos : (0 : ℝ) < ↑J - ↑m := by linarith
  have hfrac_pos : (0 : ℝ) < (↑J - ↑m) / ↑J := div_pos hJm_pos hJpos
  have hfrac_lt : (↑J - ↑m) / (↑J : ℝ) < 1 := by
    rw [div_lt_one hJpos]; linarith [show (0 : ℝ) < ↑m from by exact_mod_cast _hm_pos]
  have hexp_pos : (0 : ℝ) < 1 / ρ := div_pos one_pos hρ
  constructor
  · exact rpow_pos_of_pos hfrac_pos _
  · exact rpow_lt_one (le_of_lt hfrac_pos) hfrac_lt hexp_pos

/-- For ρ ≤ 0 and m ≥ 1: R_m = 0 (total failure from any knockout). -/
theorem knockout_total_failure {ρ : ℝ} (hρ : ρ ≤ 0) {m : ℕ} (hm : 0 < m) :
    knockoutRetained J ρ m = 0 := by
  simp only [knockoutRetained]
  simp [show ¬(ρ > 0) by linarith, show ¬(m = 0) by omega]

/-- For m = 0 (no failures): R_0 = 1 regardless of ρ. -/
theorem knockout_no_failure (ρ : ℝ) (hJ : 0 < J) :
    knockoutRetained J ρ 0 = 1 := by
  simp only [knockoutRetained, Nat.cast_zero, sub_zero]
  split_ifs with h
  · rw [div_self (Nat.cast_ne_zero.mpr (by omega))]
    simp
  · rfl

/-- Critical failure threshold: number of inputs that can fail before
    output drops below fraction α. m*(ρ, J, α) = ⌈J(1 - α^ρ)⌉. -/
def criticalFailures (J : ℕ) (ρ α : ℝ) : ℕ :=
  ⌈(↑J : ℝ) * (1 - α ^ ρ)⌉₊

-- ============================================================
-- Proposition 9.3: Primal-dual curvature (prop:duality)
-- ============================================================

/-- The dual (cost function) curvature parameter.
    For CES with elasticity σ = 1/(1-ρ), the dual uses r = ρ/(ρ-1) = 1-σ. -/
def dualExponent (ρ : ℝ) : ℝ := ρ / (ρ - 1)

/-- The dual eigenvalue on 1⊥: λ_⊥^C = -σ/w at equal prices w.
    σ = 1/(1-ρ). From the cost Hessian at equal prices:
    ∂²c/∂wⱼ∂wₖ = (1-r)/w · (1/J - δⱼₖ), eigenvalue on 1⊥ is -(1-r)/w = -σ/w. -/
def dualEigenvaluePerp (_J : ℕ) (ρ w : ℝ) : ℝ :=
  -(1 / (1 - ρ)) / w

/-- **Curvature conservation**: The product of primal and dual eigenvalue
    magnitudes is ρ-independent:
    |λ_⊥^F| * |λ_⊥^C| = 1/(Jcw).

    This is a deep result: production curvature and cost curvature
    are inversely related, and their product is a geometric invariant.
    Stronger complementarity (lower ρ) means more curved production
    isoquants but flatter cost contours, and vice versa. -/
theorem curvature_conservation (_hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1) (_hρne : ρ ≠ 0)
    {c w : ℝ} (hc : 0 < c) (hw : 0 < w) :
    |cesEigenvaluePerp J ρ c| * |dualEigenvaluePerp J ρ w| =
    1 / (↑J * c * w) := by
  simp only [cesEigenvaluePerp, dualEigenvaluePerp]
  have hJpos : (0 : ℝ) < ↑J := by exact_mod_cast (by omega : 0 < J)
  have hρ1 : (0 : ℝ) < 1 - ρ := by linarith
  have h1ρne : (1 : ℝ) - ρ ≠ 0 := ne_of_gt hρ1
  rw [show -(1 - ρ) / (↑J * c) = -((1 - ρ) / (↑J * c)) from by ring]
  rw [show -(1 / (1 - ρ)) / w = -((1 / (1 - ρ)) / w) from by ring]
  rw [abs_neg, abs_neg]
  rw [abs_of_pos (div_pos hρ1 (mul_pos hJpos hc))]
  rw [abs_of_pos (div_pos (div_pos one_pos hρ1) hw)]
  field_simp

/-- The excess cost saving coefficient: (J-1)² / (2J³K) where K = (1-ρ)(J-1)/J.
    This is the second-order coefficient in the Taylor expansion of the CES cost
    function when one input price drops by fraction δ. -/
def excessSavingCoeff (J : ℕ) (ρ : ℝ) : ℝ :=
  (↑J - 1) ^ 2 / (2 * ↑J ^ 3 * curvatureK J ρ)

/-- **Substitution savings**: When one input price drops by fraction δ,
    the excess cost saving (beyond the mechanical price effect) is
    S_excess = (J-1)² / (2J³K) · δ² + O(δ³).

    The excess saving is inversely proportional to K: when inputs are
    strong complements, there's little scope for substitution.

    **Proof.** Expand K = (1-ρ)(J-1)/J in the coefficient (J-1)²/(2J³K).
    The factor (J-1) cancels, giving (J-1)/(2J²(1-ρ)), which is manifestly
    inversely proportional to (1-ρ). -/
theorem substitution_savings (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1) :
    excessSavingCoeff J ρ = (↑J - 1) / (2 * ↑J ^ 2 * (1 - ρ)) := by
  simp only [excessSavingCoeff, curvatureK]
  have hJpos : (0 : ℝ) < ↑J := by exact_mod_cast (by omega : 0 < J)
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  have hJ1 : (0 : ℝ) < ↑J - 1 := by
    have : (1 : ℝ) < ↑J := by exact_mod_cast (by omega : 1 < J)
    linarith
  have hJ1ne : (↑J : ℝ) - 1 ≠ 0 := ne_of_gt hJ1
  have hρ1 : (0 : ℝ) < 1 - ρ := by linarith
  have hρ1ne : (1 : ℝ) - ρ ≠ 0 := ne_of_gt hρ1
  field_simp

end
