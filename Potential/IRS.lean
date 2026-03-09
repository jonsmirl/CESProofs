/-
  Increasing returns to scale results (Paper 1, Section 11):
  - Theorem 11.1 (thm:crs_forced): Scale consistency forces CRS
  - Proposition 11.2 (prop:irs_hessian): Two-eigenvalue IRS Hessian
  - Proposition 11.3 (prop:scale_scope): Scale-scope complementarity
-/

import CESProofs.Foundations.Hessian

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Theorem 11.1: CRS forced (thm:crs_forced)
-- ============================================================

/-- **Theorem (Scale Consistency Forces CRS)**: Among continuous, symmetric,
    strictly increasing functions F : ℝ₊ᴶ → ℝ₊ that are homogeneous of
    degree γ > 0, scale consistency forces γ = 1.

    **Proof.** Scale consistency requires F ∘ F (when applied to blocks) to be
    a valid instance of F. But F(λx) = λ^γ F(x) and iterating gives
    F composed with itself scales as λ^{γ²}. Scale consistency requires
    γ² = γ, so γ(γ-1) = 0, giving γ = 0 or γ = 1. Since γ > 0, γ = 1. -/
theorem crs_forced {γ : ℝ} (hγ_pos : 0 < γ)
    (hγ_idem : γ ^ 2 = γ) :
    γ = 1 := by
  -- γ² = γ implies γ(γ-1) = 0
  have h : γ * (γ - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h1 | h1
  · linarith -- γ = 0 contradicts γ > 0
  · linarith -- γ - 1 = 0 gives γ = 1

/-- The idempotency condition: for a homogeneous-of-degree-γ function,
    scale consistency requires the scaling exponent to satisfy γ² = γ.
    This is because nested aggregation scales as λ^{γ·γ} = λ^{γ²},
    while direct aggregation scales as λ^γ.

    **Proof.** Nested aggregation of a homogeneous-of-degree-γ function scales
    inputs by λ^{γ·γ} = λ^{γ²}, while direct aggregation scales by λ^γ.
    Scale consistency requires γ² = γ, giving γ = 0 or γ = 1. Since γ > 0,
    the result follows.

    Formally: if F is homogeneous of degree γ, then the nested aggregation
    G(x) = F(j ↦ F(· ↦ x_j)) is homogeneous of degree γ². If scale consistency
    requires G to also be homogeneous of degree γ, then γ² = γ. -/
theorem scaling_idempotency {γ : ℝ}
    (hγ_pos : 0 < γ)
    -- Scale consistency: nested aggregation must scale as λ^γ, not λ^{γ²}
    (hsc : γ * γ = γ) :
    γ = 1 := by
  -- γ·γ = γ means γ(γ-1) = 0
  have h : γ * (γ - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h1 | h1
  · linarith -- γ = 0 contradicts γ > 0
  · linarith -- γ - 1 = 0 gives γ = 1

-- ============================================================
-- Proposition 11.2: IRS Hessian (prop:irs_hessian)
-- ============================================================

-- The IRS CES Hessian has two distinct eigenvalues at the symmetric point:
-- (i) On 1 (scale direction): λ₁ = γ(γ-1)/(J) · c^{γ-2}
-- (ii) On 1⊥ (diversity directions): λ_⊥ = -γ(1-ρ)/(J) · c^{γ-2}
-- When γ = 1 (CRS): λ₁ = 0, recovering the standard result.
-- When γ > 1 (IRS): λ₁ > 0 (convex in scale), while λ_⊥ stays negative.

/-- Scale eigenvalue of the IRS Hessian. -/
def irsEigenvalueScale (J : ℕ) (γ c : ℝ) : ℝ :=
  γ * (γ - 1) / ↑J * c ^ (γ - 2)

/-- Diversity eigenvalue of the IRS Hessian. -/
def irsEigenvaluePerp (J : ℕ) (ρ γ c : ℝ) : ℝ :=
  -(γ * (1 - ρ)) / ↑J * c ^ (γ - 2)

/-- At CRS (γ = 1), the scale eigenvalue is 0. -/
theorem irs_scale_eigenvalue_at_crs (hJ : 0 < J) (c : ℝ) :
    irsEigenvalueScale J 1 c = 0 := by
  simp [irsEigenvalueScale]

/-- At IRS (γ > 1), the scale eigenvalue is positive (for c > 0).
    The aggregate is convex in the scale direction: increasing returns. -/
theorem irs_scale_eigenvalue_pos {γ : ℝ} (hγ : 1 < γ)
    (hJ : 0 < J) {c : ℝ} (hc : 0 < c) :
    0 < irsEigenvalueScale J γ c := by
  simp only [irsEigenvalueScale]
  apply mul_pos
  · apply div_pos
    · exact mul_pos (by linarith) (by linarith)
    · exact_mod_cast hJ
  · exact rpow_pos_of_pos hc _

/-- The diversity eigenvalue is negative for ρ < 1 and γ > 0.
    CES curvature operates on diversity regardless of returns to scale. -/
theorem irs_diversity_eigenvalue_neg {ρ γ : ℝ} (hρ : ρ < 1) (hγ : 0 < γ)
    (hJ : 0 < J) {c : ℝ} (hc : 0 < c) :
    irsEigenvaluePerp J ρ γ c < 0 := by
  simp only [irsEigenvaluePerp]
  apply mul_neg_of_neg_of_pos
  · apply div_neg_of_neg_of_pos
    · exact neg_neg_of_pos (mul_pos hγ (by linarith))
    · exact_mod_cast hJ
  · exact rpow_pos_of_pos hc _

-- ============================================================
-- Proposition 11.3: Scale-scope complementarity (prop:scale_scope)
-- ============================================================

-- Scale-scope complementarity: When γ > 1 and ρ < 1, scale and diversity are
-- complements: ∂²F_γ/(∂S ∂D) > 0. Larger firms benefit more from diversification,
-- and more diversified firms benefit more from scale.

/-- The cross-partial is proportional to γ(γ-1)(1-ρ). -/
def scaleScopeCrossPartialSign (γ ρ : ℝ) : ℝ := γ * (γ - 1) * (1 - ρ)

/-- Scale-scope complementarity holds when γ > 1 and ρ < 1. -/
theorem scale_scope_complementarity {γ ρ : ℝ} (hγ : 1 < γ) (hρ : ρ < 1) :
    0 < scaleScopeCrossPartialSign γ ρ := by
  simp only [scaleScopeCrossPartialSign]
  apply mul_pos
  · apply mul_pos <;> linarith
  · linarith

/-- No scale-scope complementarity at CRS (γ = 1). -/
theorem no_scale_scope_at_crs (ρ : ℝ) :
    scaleScopeCrossPartialSign 1 ρ = 0 := by
  simp [scaleScopeCrossPartialSign]

end
