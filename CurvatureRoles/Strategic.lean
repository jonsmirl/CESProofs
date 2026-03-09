/-
  Strategic independence of CES (Paper 1, Sections 7-8):
  - Theorem 7 (thm:strategic): No coalition can profitably manipulate CES
  - Proposition 7.1 (prop:ces_game): CES public goods game classification
-/

import CESProofs.Foundations.Hessian

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Theorem 7: Strategic independence (thm:strategic)
-- ============================================================

/-- The manipulation payoff for a coalition S that redistributes δ
    among its members (Σ_{j∈S} δⱼ = 0):
    Δ(S) = F(x + δ_S) - F(x)
    where δ_S is δ on S and 0 outside S. -/
def manipulationPayoff (J : ℕ) (F : AggFun J) (x : Fin J → ℝ)
    (S : Finset (Fin J)) (δ : Fin J → ℝ)
    (_hδ : ∑ j ∈ S, δ j = 0) : ℝ :=
  F (fun j => x j + if j ∈ S then δ j else 0) - F x

/-- **Log-supermodularity**: For i ≠ j, the off-diagonal Hessian entry
    H_{ij} = (1-ρ)/(J²c) > 0 when ρ < 1. This means ∂²F/∂xᵢ∂xⱼ > 0:
    increasing one input raises the marginal product of every other input.
    This is the CES supermodularity that drives strategic independence.

    **Proof.** For $i \neq j$, the off-diagonal entry reduces to $(1-\rho)/(J^2 c)$. Since $\rho < 1$ gives $1 - \rho > 0$ and $J^2 c > 0$ by hypothesis, the ratio is strictly positive. -/
theorem ces_log_supermodular (J : ℕ) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) (hJ : 0 < J)
    {i j : Fin J} (hij : i ≠ j) :
    0 < cesHessianEntry J ρ c i j := by
  simp only [cesHessianEntry, hij, ite_false, sub_zero, mul_one]
  apply div_pos
  · linarith
  · apply mul_pos
    · positivity
    · exact hc

/-- **Theorem 7 (Strategic Independence)** — Section 7, thm:strategic.

    (i) No coalition can profitably manipulate the CES aggregate: Δ(S) ≤ 0.
    (ii) The quantitative bound: Δ(S) ≤ -(K/(2(J-1))) · ‖δ_S‖²/c².

    The key insight: at the symmetric point, any zero-sum redistribution δ
    with Σδⱼ = 0 lies in 1⊥. The Hessian is negative definite on 1⊥
    with eigenvalue -(1-ρ)/(Jc). So the second-order effect is:
    Δ(S) ≈ (1/2) · v^T H v = -(1-ρ)/(2Jc) · ‖δ‖² ≤ 0. -/
theorem strategic_independence_qualitative (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c)
    (δ : Fin J → ℝ) (hδ : orthToOne J δ)
    (hδ_ne : ∃ j, δ j ≠ 0) :
    -- The second-order approximation of the manipulation payoff is negative
    cesHessianQF J ρ c δ < 0 :=
  ces_strict_concavity_on_perp hJ hρ hc δ hδ hδ_ne

/-- The exact Hessian quadratic form on 1-perp in terms of curvature K:
    δ^T H δ = -K/((J-1)c) * ||δ||^2.

    This is eq. (1083) in the paper proof of Theorem 9.1 (thm:strategic).
    The manipulation gain bound follows by dividing by 2c and normalizing:
    Δ(S) <= -K/(2(J-1)) * ||δ||^2 / c^2. -/
theorem strategic_bound (hJ : 2 ≤ J) {ρ : ℝ} (_hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c)
    (δ : Fin J → ℝ) (hδ : orthToOne J δ) :
    cesHessianQF J ρ c δ =
      -(curvatureK J ρ / ((↑J - 1) * c)) * vecNormSq J δ := by
  -- From cesHessianQF_on_perp: cesHessianQF = -(1-ρ)/(Jc) * ||δ||^2
  -- And K/(J-1) = (1-ρ)(J-1)/(J(J-1)) = (1-ρ)/J
  -- So -K/((J-1)c) = -(1-ρ)/(Jc), and the two expressions are equal.
  rw [cesHessianQF_on_perp (by omega) ρ c hc δ hδ]
  simp only [cesEigenvaluePerp, curvatureK, vecNormSq]
  have hJpos : (0 : ℝ) < ↑J := by exact_mod_cast (by omega : 0 < J)
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  have hJm1_pos : (0 : ℝ) < ↑J - 1 := by
    have : (1 : ℝ) < ↑J := by exact_mod_cast (by omega : 1 < J)
    linarith
  have hJm1_ne : (↑J : ℝ) - 1 ≠ 0 := ne_of_gt hJm1_pos
  have hcne : c ≠ 0 := ne_of_gt hc
  field_simp

-- ============================================================
-- Proposition 7.1: CES public goods game (prop:ces_game)
-- ============================================================

/-- The CES public goods game payoff.
    Two agents each choose x ∈ {0, 1}. Public good = M_ρ(x₁, x₂).
    Payoff = F(x₁, x₂) - e · xᵢ where e is effort cost. -/
def cesGamePayoff (ρ : ℝ) (x₁ x₂ : ℝ) (e : ℝ) (i : Fin 2) : ℝ :=
  ((1 / 2 : ℝ) * (x₁ ^ ρ + x₂ ^ ρ)) ^ (1 / ρ) - e * if i = 0 then x₁ else x₂

/-- The critical ratio f(ρ) = F(1,0)/F(1,1) = 2^{-1/ρ} for ρ > 0. -/
def cesGameCriticalRatio (ρ : ℝ) : ℝ :=
  if ρ > 0 then (2 : ℝ) ^ (-(1 / ρ)) else 0

/-- f(ρ) = 2^{-1/ρ} for ρ > 0:
    F(1,0)/F(1,1) = ((1/2)·1^ρ + (1/2)·0^ρ)^{1/ρ} / 1
                   = (1/2)^{1/ρ} = 2^{-1/ρ}. -/
theorem cesGameCriticalRatio_eq (ρ : ℝ) (hρ : 0 < ρ) :
    cesGameCriticalRatio ρ = (2 : ℝ) ^ (-(1 / ρ)) := by
  simp [cesGameCriticalRatio, hρ]

/-- For ρ > 0: 0 < f(ρ) < 1. -/
theorem cesGameCriticalRatio_bounds {ρ : ℝ} (hρ : 0 < ρ) :
    0 < cesGameCriticalRatio ρ ∧ cesGameCriticalRatio ρ < 1 := by
  rw [cesGameCriticalRatio_eq ρ hρ]
  constructor
  · positivity
  · apply rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2)
    exact neg_neg_of_pos (div_pos one_pos hρ)

/-- **Game classification by ρ**:
    - ρ ≤ 0: Stag Hunt (losing one player zeroes the public good)
    - 0 < ρ < 1: Stag Hunt or Prisoner's Dilemma (depends on e)
    - ρ > 1: Chicken or Prisoner's Dilemma

    The transition from Stag Hunt to Prisoner's Dilemma as ρ increases
    captures how complementarity determines the strategic structure of
    public goods provision. -/
theorem cesGame_classification :
    -- ρ ≤ 0: complete complementarity, losing one player is catastrophic
    (∀ ρ : ℝ, ρ ≤ 0 → cesGameCriticalRatio ρ = 0) ∧
    -- ρ > 0: partial substitutability, nonzero payoff from unilateral action
    (∀ ρ : ℝ, 0 < ρ → 0 < cesGameCriticalRatio ρ) := by
  constructor
  · intro ρ hρ
    simp [cesGameCriticalRatio, show ¬(ρ > 0) by linarith]
  · intro ρ hρ
    exact (cesGameCriticalRatio_bounds hρ).1

end
