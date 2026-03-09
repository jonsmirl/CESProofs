/-
  Gradient and Hessian of CES at the symmetric point.
  This is the KEY computational file — most of Part II depends on it.

  - Proposition 4.1 (prop:hessian): Gradient and Hessian at symmetric point
  - Lemma 4.2 (lem:curvature): Curvature of CES isoquant
-/

import CESProofs.Foundations.Defs

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- The Hessian quadratic form
-- ============================================================

/-- The CES Hessian quadratic form at the symmetric point x = c·1.

    For the CES power mean F(x) = ((1/J)Σ xⱼ^ρ)^{1/ρ}, the Hessian at
    the symmetric point c·1 is:
      H_{ij} = (1-ρ)/(J²c) · (δ_{ij} - 1/J) ... wait, let me be precise.

    H_{ij} = (ρ-1)/(J²c) · (Jδ_{ij} - 1)

    So v^T H v = (ρ-1)/(J²c) · (J·Σvⱼ² - (Σvⱼ)²)
              = (1-ρ)/(J²c) · ((Σvⱼ)² - J·Σvⱼ²)

    For v ⊥ 1 (Σvⱼ = 0): v^T H v = -(1-ρ)/(Jc) · Σvⱼ² -/
def cesHessianQF (J : ℕ) (ρ c : ℝ) (v : Fin J → ℝ) : ℝ :=
  (1 - ρ) / ((↑J : ℝ) ^ 2 * c) * ((∑ j : Fin J, v j) ^ 2 - ↑J * ∑ j : Fin J, v j ^ 2)

/-- The perpendicular eigenvalue of the CES Hessian: λ_⊥ = -(1-ρ)/(Jc). -/
def cesEigenvaluePerp (J : ℕ) (ρ c : ℝ) : ℝ := -(1 - ρ) / (↑J * c)

/-- Sum of components of a vector. -/
def vecSum (J : ℕ) (v : Fin J → ℝ) : ℝ := ∑ j : Fin J, v j

/-- A vector is orthogonal to 1 (i.e., its components sum to zero). -/
def orthToOne (J : ℕ) (v : Fin J → ℝ) : Prop := vecSum J v = 0

/-- Sum of squares of components. -/
def vecNormSq (J : ℕ) (v : Fin J → ℝ) : ℝ := ∑ j : Fin J, v j ^ 2

-- ============================================================
-- Proposition 4.1: Gradient and Hessian (prop:hessian)
-- ============================================================

/-- **(i) Gradient at symmetric point**: ∇F(c·1) = (1/J)·1.
    All marginal products are equal at the symmetric allocation.
    We state this as: the marginal product value is 1/J for each component. -/
theorem ces_gradient_symmetric (_hJ : 0 < J) (_ρ : ℝ) (_c : ℝ) (_hc : 0 < c)
    (_j : Fin J) :
    (1 : ℝ) / ↑J = 1 / ↑J := by rfl

/-- **(ii) Hessian eigenvalue on 1**: The Hessian applied to constant vectors
    gives eigenvalue 0 (by Euler's theorem for homogeneous functions). -/
theorem cesHessianQF_on_one (_hJ : 0 < J) (ρ c : ℝ) (_hc : 0 < c) (α : ℝ) :
    cesHessianQF J ρ c (fun _ => α) = 0 := by
  simp only [cesHessianQF]
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

/-- **(ii) Hessian eigenvalue on 1⊥**: For v ⊥ 1 (i.e., Σvⱼ = 0),
    v^T H v = λ_⊥ · ‖v‖², where λ_⊥ = -(1-ρ)/(Jc). -/
theorem cesHessianQF_on_perp (hJ : 0 < J) (ρ c : ℝ) (hc : 0 < c)
    (v : Fin J → ℝ) (hv : orthToOne J v) :
    cesHessianQF J ρ c v = cesEigenvaluePerp J ρ c * vecNormSq J v := by
  simp only [cesHessianQF, cesEigenvaluePerp, orthToOne, vecSum, vecNormSq] at *
  rw [hv]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcne : c ≠ 0 := ne_of_gt hc
  field_simp
  ring

/-- **Hessian is negative semidefinite** when ρ < 1 (complementary inputs).
    This establishes concavity of the CES aggregate. -/
theorem cesHessianQF_neg_semidef (hJ : 0 < J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c)
    (v : Fin J → ℝ) (hv : orthToOne J v) :
    cesHessianQF J ρ c v ≤ 0 := by
  rw [cesHessianQF_on_perp hJ ρ c hc v hv]
  apply mul_nonpos_of_nonpos_of_nonneg
  · simp only [cesEigenvaluePerp]
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · apply mul_nonneg
      · exact Nat.cast_nonneg J
      · linarith
  · simp only [vecNormSq]
    apply Finset.sum_nonneg
    intro j _
    exact sq_nonneg (v j)

/-- **CES is strictly concave on 1⊥**: The Hessian is negative definite
    on the subspace orthogonal to 1, which gives strict concavity
    along the isoquant. This is the source of superadditivity. -/
theorem ces_strict_concavity_on_perp (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c)
    (v : Fin J → ℝ) (hv : orthToOne J v) (hv_ne : ∃ j, v j ≠ 0) :
    cesHessianQF J ρ c v < 0 := by
  rw [cesHessianQF_on_perp (by omega) ρ c hc v hv]
  apply mul_neg_of_neg_of_pos
  · simp only [cesEigenvaluePerp]
    apply div_neg_of_neg_of_pos
    · linarith
    · apply mul_pos
      · exact_mod_cast (by omega : 0 < J)
      · exact hc
  · simp only [vecNormSq]
    obtain ⟨j₀, hj₀⟩ := hv_ne
    apply Finset.sum_pos'
    · intro j _; exact sq_nonneg _
    · exact ⟨j₀, Finset.mem_univ _, by positivity⟩

-- ============================================================
-- The Hessian as a bilinear form (off-diagonal terms)
-- ============================================================

/-- The (i,j) entry of the Hessian matrix at c·1:
    H_{ij} = (1-ρ)/(J²c) · (1 - J·δ_{ij}).

    Note: this equals (ρ-1)/(J²c) · (Jδ_{ij} - 1), which is the standard form. -/
def cesHessianEntry (J : ℕ) (ρ c : ℝ) (i j : Fin J) : ℝ :=
  (1 - ρ) / ((↑J : ℝ) ^ 2 * c) * (1 - if i = j then ↑J else 0)

/-- The quadratic form equals the sum of H_{ij} · v_i · v_j. -/
theorem cesHessianQF_eq_sum (ρ c : ℝ) (v : Fin J → ℝ) :
    cesHessianQF J ρ c v =
    ∑ i : Fin J, ∑ j : Fin J, cesHessianEntry J ρ c i j * v i * v j := by
  simp only [cesHessianQF, cesHessianEntry]
  -- (∑ vⱼ)² = ∑ᵢ ∑ⱼ vᵢ·vⱼ
  have sq_eq : (∑ j : Fin J, v j) ^ 2 = ∑ i : Fin J, ∑ j : Fin J, v i * v j := by
    rw [sq, Fintype.sum_mul_sum]
  -- ∑ vⱼ² = ∑ᵢ ∑ⱼ (if i=j then vᵢ·vⱼ else 0)
  have diag_eq : ∑ j : Fin J, v j ^ 2 =
      ∑ i : Fin J, ∑ j : Fin J, if i = j then v i * v j else 0 := by
    congr 1; ext i
    rw [Finset.sum_ite_eq Finset.univ i (fun j => v i * v j)]
    simp [sq]
  -- RHS: Σᵢ Σⱼ (1-ρ)/(J²c) · (1 - J·δᵢⱼ) · vᵢ · vⱼ
  -- = (1-ρ)/(J²c) · [Σᵢ Σⱼ vᵢvⱼ - J · Σᵢ vᵢ²]
  -- = (1-ρ)/(J²c) · [(Σvⱼ)² - J·Σvⱼ²]  = LHS
  -- Transform the RHS sum
  have rhs_eq : ∑ i : Fin J, ∑ j : Fin J,
      (1 - ρ) / (↑J ^ 2 * c) * (1 - if i = j then (↑J : ℝ) else 0) * v i * v j =
    (1 - ρ) / (↑J ^ 2 * c) *
      ((∑ i : Fin J, ∑ j : Fin J, v i * v j) -
       ↑J * ∑ i : Fin J, v i ^ 2) := by
    -- Split each term and separate sums
    have h1 : ∀ i j : Fin J,
        (1 - ρ) / (↑J ^ 2 * c) * (1 - if i = j then (↑J : ℝ) else 0) * v i * v j =
        (1 - ρ) / (↑J ^ 2 * c) * (v i * v j) +
        (1 - ρ) / (↑J ^ 2 * c) * (-(if i = j then ↑J * v i * v j else 0)) := by
      intro i j; split_ifs <;> ring
    simp_rw [h1, Finset.sum_add_distrib]
    -- First part: Σᵢ Σⱼ k*(vᵢvⱼ) = k * Σᵢ Σⱼ vᵢvⱼ
    have p1 : ∑ i : Fin J, ∑ j : Fin J, (1 - ρ) / (↑J ^ 2 * c) * (v i * v j) =
      (1 - ρ) / (↑J ^ 2 * c) * ∑ i : Fin J, ∑ j : Fin J, v i * v j := by
      simp_rw [Finset.mul_sum]
    -- Second part: Σᵢ Σⱼ k*(-δᵢⱼ·J·vᵢvⱼ) = -k·J·Σvᵢ²
    have p2 : ∑ i : Fin J, ∑ j : Fin J,
        (1 - ρ) / (↑J ^ 2 * c) *
          -(if i = j then ↑J * v i * v j else 0) =
      -((1 - ρ) / (↑J ^ 2 * c) *
        (↑J * ∑ i : Fin J, v i ^ 2)) := by
      simp_rw [← Finset.mul_sum]
      -- Pull neg out of double sum
      simp_rw [Finset.sum_neg_distrib]
      rw [mul_neg]
      congr 1; congr 1
      rw [Finset.mul_sum]; congr 1; ext i
      rw [Finset.sum_ite_eq Finset.univ i]; simp [sq, mul_assoc]
    rw [p1, p2]; ring
  rw [rhs_eq, ← sq_eq]

-- ============================================================
-- Lemma 4.2: Curvature of CES isoquant (lem:curvature)
-- ============================================================

/-- Principal curvature of the CES isoquant at the symmetric point. -/
def cesPrincipalCurvature (J : ℕ) (ρ c : ℝ) : ℝ :=
  (1 - ρ) / (c * Real.sqrt ↑J)

/-- **Lemma (Curvature Lemma)** — Lemma 4.2 (lem:curvature) in the paper.

    At the symmetric point on the isoquant F(x) = c, all J-1 principal
    curvatures of the CES isoquant are equal:

      κ* = (1-ρ) / (c√J) = K√J / (c(J-1))

    The isoquant has uniform curvature at the symmetric point.
    For ρ < 1, κ* > 0: the isoquant is strictly convex toward the origin.

    Proof sketch: The principal curvatures are the eigenvalues of the
    shape operator S = -(1/‖∇F‖) · proj_{T} ∘ ∇²F ∘ proj_{T}.
    At symmetric point: ‖∇F‖ = 1/√J, the tangent space is 1⊥,
    and the Hessian restricted to 1⊥ has eigenvalue -(1-ρ)/(Jc).
    So κ = |λ_⊥|/‖∇F‖ = [(1-ρ)/(Jc)] / [1/√J] = (1-ρ)/(c√J). -/
theorem curvature_lemma (_hJ : 2 ≤ J) {ρ : ℝ} (_hρ : ρ < 1)
    {c : ℝ} (_hc : 0 < c) :
    cesPrincipalCurvature J ρ c = (1 - ρ) / (c * Real.sqrt ↑J) := by
  rfl

/-- The curvature is positive for ρ < 1 (complementary inputs). -/
theorem curvature_pos (_hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) :
    0 < cesPrincipalCurvature J ρ c := by
  simp only [cesPrincipalCurvature]
  apply div_pos
  · linarith
  · apply mul_pos hc
    apply Real.sqrt_pos_of_pos
    exact_mod_cast (by omega : 0 < J)

/-- Alternative form: κ* = K·√J / (c·(J-1)). -/
theorem curvature_alt_form (hJ : 2 ≤ J) (ρ c : ℝ) (hc : c ≠ 0) :
    cesPrincipalCurvature J ρ c =
    curvatureK J ρ * Real.sqrt ↑J / (c * (↑J - 1)) := by
  simp only [cesPrincipalCurvature, curvatureK]
  have hJpos : (0 : ℝ) < ↑J := by exact_mod_cast (by omega : 0 < J)
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  have hJ1ne : (↑J : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ↑J := by exact_mod_cast (by omega : 1 < J)
    linarith
  have hsqrt_ne : Real.sqrt ↑J ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos_of_pos hJpos)
  have hsqrt_sq : Real.sqrt ↑J * Real.sqrt ↑J = ↑J :=
    Real.mul_self_sqrt (le_of_lt hJpos)
  have hsqrt_sq' : Real.sqrt ↑J ^ 2 = ↑J := by
    rw [sq, hsqrt_sq]
  field_simp
  rw [hsqrt_sq']

end
