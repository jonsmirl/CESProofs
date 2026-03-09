/-
  General CES Hessian at Arbitrary Allocation

  Resolves Gap #11: the CES Hessian was only computed at the symmetric
  point x = c·1. This file computes it at ANY allocation x.

  THE MAIN RESULT: For the CES power mean F(x) = ((1/J)Σ x_j^ρ)^{1/ρ},
  the Hessian quadratic form at a general allocation x is:

    v^T · Hess(F)(x) · v = -(1-ρ) · F(x) · Var_P[v_j/x_j]

  where P_j = x_j^ρ / Σ x_k^ρ is the escort distribution and the
  variance is Var_P[f] = E_P[f²] - (E_P[f])².

  This immediately implies:
  (a) Concavity for ρ < 1 (Var ≥ 0, so QF ≤ 0)
  (b) Euler zero-eigenvalue: v = x gives Var_P[1] = 0, so QF = 0
  (c) At x = c·1: reduces to the symmetric Hessian cesHessianQF
  (d) Effective curvature K_eff(x) = (1-ρ)(1-H(P)), where H(P) = Σ P_j²
      is the escort Herfindahl index

  The formula H_{ij} = F(1-ρ)·[P_iP_j/x_ix_j] for i≠j and
  H_{ii} = F(1-ρ)·P_i(P_i-1)/x_i² arises from:
    ∂F/∂x_i = F · P_i / x_i
    ∂²F/∂x_i∂x_j = F(1-ρ) · P_iP_j / (x_ix_j)    [i≠j]
    ∂²F/∂x_i² = F · P_i/x_i² · [(1-ρ)(P_i-1)]     [i=j]

  The algebraic core is the MULTINOMIAL COVARIANCE IDENTITY:
    Σ_i Σ_j (P_iP_j - δ_{ij}P_i) w_i w_j = (ΣP_iw_i)² - ΣP_iw_i²

  which says the quadratic form of M = PP^T - diag(P) equals -(variance).
-/

import CESProofs.Foundations.Hessian
import CESProofs.Foundations.GeneralWeights
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Chebyshev

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Section 1: Definitions
-- ============================================================

/-- The (i,j) entry of the CES Hessian matrix at a general allocation x,
    parameterized by the output level F, the escort distribution P,
    and the input vector x.

    For i ≠ j: H_{ij} = F(1-ρ) · P_i · P_j / (x_i · x_j)
    For i = j: H_{ii} = F(1-ρ) · P_i(P_i - 1) / x_i² -/
def cesGeneralHessianEntry (ρ F : ℝ)
    (P x : Fin J → ℝ) (i j : Fin J) : ℝ :=
  if i = j then
    F * (1 - ρ) * P i * (P i - 1) / (x i) ^ 2
  else
    F * (1 - ρ) * P i * P j / (x i * x j)

/-- The Hessian quadratic form v^T · H(x) · v at a general allocation,
    computed as the double sum of H_{ij} · v_i · v_j. -/
def cesGeneralHessianQF (ρ F : ℝ)
    (P x v : Fin J → ℝ) : ℝ :=
  ∑ i : Fin J, ∑ j : Fin J,
    cesGeneralHessianEntry ρ F P x i j * v i * v j

/-- Escort Herfindahl index: H(P) = Σ P_j².
    Measures concentration of the escort distribution.
    H = 1/J at symmetry, H = 1 when one input dominates. -/
def escortHerfindahl (P : Fin J → ℝ) : ℝ :=
  ∑ j, P j ^ 2

/-- Effective curvature at a general allocation:
    K_eff(x) = (1-ρ)(1 - H(P(x))).

    At symmetry (P_j = 1/J): K_eff = (1-ρ)(J-1)/J = K.
    As allocation concentrates (H → 1): K_eff → 0.
    The economy loses curvature as it becomes dominated
    by a single input. -/
def effectiveCurvatureAt (ρ : ℝ) (P : Fin J → ℝ) : ℝ :=
  (1 - ρ) * (1 - escortHerfindahl P)

-- ============================================================
-- Section 2: Core Algebraic Lemma (Multinomial Covariance)
-- ============================================================

/-- **Multinomial Covariance Identity**: The quadratic form of
    M = PP^T - diag(P) equals (E[w])² - E[w²] = -Var[w].

    This is the algebraic heart of the general Hessian formula.
    It holds for ANY vectors P and w — no probability assumptions needed.

    Proved: split into rank-1 and diagonal parts, then simplify. -/
private lemma multinomial_qf (P w : Fin J → ℝ) :
    ∑ i : Fin J, ∑ j : Fin J,
      (P i * P j - if i = j then P i else 0) *
        w i * w j =
    (∑ k, P k * w k) ^ 2 - ∑ k, P k * w k ^ 2 := by
  have h_split : ∀ i j : Fin J,
      (P i * P j - if i = j then P i else 0) *
        w i * w j =
      P i * w i * (P j * w j) -
        (if i = j then P i * w i ^ 2 else 0) := by
    intro i j
    split_ifs with h <;> [subst h; skip] <;> ring
  simp_rw [h_split, Finset.sum_sub_distrib]
  congr 1
  · rw [sq, Fintype.sum_mul_sum]
  · congr 1; ext i
    rw [Finset.sum_ite_eq Finset.univ i]; simp

-- ============================================================
-- Section 3: The Main Theorem
-- ============================================================

/-- **General Hessian = Negative Variance** (resolves Gap #11).

    The CES Hessian quadratic form at any allocation $\mathbf{x}$ equals:

    $$\mathbf{v}^\top H(\mathbf{x})\,\mathbf{v} = -(1-\rho)\,F\,\operatorname{Var}_P\!\left[\frac{v_j}{x_j}\right]$$

    where $P$ is the escort distribution ($P_j = x_j^\rho / \sum_k x_k^\rho$)
    and $\operatorname{Var}_P[f] = \mathbb{E}_P[f^2] - (\mathbb{E}_P[f])^2$.

    This is the general version of `cesHessianQF_on_perp`, valid at
    any allocation, not just the symmetric point.

    **Proof.** Substitute $w_j = v_j / x_j$ into each entry $H_{ij}\,v_i\,v_j$.
    The diagonal terms contribute $F(1-\rho)\,P_j(P_j - 1)\,w_j^2$
    and the off-diagonal terms contribute $F(1-\rho)\,P_i P_j\,w_i w_j$.
    Summing over all $i,j$ and applying the multinomial covariance identity
    $$\sum_{i,j} P_i P_j\,w_i w_j - \sum_j P_j\,w_j^2 = \left(\sum_j P_j w_j\right)^2 - \sum_j P_j w_j^2$$
    yields $-(1-\rho)\,F\,\operatorname{Var}_P[w]$. -/
theorem cesGeneralHessianQF_eq_neg_variance
    (ρ F : ℝ) (P x v : Fin J → ℝ)
    (hx : ∀ j, x j ≠ 0) :
    cesGeneralHessianQF ρ F P x v =
      -(1 - ρ) * F *
        ((∑ k, P k * (v k / x k) ^ 2) -
         (∑ k, P k * (v k / x k)) ^ 2) := by
  unfold cesGeneralHessianQF cesGeneralHessianEntry
  -- Rewrite each H_{ij} v_i v_j in terms of w_j = v_j/x_j
  have h_entry : ∀ i j : Fin J,
      (if i = j then
        F * (1 - ρ) * P i * (P i - 1) / (x i) ^ 2
      else
        F * (1 - ρ) * P i * P j / (x i * x j)) *
        v i * v j =
      F * (1 - ρ) *
        ((P i * P j - if i = j then P i else 0) *
          (v i / x i) * (v j / x j)) := by
    intro i j
    split_ifs with h
    · subst h; field_simp
    · field_simp; ring
  simp_rw [h_entry]
  -- Pull F(1-ρ) out of the double sum
  have pull_const : ∀ (c : ℝ) (f : Fin J → Fin J → ℝ),
      ∑ i : Fin J, ∑ j : Fin J, c * f i j =
      c * ∑ i : Fin J, ∑ j : Fin J, f i j := by
    intro c f
    simp_rw [← Finset.mul_sum]
  rw [pull_const]
  rw [multinomial_qf P (fun j => v j / x j)]
  ring

-- ============================================================
-- Section 4: Consequences
-- ============================================================

/-- **Weighted Variance Non-negativity**: E_P[w²] ≥ (E_P[w])²
    for any probability distribution P (P_j ≥ 0, Σ P_j = 1).

    **Proof.** E_P[(w - μ)²] = E_P[w²] - μ² ≥ 0, since each
    P_j(w_j - μ)² ≥ 0. -/
theorem weighted_variance_nonneg
    (P w : Fin J → ℝ)
    (hP_nonneg : ∀ j, 0 ≤ P j)
    (hP_sum : ∑ j, P j = 1) :
    0 ≤ (∑ k, P k * w k ^ 2) -
      (∑ k, P k * w k) ^ 2 := by
  set μ := ∑ k, P k * w k
  suffices h : 0 ≤ ∑ k, P k * (w k - μ) ^ 2 by
    have expand : (∑ k, P k * (w k - μ) ^ 2) =
        (∑ k, P k * w k ^ 2) - μ ^ 2 := by
      have h1 : ∀ k : Fin J,
          P k * (w k - μ) ^ 2 =
          P k * w k ^ 2 - 2 * μ * (P k * w k) +
          μ ^ 2 * P k := by intro k; ring
      simp_rw [h1]
      simp only [Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum,
        hP_sum]
      ring
    linarith
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (hP_nonneg k) (sq_nonneg _)

/-- **General Concavity** (ρ < 1, F > 0): The Hessian QF is ≤ 0
    at any allocation where the escort distribution is a valid
    probability distribution.

    This proves CES concavity WITHOUT restricting to the symmetric
    point. The same result holds everywhere on the domain.

    **Proof.** Rewrite the quadratic form as $v^T H v = -(1-\rho) F \cdot \operatorname{Var}_P[v/x]$ using the escort-weighted variance identity. Since $1-\rho > 0$, $F > 0$, and variance is nonneg, the product is $\leq 0$. -/
theorem cesGeneralHessianQF_neg_semidef
    {ρ : ℝ} (hρ : ρ < 1) {F : ℝ} (hF : 0 < F)
    (P : Fin J → ℝ)
    (hP_nn : ∀ j, 0 ≤ P j)
    (hP_sum : ∑ j, P j = 1)
    (x v : Fin J → ℝ) (hx : ∀ j, x j ≠ 0) :
    cesGeneralHessianQF ρ F P x v ≤ 0 := by
  rw [cesGeneralHessianQF_eq_neg_variance ρ F P x v hx]
  have hvar := weighted_variance_nonneg P
    (fun j => v j / x j) hP_nn hP_sum
  have h1 : 0 < (1 - ρ) * F := mul_pos (by linarith) hF
  nlinarith

/-- **Euler Zero-Eigenvalue**: v = x gives QF = 0,
    because v_j/x_j = 1 for all j and Var_P[1] = 0.

    This is Euler's theorem for homogeneous functions:
    the Hessian annihilates the radial direction. -/
theorem cesGeneralHessianQF_euler (ρ F : ℝ)
    (P x : Fin J → ℝ)
    (hx : ∀ j, x j ≠ 0) (hP : ∑ j, P j = 1) :
    cesGeneralHessianQF ρ F P x x = 0 := by
  rw [cesGeneralHessianQF_eq_neg_variance ρ F P x x hx]
  have h1 : ∀ k : Fin J, x k / x k = 1 :=
    fun k => div_self (hx k)
  simp_rw [h1, one_pow, mul_one, hP, one_pow,
    sub_self, mul_zero]

-- ============================================================
-- Section 5: Effective Curvature
-- ============================================================

/-- **Effective Curvature at Symmetry**: When P_j = 1/J,
    K_eff = (1-ρ)(1 - 1/J) = (1-ρ)(J-1)/J = K.

    The general effective curvature reduces to the standard
    curvature K at the symmetric allocation.

    **Proof.** At symmetry $P_j = 1/J$ for all $j$, so the escort Herfindahl is $H = J \cdot (1/J)^2 = 1/J$. Then $K_{\mathrm{eff}} = (1-\rho)(1-1/J) = (1-\rho)(J-1)/J = K$ by unfolding definitions and simplifying with `field_simp`. -/
theorem effectiveCurvature_at_symmetry (hJ : 0 < J) (ρ : ℝ) :
    effectiveCurvatureAt ρ
      (fun _ : Fin J => (1 : ℝ) / ↑J) =
      curvatureK J ρ := by
  unfold effectiveCurvatureAt escortHerfindahl curvatureK
  simp only [Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul]
  have hJne : (↑J : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **Effective Curvature Matches General Weights**: K_eff(x) at
    escort probabilities P equals the general-weight curvature
    K(ρ, P) = (1-ρ)(1 - Σ P_j²) from Paper 2b.

    This proves the conjecture from Gap #11: the effective curvature
    at a non-symmetric allocation with escort distribution P is
    EXACTLY the general-weight curvature K(ρ, a) evaluated at
    weights a = P. -/
theorem effectiveCurvature_eq_generalK (ρ : ℝ)
    (P : Fin J → ℝ) :
    effectiveCurvatureAt ρ P = generalCurvatureK J ρ P := by
  simp only [effectiveCurvatureAt, escortHerfindahl,
    generalCurvatureK]

/-- **Effective Curvature Decreases with Concentration**:
    Higher escort Herfindahl (more concentrated allocation) means
    lower effective curvature. As one input dominates (H → 1),
    the effective curvature vanishes.

    Economic interpretation: a diversified economy (low H) has
    high complementarity curvature and strong gains from variety.
    A concentrated economy (high H, one dominant sector) has
    low curvature — complementarity effects are negligible.

    **Proof.** Since $K_{\mathrm{eff}} = (1-\rho)(1 - H)$ and $1 - \rho > 0$, higher Herfindahl $H$ directly reduces $1 - H$, making the product smaller. The strict inequality $H_1 < H_2$ implies $(1-\rho)(1 - H_2) < (1-\rho)(1 - H_1)$ by `nlinarith`. -/
theorem effectiveCurvature_decreasing {ρ : ℝ} (hρ : ρ < 1)
    (P₁ P₂ : Fin J → ℝ)
    (hH : escortHerfindahl P₁ < escortHerfindahl P₂) :
    effectiveCurvatureAt ρ P₂ < effectiveCurvatureAt ρ P₁ := by
  unfold effectiveCurvatureAt
  have h1 : 0 < 1 - ρ := by linarith
  nlinarith

/-- **Maximum Curvature at Symmetry**: For a probability
    distribution P with Σ P_j = 1, the Herfindahl is minimized
    at the uniform distribution (H = 1/J), so K_eff is maximized
    at symmetry. This is stated as: K_eff(x) ≤ K for all x. -/
theorem effectiveCurvature_le_K {ρ : ℝ} (hρ : ρ < 1)
    (P : Fin J → ℝ) (hP_nn : ∀ j, 0 ≤ P j)
    (hP_sum : ∑ j, P j = 1)
    (hJ : 0 < J) :
    effectiveCurvatureAt ρ P ≤ curvatureK J ρ := by
  -- Cauchy-Schwarz: (Σ P_j)² ≤ J · Σ P_j²
  have hCS : (∑ j : Fin J, P j) ^ 2 ≤
      ↑J * ∑ j : Fin J, P j ^ 2 := by
    have h := @sq_sum_le_card_mul_sum_sq (Fin J) ℝ
      _ _ _ _ Finset.univ P
    simp only [Finset.card_fin] at h; exact h
  rw [hP_sum] at hCS; simp only [one_pow] at hCS
  have hJpos : (0 : ℝ) < ↑J := Nat.cast_pos.mpr hJ
  -- 1 ≤ J · H, so 1/J ≤ H
  have hH : 1 / ↑J ≤ ∑ j : Fin J, P j ^ 2 := by
    rw [div_le_iff₀ hJpos]; linarith
  -- K_eff = (1-ρ)(1-H) ≤ (1-ρ)(1-1/J) = (1-ρ)(J-1)/J = K
  unfold effectiveCurvatureAt escortHerfindahl curvatureK
  have h1ρ : 0 < 1 - ρ := by linarith
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  -- Rewrite K as (1-ρ)(1-1/J)
  rw [show (1 - ρ) * (↑J - 1) / ↑J =
    (1 - ρ) * (1 - 1 / ↑J) from by field_simp]
  -- (1-ρ)(1-H) ≤ (1-ρ)(1-1/J) since H ≥ 1/J
  apply mul_le_mul_of_nonneg_left _ h1ρ.le
  linarith

-- ============================================================
-- Section 6: Symmetric Specialization
-- ============================================================

/-- **Symmetric Specialization**: At x = c·1 with P = (1/J,...,1/J),
    the general Hessian quadratic form reduces to the symmetric
    cesHessianQF defined in Hessian.lean.

    This confirms that the general formula is consistent with the
    earlier symmetric computation. -/
theorem generalHessianQF_specializes_to_symmetric
    (hJ : 0 < J) (ρ c : ℝ) (hc : c ≠ 0)
    (v : Fin J → ℝ) :
    -(1 - ρ) * c *
      ((∑ k : Fin J,
          (1 : ℝ) / ↑J * (v k / c) ^ 2) -
       (∑ k : Fin J,
          (1 : ℝ) / ↑J * (v k / c)) ^ 2) =
    cesHessianQF J ρ c v := by
  simp only [cesHessianQF]
  have hJne : (↑J : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  -- Simplify the weighted sums
  have h1 : ∀ k : Fin J,
      (1 : ℝ) / ↑J * (v k / c) ^ 2 =
      v k ^ 2 / (↑J * c ^ 2) := by
    intro k; field_simp
  have h2 : ∀ k : Fin J,
      (1 : ℝ) / ↑J * (v k / c) =
      v k / (↑J * c) := by
    intro k; field_simp
  simp_rw [h1, h2, ← Finset.sum_div]
  field_simp
  ring

-- ============================================================
-- Section 7: General Bridge (Escort Fisher QF)
-- ============================================================

/-- The escort Fisher information quadratic form at a general allocation:
    I_Fisher(v) = ρ² · Var_P[v_j/x_j]

    where P is the escort distribution and Var_P is the P-weighted variance.
    At the symmetric point x = c·1, this reduces to
    ρ²/(Jc²) · ‖v_⊥‖² = escortFisherEigenvalue · ‖v_⊥‖². -/
def escortFisherQF (ρ : ℝ) (P x v : Fin J → ℝ) : ℝ :=
  ρ ^ 2 * ((∑ k, P k * (v k / x k) ^ 2) -
            (∑ k, P k * (v k / x k)) ^ 2)

/-- **General Bridge (Quadratic Form)**: At ANY allocation x,

      v^T · H^F(x) · v = -((1-ρ)/ρ²) · F · (v^T · I_Fisher(x) · v)

    The bridge ratio (1-ρ)/ρ² is universal — it depends only on ρ,
    not on the allocation x or the escort distribution P(x).

    This extends the symmetric bridge theorem (InformationGeometry.lean)
    to arbitrary allocations. The symmetric version is the special case
    where P_j = 1/J and x_j = c for all j.

    Proved: pure algebra from cesGeneralHessianQF_eq_neg_variance. -/
theorem general_bridge_qf (ρ F : ℝ) (P x v : Fin J → ℝ)
    (hx : ∀ j, x j ≠ 0) (hρ : ρ ≠ 0) :
    cesGeneralHessianQF ρ F P x v =
      -((1 - ρ) / ρ ^ 2) * F * escortFisherQF ρ P x v := by
  rw [cesGeneralHessianQF_eq_neg_variance ρ F P x v hx]
  simp only [escortFisherQF]
  have hρ2 : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  field_simp

/-- The escort Fisher QF is non-negative for any probability distribution. -/
theorem escortFisherQF_nonneg (ρ : ℝ) (P x v : Fin J → ℝ)
    (hP_nn : ∀ j, 0 ≤ P j) (hP_sum : ∑ j, P j = 1) :
    0 ≤ escortFisherQF ρ P x v := by
  simp only [escortFisherQF]
  apply mul_nonneg (sq_nonneg ρ)
  exact weighted_variance_nonneg P (fun j => v j / x j) hP_nn hP_sum

/-- The escort Fisher QF vanishes on the radial direction v = x,
    because v_j/x_j = 1 for all j and Var_P[1] = 0.
    This reflects the fact that scaling all inputs uniformly
    provides no information about the substitution parameter. -/
theorem escortFisherQF_zero_radial (ρ : ℝ) (P x : Fin J → ℝ)
    (hx : ∀ j, x j ≠ 0) (hP : ∑ j, P j = 1) :
    escortFisherQF ρ P x x = 0 := by
  simp only [escortFisherQF]
  have h1 : ∀ k : Fin J, x k / x k = 1 := fun k => div_self (hx k)
  simp_rw [h1, one_pow, mul_one, hP, one_pow, sub_self, mul_zero]

end
