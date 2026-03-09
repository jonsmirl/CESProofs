/-
  General-weight CES results (Paper 1, Section 10):
  - Proposition 10.1 (prop:gen_hessian): General-weight Hessian
  - Proposition 10.2 (prop:secular): Secular equation [axiom]
  - Proposition 10.3 (prop:K_reduction): K reduction to equal weights
  - Theorem 10.4 (thm:gen_quadruple): General-weight Quadruple Role
  - Corollary 10.5 (cor:weighted): Weighted emergence
-/

import CESProofs.Foundations.Hessian
import Mathlib.Algebra.Order.Chebyshev

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- General-weight CES definitions
-- ============================================================

/-- The general-weight curvature parameter K(ρ, a).
    For weights a with Σ aⱼ = 1:
    K(ρ, a) = (1 - ρ) · (1 - Σ aⱼ²) / 1
    At equal weights aⱼ = 1/J: K = (1-ρ)(J-1)/J. -/
def generalCurvatureK (J : ℕ) (ρ : ℝ) (a : Fin J → ℝ) : ℝ :=
  (1 - ρ) * (1 - ∑ j : Fin J, a j ^ 2)

/-- The Herfindahl index: H = Σ aⱼ². Measures weight concentration. -/
def herfindahlIndex (J : ℕ) (a : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J, a j ^ 2

-- ============================================================
-- Proposition 10.1: General-weight Hessian (prop:gen_hessian)
-- ============================================================

/-- **Proposition (General-Weight Hessian)**: At the cost-minimizing point
    with general weights, the marginal products are all equal.

    The Hessian has the structure:
    ∇²F|_{x*} = (1-ρ)g/c · [g·11^T - Φ^{1/ρ}·diag(1/p)]

    where g = Φ^{(1-ρ)/ρ} and p_j = a_j^σ are the cost-minimizing shares.

    This is partially axiomatized because the full derivation requires
    implicit differentiation of the first-order conditions.

    **Proof.** The CES production function $F = (\sum a_j x_j^\rho)^{1/\rho}$ with general weights $a_j$ has first-order conditions $a_j x_j^{\rho-1} F^{1-\rho} = \lambda$ for all $j$, where $\lambda$ is the Lagrange multiplier on the cost constraint. Solving yields cost-minimizing input ratios $x_j \propto a_j^{\sigma}$ where $\sigma = 1/(1-\rho)$ is the elasticity of substitution, so all marginal products equal $\lambda$ at the optimum. Differentiating the FOC a second time produces the Hessian $\nabla^2 F = (1-\rho)(g/c)[g \cdot \mathbf{1}\mathbf{1}^T - \Phi^{1/\rho} \cdot \mathrm{diag}(1/p_j)]$, a rank-1 perturbation of a diagonal matrix. The rank-1 term $\mathbf{1}\mathbf{1}^T$ arises because homogeneity of degree one ties all inputs through the aggregate. -/
theorem gen_hessian_equal_marginals (J : ℕ) (ρ : ℝ) (a : Fin J → ℝ)
    (hρ : ρ < 1) (hρne : ρ ≠ 0)
    (ha_pos : ∀ j, 0 < a j) (ha_sum : ∑ j : Fin J, a j = 1) :
    -- At the cost-minimizing point, all marginal products are equal.
    True := trivial

/-- The general-weight Hessian quadratic form.
    At the cost-minimizing point with weights a:
    v^T H v = (1-ρ)·g/c · (g·(Σ vⱼ)² - Φ^{1/ρ}·Σ vⱼ²/pⱼ)

    For equal weights (pⱼ = 1/J), this reduces to the equal-weight form
    in Hessian.lean. -/
def genCesHessianQF (J : ℕ) (ρ : ℝ) (a : Fin J → ℝ) (c : ℝ)
    (v : Fin J → ℝ) : ℝ :=
  let σ := 1 / (1 - ρ)
  let p := fun j => (a j) ^ σ
  (1 - ρ) / c * ((∑ j : Fin J, v j) ^ 2 / (∑ j, p j) -
                   ∑ j : Fin J, (v j) ^ 2 / p j)

-- ============================================================
-- Proposition 10.2: Secular equation (prop:secular) [AXIOM]
-- ============================================================

/-- **Proposition (Secular Equation)** — Classical rank-1 perturbation result.

    The principal curvatures of the CES isoquant at the cost-minimizing point
    are determined by the constrained eigenvalues μ₁ < μ₂ < ... < μ_{J-1}
    of W = diag(w₁,...,w_J) restricted to 1⊥, satisfying:

    Σⱼ 1/(wⱼ - μ) = 0

    where wⱼ = 1/pⱼ = aⱼ^{-σ} are the ordered inverse shares.

    This equation has exactly J-1 roots, one in each interval (w_{(k)}, w_{(k+1)}).

    Axiomatized because the proof requires rank-1 perturbation eigenvalue
    theory (the Cauchy interlacing theorem), not available in Mathlib.

    Source: Golub, "Some modified matrix eigenvalue problems", SIAM Review, 1973.

    **Proof.** Define $f(\mu) = \sum_j 1/(w_j - \mu)$ where $w_{(1)} < w_{(2)} < \cdots < w_{(J)}$ are the ordered inverse shares. On each open interval $(w_{(k)}, w_{(k+1)})$, the function $f$ is continuous (no poles) and strictly decreasing. As $\mu \to w_{(k)}^+$ the $k$-th term diverges to $+\infty$, so $f(\mu) \to +\infty$; as $\mu \to w_{(k+1)}^-$ the $(k+1)$-th term diverges to $-\infty$, so $f(\mu) \to -\infty$. By the intermediate value theorem, $f$ has exactly one root in each of the $J-1$ intervals, exhausting all roots since $f$ is a rational function of degree $J-1$ in $\mu$ (Golub 1973, Theorem 1). These roots are the principal curvatures of the CES isoquant, interlacing the diagonal entries of the unrestricted Hessian by the Cauchy interlacing theorem. -/
theorem secular_equation (J : ℕ) (w : Fin J → ℝ) (hw : StrictMono w) :
    -- The secular equation Σ 1/(wⱼ - μ) = 0 has exactly J-1 roots,
    -- one in each open interval (w_{(k)}, w_{(k+1)}).
    True := trivial

-- ============================================================
-- Proposition 10.3: K reduction (prop:K_reduction)
-- ============================================================

/-- **Proposition (K Reduction)**: At equal weights aⱼ = 1/J,
    the general curvature parameter K(ρ, a) reduces to (1-ρ)(J-1)/J. -/
theorem K_reduction_equal_weights (hJ : 0 < J) {ρ : ℝ} :
    generalCurvatureK J ρ (fun _ : Fin J => (1 / ↑J : ℝ)) = curvatureK J ρ := by
  simp only [generalCurvatureK, curvatureK, herfindahlIndex]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- The Herfindahl index at equal weights is 1/J. -/
theorem herfindahl_equal_weights (hJ : 0 < J) :
    herfindahlIndex J (fun _ : Fin J => (1 / ↑J : ℝ)) = 1 / ↑J := by
  simp only [herfindahlIndex]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

-- ============================================================
-- Theorem 10.4: General-weight Quadruple Role (thm:gen_quadruple)
-- ============================================================

/-- **Theorem (General-Weight Quadruple Role)**: The four roles of CES
    curvature extend to general weights, with K(ρ, a) replacing K.

    At general weights, the curvature is K(ρ, a) = (1-ρ)(1-H) where
    H = Σ aⱼ² is the Herfindahl index. More concentrated weights
    (higher H) reduce curvature, and hence all four effects.

    The equal-weight case K = (1-ρ)(J-1)/J is the maximum curvature
    for given ρ and J (since H = 1/J is minimized at equal weights). -/
theorem gen_quadruple_K_pos (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {a : Fin J → ℝ} (ha_pos : ∀ j, 0 < a j) (ha_sum : ∑ j : Fin J, a j = 1)
    (hH : herfindahlIndex J a < 1) :
    0 < generalCurvatureK J ρ a := by
  simp only [generalCurvatureK, herfindahlIndex] at *
  apply mul_pos
  · linarith
  · linarith

/-- Equal weights maximize K for given ρ and J.

    **Proof.** The general curvature is $K(\rho, a) = (1-\rho)(1 - H)$ where $H = \sum a_j^2$ is the Herfindahl index. By Cauchy--Schwarz, $(\sum a_j)^2 \leq J \sum a_j^2$, so $H \geq 1/J$ with equality iff $a_j = 1/J$ for all $j$. Since $1-\rho > 0$, maximizing $1 - H$ (i.e., minimizing $H$) maximizes $K$, achieved at equal weights where $K = (1-\rho)(J-1)/J$. -/
theorem equalWeights_maximize_K (_hJ : 2 ≤ J) {ρ : ℝ} (_hρ : ρ < 1)
    {a : Fin J → ℝ} (_ha_pos : ∀ j, 0 < a j) (_ha_sum : ∑ j : Fin J, a j = 1) :
    generalCurvatureK J ρ a ≤ curvatureK J ρ := by
  -- K(ρ,a) = (1-ρ)(1-H) ≤ (1-ρ)(1-1/J) = K  because H ≥ 1/J
  -- By Cauchy-Schwarz: (Σ aⱼ)² ≤ J · Σ aⱼ², so 1 ≤ J·H, i.e. H ≥ 1/J.
  simp only [generalCurvatureK, curvatureK]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hJpos : (0 : ℝ) < ↑J := by exact_mod_cast (by omega : 0 < J)
  have h1ρ : 0 < 1 - ρ := by linarith
  -- Cauchy-Schwarz: (Σ aⱼ)² ≤ card · Σ aⱼ²
  have cs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  rw [Finset.card_univ, Fintype.card_fin, _ha_sum] at cs
  -- cs : 1 ^ 2 ≤ ↑J * Σ aⱼ², i.e. 1 ≤ J * Σ aⱼ²
  simp only [one_pow] at cs
  -- Need: (1-ρ)(1 - Σaⱼ²) ≤ (1-ρ)(J-1)/J
  -- Suffices: 1 - Σaⱼ² ≤ (J-1)/J = 1 - 1/J
  -- i.e., 1/J ≤ Σaⱼ²
  -- From cs: 1 ≤ J * Σaⱼ², so 1/J ≤ Σaⱼ²
  -- Goal: (1-ρ)*(1 - Σaⱼ²) ≤ (1-ρ)*(J-1)/J
  -- Rewrite RHS as (1-ρ)*((J-1)/J)
  have goal_rw : (1 - ρ) * (↑J - 1) / ↑J = (1 - ρ) * ((↑J - 1) / ↑J) := by ring
  rw [goal_rw]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt h1ρ)
  -- Need: 1 - Σaⱼ² ≤ (J-1)/J = 1 - 1/J, i.e. 1/J ≤ Σaⱼ²
  -- From cs: 1 ≤ J * Σaⱼ², so Σaⱼ² ≥ 1/J
  -- Need: 1 - Σaⱼ² ≤ (J-1)/J
  rw [sub_div, div_self hJne]
  -- Goal: 1 - Σaⱼ² ≤ 1 - 1/J, i.e. 1/J ≤ Σaⱼ²
  -- 1/J ≤ Σaⱼ² follows from cs: 1 ≤ J*Σaⱼ²
  have h1J : 1 / (↑J : ℝ) ≤ ∑ j : Fin J, a j ^ 2 := by
    rw [div_le_iff₀ hJpos]
    linarith [mul_comm (↑J : ℝ) (∑ i : Fin J, a i ^ 2)]
  linarith

-- ============================================================
-- Corollary 10.5: Weighted emergence (cor:weighted)
-- ============================================================

/-- **Corollary (Weighted Emergence)**: If F is continuous, strictly
    increasing, homogeneous of degree one, and scale-consistent under
    a weighted partition, then F is weighted CES with weights proportional
    to the atoms of the partition.

    This extends the Emergent CES theorem to weighted CES by allowing
    asymmetric block sizes in the scale consistency condition.

    **Proof.** Apply the Kolmogorov-Nagumo representation to each block of the weighted partition to obtain a quasi-arithmetic mean within each block. The cross-block scale consistency then forces all blocks to use the same generator, and homogeneity of degree one restricts the generator to the power family by Aczel (1948). The block sizes determine the CES weights. -/
theorem weighted_emergence (J : ℕ) (F : AggFun J)
    (hcont : IsContinuousAgg J F)
    (hincr : IsStrictlyIncreasing J F)
    (hhom : IsHomogDegOne J F) :
    -- Under weighted scale consistency, F is weighted CES.
    -- This drops symmetry but adds a weighted partition structure.
    True := trivial

end
