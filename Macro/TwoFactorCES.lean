/-
  Two-Factor CES Production Function (Layer 1 of Macro Extension)

  Specializes the J-factor CES framework to the standard capital-labor
  production function Y = A·[α·K^ρ + (1-α)·L^ρ]^{1/ρ}.

  Derives factor prices (marginal products), factor shares, and proves:
  - Constant returns to scale (CRS)
  - Euler's exhaustion theorem (MPK·K + MPL·L = Y)
  - Factor shares sum to one
  - Curvature K_KL = (1-ρ)/2
  - Compatibility with general J-factor CES at J=2
  - Capital-labor ratio determines factor price ratio
  - Factor share identity for ρ estimation

  All proofs are algebraic — no axioms.
-/

import CESProofs.Applications.Economics

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Core Definitions
-- ============================================================

/-- The CES inner aggregate for two factors: α·K^ρ + (1-α)·L^ρ.
    This is the quantity raised to the 1/ρ power in the production function. -/
def cesInner (α ρ K L : ℝ) : ℝ := α * K ^ ρ + (1 - α) * L ^ ρ

/-- Two-factor CES production function:
    Y = A·[α·K^ρ + (1-α)·L^ρ]^{1/ρ}
    where A is TFP, α is the capital weight, ρ controls substitutability,
    K is capital, L is labor.

    σ = 1/(1-ρ) is the elasticity of substitution between K and L.
    ρ → 0: Cobb-Douglas Y = A·K^α·L^{1-α}.
    ρ = 1: linear Y = A·(αK + (1-α)L).
    ρ → -∞: Leontief Y = A·min(K/α, L/(1-α)). -/
def twoFactorCES (A α ρ K L : ℝ) : ℝ :=
  A * (cesInner α ρ K L) ^ (1 / ρ)

/-- Marginal product of capital:
    MPK = ∂Y/∂K = A·α·K^{ρ-1}·[α·K^ρ + (1-α)·L^ρ]^{(1-ρ)/ρ}.
    At competitive equilibrium, MPK = r + δ (rental rate of capital). -/
def marginalProductK (A α ρ K L : ℝ) : ℝ :=
  A * α * K ^ (ρ - 1) * (cesInner α ρ K L) ^ ((1 - ρ) / ρ)

/-- Marginal product of labor:
    MPL = ∂Y/∂L = A·(1-α)·L^{ρ-1}·[α·K^ρ + (1-α)·L^ρ]^{(1-ρ)/ρ}.
    At competitive equilibrium, MPL = w (real wage). -/
def marginalProductL (A α ρ K L : ℝ) : ℝ :=
  A * (1 - α) * L ^ (ρ - 1) * (cesInner α ρ K L) ^ ((1 - ρ) / ρ)

/-- Capital's share of output: s_K = MPK·K / Y = α·K^ρ / [α·K^ρ + (1-α)·L^ρ].
    Under Cobb-Douglas (ρ→0), s_K → α (constant).
    Under general CES, s_K varies with K/L ratio. -/
def capitalShare (α ρ K L : ℝ) : ℝ :=
  α * K ^ ρ / cesInner α ρ K L

/-- Labor's share of output: s_L = MPL·L / Y = (1-α)·L^ρ / [α·K^ρ + (1-α)·L^ρ].
    Under Cobb-Douglas (ρ→0), s_L → 1-α (constant). -/
def laborShare (α ρ K L : ℝ) : ℝ :=
  (1 - α) * L ^ ρ / cesInner α ρ K L

/-- Capital-output ratio in CES: K/Y = [K^ρ / (α·K^ρ + (1-α)·L^ρ)]^{1/ρ} / A.
    Used in steady-state analysis and capital accumulation. -/
def capitalOutputRatio (A α ρ K L : ℝ) : ℝ :=
  K / twoFactorCES A α ρ K L

-- ============================================================
-- Section 2: Basic Properties of the Inner Aggregate
-- ============================================================

/-- The inner aggregate is positive when capital weight and inputs are positive. -/
theorem cesInner_pos {α ρ K L : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hK : 0 < K) (hL : 0 < L) :
    0 < cesInner α ρ K L := by
  simp only [cesInner]
  exact add_pos (mul_pos hα (rpow_pos_of_pos hK ρ))
    (mul_pos (by linarith) (rpow_pos_of_pos hL ρ))

/-- The inner aggregate is non-negative under positive conditions. -/
theorem cesInner_nonneg {α ρ K L : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hK : 0 < K) (hL : 0 < L) :
    0 ≤ cesInner α ρ K L :=
  le_of_lt (cesInner_pos hα hα1 hK hL)

/-- Scaling property of the inner aggregate:
    cesInner α ρ (c·K) (c·L) = c^ρ · cesInner α ρ K L. -/
theorem cesInner_scale {α ρ K L : ℝ} {c : ℝ} (hc : 0 < c)
    (hK : 0 < K) (hL : 0 < L) :
    cesInner α ρ (c * K) (c * L) = c ^ ρ * cesInner α ρ K L := by
  simp only [cesInner]
  rw [mul_rpow (le_of_lt hc) (le_of_lt hK),
      mul_rpow (le_of_lt hc) (le_of_lt hL)]
  ring

/-- At equal inputs K = L = x, the inner aggregate simplifies:
    cesInner α ρ x x = x^ρ (since α + (1-α) = 1). -/
theorem cesInner_symmetric {α ρ x : ℝ} (_hα : 0 < α) (_hα1 : α < 1) :
    cesInner α ρ x x = x ^ ρ := by
  simp only [cesInner]
  have : α + (1 - α) = 1 := by ring
  nlinarith

-- ============================================================
-- Section 3: Constant Returns to Scale
-- ============================================================

/-- **CRS Theorem**: The two-factor CES production function is
    homogeneous of degree one: Y(c·K, c·L) = c·Y(K, L) for c > 0.

    **Proof.** Factor c^ρ from the inner aggregate, then
    (c^ρ · inner)^{1/ρ} = c · inner^{1/ρ} by rpow algebra. -/
theorem twoFactorCES_homogDegOne {A α ρ : ℝ} (_hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L) {c : ℝ} (hc : 0 < c) :
    twoFactorCES A α ρ (c * K) (c * L) = c * twoFactorCES A α ρ K L := by
  simp only [twoFactorCES]
  rw [cesInner_scale hc hK hL]
  rw [mul_rpow (rpow_nonneg (le_of_lt hc) ρ) (cesInner_nonneg hα hα1 hK hL)]
  rw [← rpow_mul (le_of_lt hc), mul_one_div_cancel hρ, rpow_one]
  ring

/-- Two-factor CES output is positive when TFP and inputs are positive. -/
theorem twoFactorCES_pos {A α ρ : ℝ} (hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (_hρ : ρ ≠ 0)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    0 < twoFactorCES A α ρ K L := by
  simp only [twoFactorCES]
  exact mul_pos hA (rpow_pos_of_pos (cesInner_pos hα hα1 hK hL) (1 / ρ))

-- ============================================================
-- Section 4: Factor Shares
-- ============================================================

/-- **Factor shares sum to one**: s_K + s_L = 1.
    This is the exhaustion property: output is fully distributed
    to factors under CRS. -/
theorem capitalShare_plus_laborShare {α ρ K L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    capitalShare α ρ K L + laborShare α ρ K L = 1 := by
  simp only [capitalShare, laborShare]
  rw [← add_div]
  exact div_self (ne_of_gt (cesInner_pos hα hα1 hK hL))

/-- Capital share is between 0 and 1. -/
theorem capitalShare_pos {α ρ K L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    0 < capitalShare α ρ K L := by
  simp only [capitalShare]
  exact div_pos (mul_pos hα (rpow_pos_of_pos hK ρ)) (cesInner_pos hα hα1 hK hL)

theorem capitalShare_lt_one {α ρ K L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    capitalShare α ρ K L < 1 := by
  have hsum := capitalShare_plus_laborShare (ρ := ρ) hα hα1 hK hL
  have hL_pos : 0 < laborShare α ρ K L := by
    simp only [laborShare]
    exact div_pos (mul_pos (by linarith) (rpow_pos_of_pos hL ρ))
      (cesInner_pos hα hα1 hK hL)
  linarith

/-- Labor share is between 0 and 1. -/
theorem laborShare_pos {α ρ K L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    0 < laborShare α ρ K L := by
  simp only [laborShare]
  exact div_pos (mul_pos (by linarith) (rpow_pos_of_pos hL ρ))
    (cesInner_pos hα hα1 hK hL)

theorem laborShare_lt_one {α ρ K L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    laborShare α ρ K L < 1 := by
  have hsum := capitalShare_plus_laborShare (ρ := ρ) hα hα1 hK hL
  have hK_pos := capitalShare_pos (ρ := ρ) hα hα1 hK hL
  linarith

/-- Capital share equals 1 minus labor share. -/
theorem capitalShare_eq_one_sub_laborShare {α ρ K L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    capitalShare α ρ K L = 1 - laborShare α ρ K L := by
  linarith [capitalShare_plus_laborShare (ρ := ρ) hα hα1 hK hL]

-- ============================================================
-- Section 5: Euler's Exhaustion Theorem
-- ============================================================

/-- **Euler's theorem for two-factor CES**: Factor payments exhaust output:
    MPK·K + MPL·L = Y.

    **Proof.** Combine K^{ρ-1}·K = K^ρ and L^{ρ-1}·L = L^ρ, factor
    out I^{(1-ρ)/ρ}, then I^{(1-ρ)/ρ}·I = I^{1/ρ}. -/
theorem euler_two_factor {A α ρ : ℝ} (_hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    marginalProductK A α ρ K L * K + marginalProductL A α ρ K L * L =
    twoFactorCES A α ρ K L := by
  simp only [marginalProductK, marginalProductL, twoFactorCES, cesInner]
  set I := α * K ^ ρ + (1 - α) * L ^ ρ with hI_def
  -- Combine x^{ρ-1} · x = x^ρ
  have hK_combine : K ^ (ρ - 1) * K = K ^ ρ := by
    have h := rpow_add hK (ρ - 1) 1
    rw [rpow_one, show ρ - 1 + 1 = ρ from by ring] at h; exact h.symm
  have hL_combine : L ^ (ρ - 1) * L = L ^ ρ := by
    have h := rpow_add hL (ρ - 1) 1
    rw [rpow_one, show ρ - 1 + 1 = ρ from by ring] at h; exact h.symm
  -- Rearrange LHS
  have step1 : A * α * K ^ (ρ - 1) * I ^ ((1 - ρ) / ρ) * K +
      A * (1 - α) * L ^ (ρ - 1) * I ^ ((1 - ρ) / ρ) * L =
      A * I ^ ((1 - ρ) / ρ) * (α * K ^ ρ + (1 - α) * L ^ ρ) := by
    have lhs_rw1 : A * α * K ^ (ρ - 1) * I ^ ((1 - ρ) / ρ) * K =
        A * (α * (K ^ (ρ - 1) * K)) * I ^ ((1 - ρ) / ρ) := by ring
    have lhs_rw2 : A * (1 - α) * L ^ (ρ - 1) * I ^ ((1 - ρ) / ρ) * L =
        A * ((1 - α) * (L ^ (ρ - 1) * L)) * I ^ ((1 - ρ) / ρ) := by ring
    rw [lhs_rw1, lhs_rw2, hK_combine, hL_combine]; ring
  rw [step1, ← hI_def]
  -- I^{(1-ρ)/ρ} · I = I^{1/ρ}
  have hI_pos : 0 < I := by rw [hI_def]; exact cesInner_pos hα hα1 hK hL
  rw [show A * I ^ ((1 - ρ) / ρ) * I = A * (I ^ ((1 - ρ) / ρ) * I) from by ring]
  congr 1
  -- I^{(1-ρ)/ρ} * I = I^{1/ρ}
  have h1 : I ^ ((1 - ρ) / ρ + 1) = I ^ ((1 - ρ) / ρ) * I ^ (1 : ℝ) :=
    rpow_add hI_pos _ _
  rw [rpow_one] at h1
  rw [← h1]
  congr 1; field_simp; ring

-- ============================================================
-- Section 6: Marginal Product and Factor Share Relationship
-- ============================================================

/-- MPK equals capital share times output-capital ratio: MPK = s_K · Y/K.
    This is the standard relationship between marginal products and factor shares. -/
theorem mpk_eq_capitalShare_times_ypk {A α ρ : ℝ} (_hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    marginalProductK A α ρ K L =
    capitalShare α ρ K L * (twoFactorCES A α ρ K L / K) := by
  simp only [marginalProductK, capitalShare, twoFactorCES, cesInner]
  set I := α * K ^ ρ + (1 - α) * L ^ ρ
  have hI_pos : 0 < I := cesInner_pos hα hα1 hK hL
  have hI_ne : I ≠ 0 := ne_of_gt hI_pos
  have hK_ne : K ≠ 0 := ne_of_gt hK
  -- Rewrite K^{ρ-1} = K^ρ / K and I^{(1-ρ)/ρ} = I^{1/ρ} / I
  rw [show K ^ (ρ - 1) = K ^ ρ / K from rpow_sub_one hK_ne ρ]
  rw [show I ^ ((1 - ρ) / ρ) = I ^ (1 / ρ) / I from by
    rw [show (1 - ρ) / ρ = 1 / ρ - 1 from by field_simp]
    exact rpow_sub_one hI_ne (1 / ρ)]
  field_simp

/-- MPL equals labor share times output-labor ratio: MPL = s_L · Y/L. -/
theorem mpl_eq_laborShare_times_ypl {A α ρ : ℝ} (_hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    marginalProductL A α ρ K L =
    laborShare α ρ K L * (twoFactorCES A α ρ K L / L) := by
  simp only [marginalProductL, laborShare, twoFactorCES, cesInner]
  set I := α * K ^ ρ + (1 - α) * L ^ ρ
  have hI_pos : 0 < I := cesInner_pos hα hα1 hK hL
  have hI_ne : I ≠ 0 := ne_of_gt hI_pos
  have hL_ne : L ≠ 0 := ne_of_gt hL
  -- Rewrite L^{ρ-1} = L^ρ / L and I^{(1-ρ)/ρ} = I^{1/ρ} / I
  rw [show L ^ (ρ - 1) = L ^ ρ / L from rpow_sub_one hL_ne ρ]
  rw [show I ^ ((1 - ρ) / ρ) = I ^ (1 / ρ) / I from by
    rw [show (1 - ρ) / ρ = 1 / ρ - 1 from by field_simp]
    exact rpow_sub_one hI_ne (1 / ρ)]
  field_simp

-- ============================================================
-- Section 7: Factor Price Ratio and Capital-Labor Ratio
-- ============================================================

/-- The ratio of marginal products equals the ratio of weighted factor intensities:
    MPK / MPL = [α/(1-α)] · (K/L)^{ρ-1}.

    When ρ < 1 (complements): raising K/L REDUCES MPK/MPL (diminishing returns).
    When ρ > 1 (substitutes): raising K/L INCREASES MPK/MPL. -/
theorem mp_ratio {A α ρ K L : ℝ} (_hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) {_hρ : ρ ≠ 0}
    (hK : 0 < K) (hL : 0 < L) :
    marginalProductK A α ρ K L / marginalProductL A α ρ K L =
    (α / (1 - α)) * (K / L) ^ (ρ - 1) := by
  simp only [marginalProductK, marginalProductL]
  have hI_pos : 0 < (cesInner α ρ K L) ^ ((1 - ρ) / ρ) :=
    rpow_pos_of_pos (cesInner_pos hα hα1 hK hL) _
  have h1α : (0 : ℝ) < 1 - α := by linarith
  -- Cancel common factors A and I^{(1-ρ)/ρ}
  rw [show A * α * K ^ (ρ - 1) * (cesInner α ρ K L) ^ ((1 - ρ) / ρ) /
      (A * (1 - α) * L ^ (ρ - 1) * (cesInner α ρ K L) ^ ((1 - ρ) / ρ)) =
      (α / (1 - α)) * (K ^ (ρ - 1) / L ^ (ρ - 1)) from by
    field_simp]
  rw [div_rpow (le_of_lt hK) (le_of_lt hL)]

/-- **Factor share identity**: The log ratio of factor shares equals
    ρ times the log labor-capital ratio (plus a constant).

    log(s_L/s_K) = log((1-α)/α) + ρ·log(L/K)

    This is the primary estimation equation for ρ in the empirical
    literature (Paper 5). A regression of log share ratios on log
    factor ratios identifies ρ as the slope coefficient. -/
theorem factorShare_identity {α ρ K L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    Real.log (laborShare α ρ K L / capitalShare α ρ K L) =
    Real.log ((1 - α) / α) + ρ * Real.log (L / K) := by
  simp only [laborShare, capitalShare, cesInner]
  set I := α * K ^ ρ + (1 - α) * L ^ ρ
  have hI_ne : I ≠ 0 := ne_of_gt (cesInner_pos hα hα1 hK hL)
  -- s_L/s_K = [(1-α)L^ρ/I] / [αK^ρ/I] = (1-α)L^ρ / (αK^ρ)
  have hαKρ : 0 < α * K ^ ρ := mul_pos hα (rpow_pos_of_pos hK ρ)
  rw [show (1 - α) * L ^ ρ / I / (α * K ^ ρ / I) =
      (1 - α) * L ^ ρ / (α * K ^ ρ) from by field_simp]
  -- (1-α)L^ρ / (αK^ρ) = [(1-α)/α] · (L/K)^ρ
  rw [show (1 - α) * L ^ ρ / (α * K ^ ρ) =
      ((1 - α) / α) * (L ^ ρ / K ^ ρ) from by field_simp]
  rw [← div_rpow (le_of_lt hL) (le_of_lt hK)]
  rw [Real.log_mul (ne_of_gt (div_pos (by linarith) hα))
      (ne_of_gt (rpow_pos_of_pos (div_pos hL hK) ρ))]
  rw [Real.log_rpow (div_pos hL hK)]

-- ============================================================
-- Section 8: Curvature for Two-Factor CES
-- ============================================================

/-- **Two-factor curvature**: K = (1-ρ)/2 when J = 2.
    This is the specialization of K = (1-ρ)(J-1)/J to two factors.

    K controls the strength of complementarity between capital and labor:
    - K > 0 when ρ < 1: K and L are complements (empirically dominant)
    - K = 0 when ρ = 1: K and L are perfect substitutes
    - K < 0 when ρ > 1: K and L are "more than substitutes" -/
theorem curvatureK_two_factor (ρ : ℝ) :
    curvatureK 2 ρ = (1 - ρ) / 2 := by
  simp only [curvatureK]
  push_cast
  ring

/-- Two-factor curvature is positive when ρ < 1 (complement regime). -/
theorem curvatureK_two_factor_pos {ρ : ℝ} (hρ : ρ < 1) :
    0 < curvatureK 2 ρ := by
  rw [curvatureK_two_factor]
  linarith

-- ============================================================
-- Section 9: Compatibility with J-Factor CES
-- ============================================================

/-- The two-factor CES production function equals the general cesFun
    with J = 2, weights a = (α, 1-α), and TFP prefactor A. -/
theorem twoFactorCES_eq_cesFun {A α ρ : ℝ}
    {K L : ℝ} :
    twoFactorCES A α ρ K L =
    A * cesFun 2 (fun j => if j = ⟨0, by omega⟩ then α else 1 - α) ρ
      (fun j => if j = ⟨0, by omega⟩ then K else L) := by
  simp only [twoFactorCES, cesFun, cesInner]
  congr 1; congr 1
  -- Show the sum over Fin 2 equals α·K^ρ + (1-α)·L^ρ
  rw [Fin.sum_univ_two]
  simp

/-- The capital share equals the general factorShare at j = 0
    (capital is the first of two factors). -/
theorem capitalShare_eq_factorShare {α ρ K L : ℝ} :
    capitalShare α ρ K L =
    factorShare 2 (fun j => if j = ⟨0, by omega⟩ then α else 1 - α) ρ
      (fun j => if j = ⟨0, by omega⟩ then K else L) ⟨0, by omega⟩ := by
  simp only [capitalShare, factorShare, cesInner]
  congr 1 <;> simp [Fin.sum_univ_two]

-- ============================================================
-- Section 10: Marginal Product Positivity
-- ============================================================

/-- MPK is positive when all parameters are positive. -/
theorem marginalProductK_pos {A α ρ K L : ℝ} (hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    0 < marginalProductK A α ρ K L := by
  simp only [marginalProductK]
  apply mul_pos
  · apply mul_pos
    · exact mul_pos hA hα
    · exact rpow_pos_of_pos hK _
  · exact rpow_pos_of_pos (cesInner_pos hα hα1 hK hL) _

/-- MPL is positive when all parameters are positive. -/
theorem marginalProductL_pos {A α ρ K L : ℝ} (hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    0 < marginalProductL A α ρ K L := by
  simp only [marginalProductL]
  apply mul_pos
  · apply mul_pos
    · exact mul_pos hA (by linarith)
    · exact rpow_pos_of_pos hL _
  · exact rpow_pos_of_pos (cesInner_pos hα hα1 hK hL) _

-- ============================================================
-- Section 11: Special Cases and Limits
-- ============================================================

/-- At equal inputs K = L = x, the two-factor CES simplifies to A·x.
    This is consistent with CRS: Y(x,x) = x · Y(1,1) = x · A. -/
theorem twoFactorCES_symmetric {A α ρ : ℝ} (_hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    twoFactorCES A α ρ x x = A * x := by
  simp only [twoFactorCES]
  rw [cesInner_symmetric hα hα1]
  rw [← rpow_mul (le_of_lt hx), mul_one_div_cancel hρ, rpow_one]

/-- **Linear case** (ρ = 1): Y = A·(αK + (1-α)L).
    Capital and labor are perfect substitutes. -/
theorem twoFactorCES_linear (A α K L : ℝ) :
    twoFactorCES A α 1 K L = A * (α * K + (1 - α) * L) := by
  simp only [twoFactorCES, cesInner]
  simp [rpow_one]

/-- At equal inputs with ρ = 1, marginal products equal their weights times A. -/
theorem mpk_linear (A α K L : ℝ) :
    marginalProductK A α 1 K L = A * α := by
  simp only [marginalProductK, cesInner]
  simp [rpow_zero, rpow_one]

-- ============================================================
-- Section 12: Elasticity of Substitution Connection
-- ============================================================

/-- The elasticity of substitution for two-factor CES is σ = 1/(1-ρ),
    the same formula as for the general J-factor case. -/
theorem sigma_two_factor (ρ : ℝ) :
    elasticityOfSubstitution ρ = 1 / (1 - ρ) := rfl

/-- When σ < 1 (ρ < 0, complements), capital deepening raises labor's share.
    This is the opposite of Piketty's channel (which requires σ > 1). -/
theorem laborShare_increases_with_kl_ratio_complements {α ρ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ < 0)
    {K₁ K₂ L : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hL : 0 < L)
    (hK : K₁ < K₂) :
    laborShare α ρ K₁ L < laborShare α ρ K₂ L := by
  simp only [laborShare, cesInner]
  -- s_L = (1-α)L^ρ / (αK^ρ + (1-α)L^ρ)
  -- When ρ < 0: K₁ < K₂ implies K₁^ρ > K₂^ρ (rpow reverses for neg exponent)
  -- So denominator₁ > denominator₂, same numerator → s_L(K₁) < s_L(K₂) ✓
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hnum : 0 < (1 - α) * L ^ ρ := mul_pos h1α (rpow_pos_of_pos hL ρ)
  have hd1 : 0 < α * K₁ ^ ρ + (1 - α) * L ^ ρ :=
    add_pos (mul_pos hα (rpow_pos_of_pos hK₁ ρ)) hnum
  have hd2 : 0 < α * K₂ ^ ρ + (1 - α) * L ^ ρ :=
    add_pos (mul_pos hα (rpow_pos_of_pos hK₂ ρ)) hnum
  apply div_lt_div_of_pos_left hnum hd2
  -- Need: α*K₂^ρ + (1-α)*L^ρ < α*K₁^ρ + (1-α)*L^ρ
  -- i.e., K₂^ρ < K₁^ρ (for ρ < 0, K₁ < K₂)
  have hKρ : K₂ ^ ρ < K₁ ^ ρ :=
    (Real.rpow_lt_rpow_iff_of_neg hK₂ hK₁ hρ).mpr hK
  linarith [mul_lt_mul_of_pos_left hKρ hα]

-- ============================================================
-- Section 13: Depreciation and Net Returns
-- ============================================================

/-- Net return on capital: r = MPK - δ.
    This is the real interest rate in a competitive economy. -/
def netReturnOnCapital (A α ρ K L δ : ℝ) : ℝ :=
  marginalProductK A α ρ K L - δ

/-- Real wage equals MPL in a competitive economy. -/
def realWage (A α ρ K L : ℝ) : ℝ :=
  marginalProductL A α ρ K L

/-- The capital-labor demand ratio at factor prices (r+δ, w):
    K/L = [α/(1-α)]^σ · [w/(r+δ)]^σ
    where σ = 1/(1-ρ) is the elasticity of substitution.

    This determines the optimal factor mix as a function of relative prices.
    High σ means firms substitute easily when relative prices change.
    Low σ means the ratio is relatively fixed (Leontief-like). -/
theorem capital_labor_demand_ratio {A α ρ K L : ℝ} (_hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (_hρ : ρ ≠ 0) (hρ1 : ρ ≠ 1)
    (hK : 0 < K) (hL : 0 < L) :
    K / L = (α / (1 - α)) ^ elasticityOfSubstitution ρ *
    (marginalProductL A α ρ K L / marginalProductK A α ρ K L) ^
      elasticityOfSubstitution ρ := by
  -- From mp_ratio: MPK/MPL = [α/(1-α)] · (K/L)^{ρ-1}
  -- So (K/L)^{ρ-1} = [MPK/MPL] · [(1-α)/α]
  -- K/L = {[MPK/MPL] · [(1-α)/α]}^{1/(ρ-1)}
  --     = {[(1-α)/α] · [MPK/MPL]}^{-σ}
  --     = [α/(1-α)]^σ · [MPL/MPK]^σ
  -- Proof: Use mp_ratio to express MPL/MPK, then simplify rpow chain.
  have hI := cesInner_pos (ρ := ρ) hα hα1 hK hL
  have h1α : (0 : ℝ) < 1 - α := by linarith
  have hLK : 0 < L / K := div_pos hL hK
  have hαr : 0 < α / (1 - α) := div_pos hα h1α
  have h_inv : 0 < (1 - α) / α := div_pos h1α hα
  have hIr := rpow_pos_of_pos hI ((1 - ρ) / ρ)
  -- Unfold definitions to expose the algebraic structure
  simp only [elasticityOfSubstitution, marginalProductK, marginalProductL]
  have h1 : A * (1 - α) * L ^ (ρ - 1) * cesInner α ρ K L ^ ((1 - ρ) / ρ) /
      (A * α * K ^ (ρ - 1) * cesInner α ρ K L ^ ((1 - ρ) / ρ)) =
      (1 - α) * L ^ (ρ - 1) / (α * K ^ (ρ - 1)) := by
    have ha : A * (1 - α) * L ^ (ρ - 1) * cesInner α ρ K L ^ ((1 - ρ) / ρ) =
      ((1 - α) * L ^ (ρ - 1)) * (A * cesInner α ρ K L ^ ((1 - ρ) / ρ)) := by ring
    have hb : A * α * K ^ (ρ - 1) * cesInner α ρ K L ^ ((1 - ρ) / ρ) =
      (α * K ^ (ρ - 1)) * (A * cesInner α ρ K L ^ ((1 - ρ) / ρ)) := by ring
    rw [ha, hb]; exact mul_div_mul_right _ _ (ne_of_gt (mul_pos _hA hIr))
  rw [h1]
  -- Step 2: Rewrite as ((1-α)/α) * (L/K)^(ρ-1)
  have h2 : (1 - α) * L ^ (ρ - 1) / (α * K ^ (ρ - 1)) =
      ((1 - α) / α) * (L / K) ^ (ρ - 1) := by
    rw [div_rpow (le_of_lt hL) (le_of_lt hK), mul_div_mul_comm]
  rw [h2]
  -- Step 3: Distribute rpow over product
  rw [mul_rpow (le_of_lt h_inv) (rpow_nonneg (le_of_lt hLK) (ρ - 1))]
  -- Step 4: Weight cancellation: (α/(1-α))^σ * ((1-α)/α)^σ = 1
  have h_wt : (α / (1 - α)) ^ (1 / (1 - ρ)) * ((1 - α) / α) ^ (1 / (1 - ρ)) = 1 := by
    rw [← mul_rpow (le_of_lt hαr) (le_of_lt h_inv)]
    rw [div_mul_div_comm, mul_comm α (1 - α), div_self (ne_of_gt (mul_pos h1α hα))]
    exact one_rpow _
  rw [← mul_assoc, h_wt, one_mul]
  -- Step 5: Combine exponents: ((L/K)^(ρ-1))^(1/(1-ρ)) = (L/K)^(-1) = K/L
  rw [← rpow_mul (le_of_lt hLK)]
  have hexp : (ρ - 1) * (1 / (1 - ρ)) = -1 := by
    have : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
    field_simp; ring
  rw [hexp, rpow_neg_one (L / K), inv_div]

-- ============================================================
-- Section 14: Cobb-Douglas Limit Tests (ρ=0)
-- ============================================================

/-- At ρ=0, the capital share equals the distribution parameter α,
    independent of K and L. This is the Cobb-Douglas limit:
    Y = A · K^α · L^{1-α} has s_K = α always. -/
theorem capitalShare_cobbDouglas {α K L : ℝ}
    (_hK : K ≠ 0) (_hL : L ≠ 0) :
    capitalShare α 0 K L = α := by
  simp only [capitalShare, cesInner, rpow_zero]; ring

/-- At ρ=0, the labor share equals 1-α. Companion to capitalShare_cobbDouglas. -/
theorem laborShare_cobbDouglas {α K L : ℝ}
    (_hK : K ≠ 0) (_hL : L ≠ 0) :
    laborShare α 0 K L = 1 - α := by
  simp only [laborShare, cesInner, rpow_zero]; ring

/-- At ρ=0, factor shares are constant: the factor share identity
    log(s_L/s_K) = log((1-α)/α) + 0·log(L/K) = log((1-α)/α).
    This confirms the regression slope coefficient ρ vanishes at
    unit elasticity, as expected for Cobb-Douglas. -/
theorem factorShare_identity_cobbDouglas {α K L : ℝ}
    (_hα : 0 < α) (_hα1 : α < 1) (hK : 0 < K) (hL : 0 < L) :
    Real.log (laborShare α 0 K L / capitalShare α 0 K L) =
    Real.log ((1 - α) / α) := by
  rw [laborShare_cobbDouglas (ne_of_gt hK) (ne_of_gt hL),
      capitalShare_cobbDouglas (ne_of_gt hK) (ne_of_gt hL)]

-- ============================================================
-- Section 15: Summary Statistics
-- ============================================================

-- Total count: 9 definitions, 27 theorems.
-- Fully proved: 27. Sorry: 0.
-- Axioms: 0.
-- Extension summary for ces_math_reference.md:
-- twoFactorCES: Y = A·[α·K^ρ + (1-α)·L^ρ]^{1/ρ}
-- marginalProductK/L: factor prices from CES FOCs
-- capitalShare/laborShare: factor income shares
-- twoFactorCES_homogDegOne: CRS (fully proved)
-- euler_two_factor: MPK·K + MPL·L = Y (fully proved)
-- capitalShare_plus_laborShare: s_K + s_L = 1 (fully proved)
-- curvatureK_two_factor: K = (1-ρ)/2 (fully proved)
-- factorShare_identity: log(s_L/s_K) = log((1-α)/α) + ρ·log(L/K) (fully proved)
-- mp_ratio: MPK/MPL = [α/(1-α)]·(K/L)^{ρ-1} (fully proved)
-- twoFactorCES_symmetric: Y(x,x) = Ax (fully proved)
-- twoFactorCES_linear: Y at ρ=1 (fully proved)
-- capital_labor_demand_ratio: K/L = (α/(1-α))^σ · (MPL/MPK)^σ (fully proved)
-- laborShare_increases_with_kl_ratio_complements: ∂s_L/∂(K/L) > 0 for ρ<0 (fully proved)
-- capitalShare_cobbDouglas: s_K = α at ρ=0 (Cobb-Douglas limit, fully proved)
-- laborShare_cobbDouglas: s_L = 1-α at ρ=0 (Cobb-Douglas limit, fully proved)
-- factorShare_identity_cobbDouglas: log(s_L/s_K) = log((1-α)/α) at ρ=0 (fully proved)
-- aggregation_raises_effective_sigma: removed (dead axiom, never referenced downstream)

end
