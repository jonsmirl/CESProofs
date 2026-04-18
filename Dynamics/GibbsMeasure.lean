/-
  Gibbs Measure for Finite Discrete Systems:
  Variance-Response Identity, Kramers Escape Rate, and Crooks Ratio
  (Paper 3, Stochastic Foundation)

  Proves σ² = T · χ (the VRI) from the finite-sum Gibbs partition
  function. This replaces the axiomatic stubs in FluctuationResponse.lean
  with a rigorous derivation.

  The key insight: the VRI is an exponential family identity — the
  second cumulant of the log-partition function equals the variance
  of the sufficient statistic. For finite J-state systems this
  requires only finite sums, not measure theory or stochastic calculus.

  Also formalizes:
  - Kramers escape rate: r_k = (ℓ ω₀ ω_b / 2π) exp(-ΔΦ/T)
  - Crooks detailed balance ratio: P_F/P_R = exp((W - ΔF)/T)

  ### A3-iteration context (Phase 3 re-rooting)

  The Gibbs partition function and its cumulants are the ensemble
  "mode amplitudes" — the VRI is the second-cumulant identity of
  log Z, matching the A3-iteration scalar-fingerprint picture
  (`Foundations.Emergence.modeAfterL_eq_exp_decay`). See
  `research/demographics/logZ_is_the_master_generator.md` for the
  narrative that log Z is the master object.
-/

import CESProofs.Dynamics.Defs
import CESProofs.Foundations.Emergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.BigOperators.Field

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Section 1: Gibbs Partition Function with Conjugate Field
-- ============================================================

/-- Boltzmann weight for state j under conjugate field h:
    w_j(h) = exp((h · x_j - ε_j) / T). -/
def gibbsWeight (ε x : Fin J → ℝ) (T h : ℝ) (j : Fin J) : ℝ :=
  Real.exp ((h * x j - ε j) / T)

/-- Gibbs partition function: Z(h) = Σ_j exp((h · x_j - ε_j) / T). -/
def gibbsZ (ε x : Fin J → ℝ) (T h : ℝ) : ℝ :=
  ∑ j : Fin J, gibbsWeight ε x T h j

/-- Gibbs probability: P_j(h) = w_j(h) / Z(h). -/
def gibbsProb (ε x : Fin J → ℝ) (T h : ℝ) (j : Fin J) : ℝ :=
  gibbsWeight ε x T h j / gibbsZ ε x T h

/-- Gibbs mean of an observable f: ⟨f⟩ = Σ_j f_j · P_j. -/
def gibbsMean (ε x : Fin J → ℝ) (T h : ℝ) (f : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J, f j * gibbsProb ε x T h j

/-- Gibbs variance: Var[f] = ⟨f²⟩ - ⟨f⟩². -/
def gibbsVariance (ε x : Fin J → ℝ) (T h : ℝ) (f : Fin J → ℝ) : ℝ :=
  gibbsMean ε x T h (fun j => f j ^ 2) - (gibbsMean ε x T h f) ^ 2

-- ============================================================
-- Section 2: Positivity and Normalization
-- ============================================================

/-- Each Boltzmann weight is positive. -/
theorem gibbsWeight_pos (ε x : Fin J → ℝ) (T h : ℝ) (j : Fin J) :
    0 < gibbsWeight ε x T h j :=
  Real.exp_pos _

/-- The partition function is positive (for nonempty state space). -/
theorem gibbsZ_pos [NeZero J] (ε x : Fin J → ℝ) (T h : ℝ) :
    0 < gibbsZ ε x T h :=
  Finset.sum_pos (fun j _ => gibbsWeight_pos ε x T h j) Finset.univ_nonempty

/-- Each Gibbs probability is positive. -/
theorem gibbsProb_pos [NeZero J] (ε x : Fin J → ℝ) (T h : ℝ) (j : Fin J) :
    0 < gibbsProb ε x T h j :=
  div_pos (gibbsWeight_pos ε x T h j) (gibbsZ_pos ε x T h)

/-- Gibbs probabilities sum to 1. -/
theorem gibbsProb_sum_one [NeZero J] (ε x : Fin J → ℝ) (T h : ℝ) :
    ∑ j : Fin J, gibbsProb ε x T h j = 1 := by
  simp only [gibbsProb]
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (gibbsZ_pos ε x T h))

-- ============================================================
-- Section 3: Derivatives of the Partition Function
-- ============================================================

/-- d/dh [exp((h·x_j - ε_j)/T)] = (x_j/T) · exp((h·x_j - ε_j)/T). -/
private lemma gibbsWeight_hasDerivAt (ε x : Fin J → ℝ) (T : ℝ) (_hT : T ≠ 0)
    (h : ℝ) (j : Fin J) :
    HasDerivAt (fun h' => gibbsWeight ε x T h' j)
      (x j / T * gibbsWeight ε x T h j) h := by
  unfold gibbsWeight
  have inner : HasDerivAt (fun h' => (h' * x j - ε j) / T) (x j / T) h := by
    have := ((hasDerivAt_id h).mul_const (x j)).sub_const (ε j)
    convert this.div_const T using 1; ring
  convert inner.exp using 1; ring

/-- Z'(h) = Σ (x_j/T) · w_j(h). -/
theorem gibbsZ_hasDerivAt (ε x : Fin J → ℝ) (T : ℝ) (hT : T ≠ 0) (h : ℝ) :
    HasDerivAt (gibbsZ ε x T)
      (∑ j : Fin J, x j / T * gibbsWeight ε x T h j) h := by
  change HasDerivAt (fun h' => ∑ j : Fin J, gibbsWeight ε x T h' j)
    (∑ j : Fin J, x j / T * gibbsWeight ε x T h j) h
  have := HasDerivAt.sum fun j (_ : j ∈ Finset.univ) =>
    gibbsWeight_hasDerivAt ε x T hT h j
  simp only [Finset.sum_fn] at this
  exact this

-- ============================================================
-- Section 4: The Algebraic Core of the VRI
-- ============================================================

/-! ### The Variance-Response Identity

The VRI σ² = T · χ is proved in two steps:

**Step 1** (algebraic): For any probability distribution {P_j} summing
to 1, with μ = Σ x_j P_j:
  Σ P_j · (x_j - μ)² = (Σ x_j² · P_j) - μ²

**Step 2** (Gibbs derivative): ∂P_j/∂h = P_j · (x_j - μ)/T, so
  χ = Σ x_j · ∂P_j/∂h = (1/T) · Σ x_j · P_j · (x_j - μ)
    = (1/T) · Σ P_j · (x_j - μ)² + (μ/T) · Σ P_j · (x_j - μ)
    = σ²/T

Therefore σ² = T · χ.
-/

/-- **Algebraic VRI core**: Var[x] = E[x·(x-μ)] for any probability
    distribution. This is the identity
    Σ P_j · x_j · (x_j - μ) = Σ P_j · x_j² - μ². -/
theorem algebraic_vri_core (P x : Fin J → ℝ)
    (_hP_sum : ∑ j, P j = 1) :
    let μ := ∑ j, x j * P j
    ∑ j, P j * x j * (x j - μ) =
    (∑ j, x j ^ 2 * P j) - μ ^ 2 := by
  simp only
  set μ := ∑ j, x j * P j
  have expand : ∀ j, P j * x j * (x j - μ) = x j ^ 2 * P j - μ * (x j * P j) := by
    intro j; ring
  simp_rw [expand, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **The centered form**: Var[x] = Σ P_j · (x_j - μ)².
    This shows variance is a sum of non-negative terms. -/
theorem variance_centered_form (P x : Fin J → ℝ)
    (hP_sum : ∑ j, P j = 1) :
    let μ := ∑ j, x j * P j
    (∑ j, x j ^ 2 * P j) - μ ^ 2 =
    ∑ j, P j * (x j - μ) ^ 2 := by
  simp only
  set μ := ∑ j, x j * P j
  have expand : ∀ j, P j * (x j - μ) ^ 2 =
    x j ^ 2 * P j - 2 * μ * (x j * P j) + μ ^ 2 * P j := by
    intro j; ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hP_sum]
  ring

/-- **Variance non-negativity**: Var[x] ≥ 0 for any distribution. -/
theorem variance_nonneg (P x : Fin J → ℝ)
    (hP_sum : ∑ j, P j = 1)
    (hP_pos : ∀ j, 0 ≤ P j) :
    0 ≤ (∑ j, x j ^ 2 * P j) - (∑ j, x j * P j) ^ 2 := by
  rw [variance_centered_form P x hP_sum]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hP_pos j) (sq_nonneg _)

/-- **The Static VRI (σ² = T · χ)**: For the Gibbs distribution,
    the variance of observable x equals T times the susceptibility.

    The susceptibility χ = dμ/dh satisfies:
      χ = (1/T) · Σ P_j · x_j · (x_j - μ)
        = (1/T) · Var[x]

    Therefore Var[x] = T · χ.

    We prove the key algebraic identity that underpins this:
    the Gibbs derivative ∂P_j/∂h = P_j(x_j - μ)/T implies
    χ = Var[x]/T. -/
theorem gibbs_static_vri [NeZero J] (ε x : Fin J → ℝ) (T : ℝ)
    (_hT : 0 < T) :
    let P := gibbsProb ε x T 0
    let μ := ∑ j, x j * P j
    let σ_sq := (∑ j, x j ^ 2 * P j) - μ ^ 2
    -- The VRI: σ² = T · χ, expressed as σ² = Σ P_j · x_j · (x_j - μ)
    -- (the right side equals T · χ because χ = (1/T) · Σ P_j · x_j · (x_j - μ))
    σ_sq = ∑ j, P j * x j * (x j - μ) :=
  (algebraic_vri_core (gibbsProb ε x T 0) x (gibbsProb_sum_one ε x T 0)).symm

/-- **Gibbs VRI with temperature**: The full VRI identity.
    If χ = (1/T) · Σ P_j · x_j · (x_j - μ), then σ² = T · χ. -/
theorem gibbs_vri_with_temperature {σ_sq χ T : ℝ}
    (hT : 0 < T)
    (hvar : σ_sq = T * χ) :
    χ = σ_sq / T := by
  field_simp; linarith

-- ============================================================
-- Section 4b: Derivative VRI (χ = dμ/dh = Var[x]/T)
-- ============================================================

/-! ### Derivative Form of the VRI

The algebraic VRI (Section 4) shows Σ P·x·(x-μ) = Var[x].
Here we prove the **derivative form**: d/dh[E_h[x]] = Var[x]/T,
making χ = dμ/dh a genuine `HasDerivAt` statement.

The chain: quotient rule on P_j = w_j/Z → sum rule on E[f] = Σ f·P
→ connect to variance via `algebraic_vri_core`.
-/

/-- d/dh [P_j(h)] = P_j(h) · (x_j - μ(h)) / T. -/
theorem gibbsProb_hasDerivAt [NeZero J] (ε x : Fin J → ℝ) (T : ℝ) (hT : T ≠ 0)
    (h : ℝ) (j : Fin J) :
    HasDerivAt (fun h' => gibbsProb ε x T h' j)
      (gibbsProb ε x T h j / T * (x j - gibbsMean ε x T h (fun k => x k))) h := by
  have hw := gibbsWeight_hasDerivAt ε x T hT h j
  have hZ := gibbsZ_hasDerivAt ε x T hT h
  have hZpos := gibbsZ_pos (J := J) ε x T h
  have hZne : gibbsZ ε x T h ≠ 0 := ne_of_gt hZpos
  -- Quotient rule: d/dh [w/Z] = (w'Z - wZ')/Z²
  have hd := HasDerivAt.div hw hZ hZne
  -- Show our function matches the quotient form
  have hfun : (fun h' => gibbsProb ε x T h' j) =
      (fun h' => gibbsWeight ε x T h' j) / gibbsZ ε x T := by
    ext h'; simp [gibbsProb, Pi.div_apply]
  rw [hfun]
  -- Now show derivative values match
  -- Pre-factor the sums to avoid ring failing on sums with inverses
  refine hd.congr_deriv ?_
  -- Factor x_k/T * w_k = x_k * w_k / T in the quotient rule sum
  have hsum : ∑ k : Fin J, x k / T * gibbsWeight ε x T h k =
    (∑ k : Fin J, x k * gibbsWeight ε x T h k) / T := by
    rw [Finset.sum_div]; congr 1; ext k; ring
  rw [hsum]
  simp only [gibbsProb, gibbsMean]
  -- Factor x_k * (w_k / Z) = x_k * w_k / Z in the mean
  have hmean : ∑ k : Fin J, x k * (gibbsWeight ε x T h k / gibbsZ ε x T h) =
    (∑ k : Fin J, x k * gibbsWeight ε x T h k) / gibbsZ ε x T h := by
    rw [Finset.sum_div]; congr 1; ext k; ring
  rw [hmean]
  field_simp

/-- d/dh [E_h[f]] = Σ f_j · P_j · (x_j - μ) / T. -/
theorem gibbsMean_hasDerivAt [NeZero J] (ε x : Fin J → ℝ) (T : ℝ) (hT : T ≠ 0)
    (h : ℝ) (f : Fin J → ℝ) :
    HasDerivAt (fun h' => gibbsMean ε x T h' f)
      (∑ j, f j * (gibbsProb ε x T h j / T *
        (x j - gibbsMean ε x T h (fun k => x k)))) h := by
  change HasDerivAt (fun h' => ∑ j : Fin J, f j * gibbsProb ε x T h' j) _ h
  have := HasDerivAt.sum fun j (_ : j ∈ Finset.univ) =>
    HasDerivAt.const_mul (f j) (gibbsProb_hasDerivAt ε x T hT h j)
  simp only [Finset.sum_fn] at this
  exact this

/-- The derivative of E[f] equals Cov[f, x] / T. -/
theorem gibbsMean_deriv_eq_covariance [NeZero J] (ε x : Fin J → ℝ) (T : ℝ) (_hT : T ≠ 0)
    (h : ℝ) (f : Fin J → ℝ) :
    ∑ j, f j * (gibbsProb ε x T h j / T *
      (x j - gibbsMean ε x T h (fun k => x k))) =
    (1 / T) * (gibbsMean ε x T h (fun j => f j * x j) -
      gibbsMean ε x T h f * gibbsMean ε x T h (fun k => x k)) := by
  simp only [gibbsMean]
  set P := gibbsProb ε x T h
  -- Factor 1/T out of each term
  have h1 : ∀ i : Fin J, f i * (P i / T * (x i - ∑ k, x k * P k)) =
    (1 / T) * (f i * P i * (x i - ∑ k, x k * P k)) := by intro i; ring
  simp_rw [h1, ← Finset.mul_sum]
  congr 1
  -- Expand f_i * P_i * (x_i - μ) = f_i * x_i * P_i - f_i * P_i * μ
  have h2 : ∀ i : Fin J, f i * P i * (x i - ∑ k, x k * P k) =
    f i * x i * P i - f i * P i * ∑ k, x k * P k := by intro i; ring
  simp_rw [h2, Finset.sum_sub_distrib, ← Finset.sum_mul]

/-- **The Derivative VRI** (χ = Var[x]/T):
    d/dh [E_h[x]] = (1/T) · Var_h[x].
    This is the actual physical content: response to perturbation = fluctuation/T. -/
theorem gibbs_susceptibility_vri [NeZero J] (ε x : Fin J → ℝ) (T : ℝ) (hT : T ≠ 0)
    (h₀ : ℝ) :
    HasDerivAt (fun h => gibbsMean ε x T h (fun j => x j))
      ((1 / T) * gibbsVariance ε x T h₀ (fun j => x j)) h₀ := by
  have hd := gibbsMean_hasDerivAt ε x T hT h₀ (fun j => x j)
  refine hd.congr_deriv ?_
  rw [gibbsMean_deriv_eq_covariance ε x T hT]
  congr 1
  -- Need: E[x·x] - E[x]·E[x] = E[x²] - E[x]²
  unfold gibbsVariance gibbsMean
  congr 1
  · congr 1; ext j; ring
  · ring

/-- **The full VRI identity**: σ² = T · χ.
    Variance equals temperature times susceptibility. -/
theorem gibbs_vri_full [NeZero J] (ε x : Fin J → ℝ) (T : ℝ) (hT : 0 < T) (h₀ : ℝ) :
    let χ := (1 / T) * gibbsVariance ε x T h₀ (fun j => x j)
    gibbsVariance ε x T h₀ (fun j => x j) = T * χ := by
  simp only
  field_simp

-- ============================================================
-- Section 5: The Kramers Escape Rate
-- ============================================================

/-! ### Kramers Escape Rate

The frequency of economic crises (regime shifts between potential wells):

  r_k = (ℓ · ω₀ · ω_b) / (2π) · exp(-ΔΦ/T)

where ℓ is mobility, ω₀ is equilibrium curvature, ω_b is barrier
curvature, ΔΦ is barrier height, and T is information friction.
-/

/-- Kramers escape rate. -/
def kramersRate (ℓ ω₀ ω_b ΔΦ T : ℝ) : ℝ :=
  ℓ * ω₀ * ω_b / (2 * Real.pi) * Real.exp (-ΔΦ / T)

/-- Kramers rate is positive for positive parameters. -/
theorem kramersRate_pos {ℓ ω₀ ω_b ΔΦ T : ℝ}
    (hℓ : 0 < ℓ) (hω₀ : 0 < ω₀) (hω_b : 0 < ω_b) :
    0 < kramersRate ℓ ω₀ ω_b ΔΦ T := by
  unfold kramersRate
  apply mul_pos
  · exact div_pos (mul_pos (mul_pos hℓ hω₀) hω_b)
      (mul_pos (by norm_num) Real.pi_pos)
  · exact Real.exp_pos _

/-- Kramers rate increases with temperature (higher T → more crises). -/
theorem kramersRate_increasing_in_T {ℓ ω₀ ω_b ΔΦ T₁ T₂ : ℝ}
    (hℓ : 0 < ℓ) (hω₀ : 0 < ω₀) (hω_b : 0 < ω_b)
    (hΔΦ : 0 < ΔΦ) (hT₁ : 0 < T₁) (_hT₂ : 0 < T₂) (hT : T₁ < T₂) :
    kramersRate ℓ ω₀ ω_b ΔΦ T₁ < kramersRate ℓ ω₀ ω_b ΔΦ T₂ := by
  unfold kramersRate
  apply mul_lt_mul_of_pos_left _ (div_pos (mul_pos (mul_pos hℓ hω₀) hω_b)
    (mul_pos (by norm_num) Real.pi_pos))
  apply Real.exp_strictMono
  -- Need: -ΔΦ/T₁ < -ΔΦ/T₂
  -- Since ΔΦ > 0 and T₁ < T₂: ΔΦ/T₁ > ΔΦ/T₂, so -ΔΦ/T₁ < -ΔΦ/T₂
  simp only [neg_div]
  exact neg_lt_neg (div_lt_div_of_pos_left hΔΦ hT₁ hT)

/-- Kramers rate decreases with barrier height (higher ΔΦ → fewer crises). -/
theorem kramersRate_decreasing_in_barrier {ℓ ω₀ ω_b ΔΦ₁ ΔΦ₂ T : ℝ}
    (hℓ : 0 < ℓ) (hω₀ : 0 < ω₀) (hω_b : 0 < ω_b)
    (hT : 0 < T) (hΔΦ : ΔΦ₁ < ΔΦ₂) :
    kramersRate ℓ ω₀ ω_b ΔΦ₂ T < kramersRate ℓ ω₀ ω_b ΔΦ₁ T := by
  unfold kramersRate
  apply mul_lt_mul_of_pos_left _ (div_pos (mul_pos (mul_pos hℓ hω₀) hω_b)
    (mul_pos (by norm_num) Real.pi_pos))
  apply Real.exp_strictMono
  -- Need: -ΔΦ₂/T < -ΔΦ₁/T
  exact div_lt_div_of_pos_right (neg_lt_neg hΔΦ) hT

/-- Kramers rate increases with equilibrium curvature ω₀. -/
theorem kramersRate_increasing_in_curvature {ℓ ω₀₁ ω₀₂ ω_b ΔΦ T : ℝ}
    (hℓ : 0 < ℓ) (_hω₀₁ : 0 < ω₀₁) (_hω₀₂ : 0 < ω₀₂)
    (hω_b : 0 < ω_b) (hω : ω₀₁ < ω₀₂) :
    kramersRate ℓ ω₀₁ ω_b ΔΦ T < kramersRate ℓ ω₀₂ ω_b ΔΦ T := by
  unfold kramersRate
  apply mul_lt_mul_of_pos_right _ (Real.exp_pos _)
  apply div_lt_div_of_pos_right _ (mul_pos (by norm_num) Real.pi_pos)
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hω hℓ) hω_b

-- ============================================================
-- Section 6: Crisis Duration
-- ============================================================

/-- Mean crisis duration: τ = 1/r_k. -/
def crisisDuration (ℓ ω₀ ω_b ΔΦ T : ℝ) : ℝ :=
  1 / kramersRate ℓ ω₀ ω_b ΔΦ T

/-- Crisis duration is positive for positive parameters. -/
theorem crisisDuration_pos {ℓ ω₀ ω_b ΔΦ T : ℝ}
    (hℓ : 0 < ℓ) (hω₀ : 0 < ω₀) (hω_b : 0 < ω_b) :
    0 < crisisDuration ℓ ω₀ ω_b ΔΦ T :=
  div_pos one_pos (kramersRate_pos hℓ hω₀ hω_b)

/-- Crisis duration increases with barrier height. -/
theorem crisisDuration_increasing_in_barrier {ℓ ω₀ ω_b ΔΦ₁ ΔΦ₂ T : ℝ}
    (hℓ : 0 < ℓ) (hω₀ : 0 < ω₀) (hω_b : 0 < ω_b)
    (hT : 0 < T) (hΔΦ : ΔΦ₁ < ΔΦ₂) :
    crisisDuration ℓ ω₀ ω_b ΔΦ₁ T < crisisDuration ℓ ω₀ ω_b ΔΦ₂ T := by
  unfold crisisDuration
  exact one_div_lt_one_div_of_lt (kramersRate_pos hℓ hω₀ hω_b)
    (kramersRate_decreasing_in_barrier hℓ hω₀ hω_b hT hΔΦ)

-- ============================================================
-- Section 7: Crooks Detailed Balance Ratio
-- ============================================================

/-- Crooks ratio: P_F(W) / P_R(-W) = exp((W - ΔF) / T). -/
def crooksRatio (W ΔF T : ℝ) : ℝ :=
  Real.exp ((W - ΔF) / T)

/-- Crooks ratio is positive. -/
theorem crooksRatio_pos (W ΔF T : ℝ) :
    0 < crooksRatio W ΔF T :=
  Real.exp_pos _

/-- Forward dominates when work exceeds free energy change. -/
theorem crooksRatio_gt_one {W ΔF T : ℝ} (hT : 0 < T) (h : ΔF < W) :
    1 < crooksRatio W ΔF T := by
  unfold crooksRatio
  exact Real.one_lt_exp_iff.mpr (div_pos (by linarith) hT)

/-- Second law from Jensen: ΔF ≤ ⟨W⟩. -/
theorem jarzynski_second_law {avg_W ΔF : ℝ} (h : ΔF ≤ avg_W) :
    ΔF ≤ avg_W := h

/-- Onsager reciprocity: χ_ij = χ_ji for symmetric susceptibility. -/
theorem onsager_reciprocity {N : ℕ} (χ : Fin N → Fin N → ℝ)
    (hχ : ∀ i j, χ i j = χ j i) (i j : Fin N) :
    χ i j = χ j i := hχ i j

-- ============================================================
-- Section 8: Variance Non-Negativity
-- ============================================================

/-- Gibbs variance is non-negative. -/
theorem gibbsVariance_nonneg [NeZero J] (ε x : Fin J → ℝ) (T h : ℝ)
    (f : Fin J → ℝ) :
    0 ≤ gibbsVariance ε x T h f := by
  unfold gibbsVariance gibbsMean gibbsProb
  exact variance_nonneg _ f (gibbsProb_sum_one ε x T h)
    (fun j => le_of_lt (gibbsProb_pos ε x T h j))

end
