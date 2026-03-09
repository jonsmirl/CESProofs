/-
  The Cumulant Tower: Higher-Order Bridges Between CES and Escort Statistics

  Extends the VRI (kappa_2 = Var_P[log x] = A''(rho)) to the full cumulant tower:

    kappa_1 = E_P[log x]              = A'(rho)    (mean)
    kappa_2 = Var_P[log x]            = A''(rho)   (variance = Fisher info)
    kappa_3 = E_P[(log x - mu)^3]     = A'''(rho)  (skewness = prudence)
    kappa_4 = E_P[(log x - mu)^4]-3k2^2 = A''''(rho) (excess kurtosis = temperance)

  where A(rho) = log Z(rho) is the log-partition function.

  Key results:
  1. General derivative: d^n/drho^n Z = Sum x_j^rho * (log x_j)^n
  2. Moment recursion: d/drho M_n = M_{n+1} - M_n * M_1
  3. Third cumulant: kappa_3 = d/drho kappa_2 = d^3/drho^3 log Z
  4. Generalized estimation paradox: all kappa_n = 0 at symmetry
  5. CES-partition transfer: rho * log F = log Z - log J

  Economic implications:
  - kappa_2 = Arrow-Pratt risk aversion (bridge theorem)
  - kappa_3 = Kimball prudence (precautionary saving motive)
  - kappa_4 = Kimball temperance (background risk response)
  - CES LOCKS all of these to rho: no independent parameters!

  In expected utility theory, u'', u''', u'''' are independent
  preference parameters. In CES production, the curvature parameter
  rho simultaneously determines risk aversion, prudence, AND
  temperance through the escort distribution. This is an extremely
  strong testable prediction: the ratio kappa_3/kappa_2^{3/2}
  (skewness) is fully determined by rho and the input vector x.
-/

import CESProofs.Foundations.InformationGeometry

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Part A: Higher Derivatives of x^rho and Z(rho)
-- ============================================================

/-- d/drho (x^rho) = x^rho * log x. -/
private lemma hasDerivAt_rpow {x : ℝ} (hx : 0 < x) (ρ : ℝ) :
    HasDerivAt (fun p => x ^ p) (x ^ ρ * Real.log x) ρ := by
  simp_rw [rpow_def_of_pos hx]
  exact ((hasDerivAt_id ρ).const_mul (Real.log x)
    |>.congr_deriv (by ring)).exp

/-- General derivative: d/drho [x^rho * (log x)^n] = x^rho * (log x)^(n+1).

    Each differentiation w.r.t. rho multiplies by another factor of log x,
    since (log x)^n is constant in rho. This is the engine that generates
    higher moments of the escort distribution. -/
private lemma hasDerivAt_rpow_logpow {x : ℝ} (hx : 0 < x) (ρ : ℝ) (n : ℕ) :
    HasDerivAt (fun p => x ^ p * (Real.log x) ^ n)
      (x ^ ρ * (Real.log x) ^ (n + 1)) ρ := by
  convert (hasDerivAt_rpow hx ρ).mul_const ((Real.log x) ^ n) using 1
  ring

/-- The n-th derivative coefficient of Z:
    Z^{(n)}(rho) = Sum_j x_j^rho * (log x_j)^n.

    Z^{(0)} = Z (partition function),
    Z^{(1)} = Z' (first derivative),
    Z^{(n)} = n-th derivative of Z w.r.t. rho. -/
def escortPartitionZn (x : Fin J → ℝ) (ρ : ℝ) (n : ℕ) : ℝ :=
  ∑ j : Fin J, x j ^ ρ * (Real.log (x j)) ^ n

/-- Z^{(0)} = Z: the zeroth derivative coefficient is the partition function. -/
theorem escortPartitionZn_zero (x : Fin J → ℝ) (ρ : ℝ) :
    escortPartitionZn x ρ 0 = escortPartitionZ x ρ := by
  simp [escortPartitionZn, escortPartitionZ]

/-- Z^{(1)} = Z': the first derivative coefficient matches Z'. -/
theorem escortPartitionZn_one (x : Fin J → ℝ) (ρ : ℝ) :
    escortPartitionZn x ρ 1 = escortPartitionZ' x ρ := by
  simp [escortPartitionZn, escortPartitionZ']

/-- **The derivative chain**: d/drho Z^{(n)} = Z^{(n+1)}.

    The (n+1)-th derivative coefficient is the rho-derivative of the n-th.
    This is the fundamental recurrence that builds the cumulant tower:
    each differentiation w.r.t. rho inserts another factor of log x_j
    into each term of the sum. -/
theorem escortPartitionZn_hasDerivAt
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) (n : ℕ) :
    HasDerivAt (fun p => escortPartitionZn x p n)
      (escortPartitionZn x ρ (n + 1)) ρ := by
  unfold escortPartitionZn
  convert HasDerivAt.sum (u := Finset.univ)
    (fun j _ => hasDerivAt_rpow_logpow (hx j) ρ n) using 1
  ext p; simp

-- ============================================================
-- Part B: Raw Escort Moments and the Moment Recursion
-- ============================================================

/-- The n-th raw escort moment: M_n(rho) = E_P[(log x)^n] = Z^{(n)}/Z.

    These are the moments of the sufficient statistic log x under the
    escort distribution P_j = x_j^rho / Z(rho).

    M_0 = 1 (normalization),
    M_1 = E_P[log x] (mean),
    M_2 = E_P[(log x)^2] (raw second moment). -/
def escortRawMoment (x : Fin J → ℝ) (ρ : ℝ) (n : ℕ) : ℝ :=
  escortPartitionZn x ρ n / escortPartitionZ x ρ

/-- M_0 = 1: the zeroth moment is normalization. -/
theorem escortRawMoment_zero [NeZero J]
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    escortRawMoment x ρ 0 = 1 := by
  simp only [escortRawMoment, escortPartitionZn_zero]
  exact div_self (ne_of_gt (escortPartitionZ_pos x hx ρ))

/-- M_1 equals the escort expectation of log x. -/
theorem escortRawMoment_one [NeZero J]
    (x : Fin J → ℝ) (_hx : ∀ j, 0 < x j) (ρ : ℝ) :
    escortRawMoment x ρ 1 =
    escortExpectation x ρ (fun j => Real.log (x j)) := by
  simp only [escortRawMoment, escortPartitionZn, escortExpectation,
    escortProbability, pow_one, div_mul_eq_mul_div, ← Finset.sum_div]

/-- **Moment Recursion (THE engine of the cumulant tower)**:

      d/drho M_n = M_{n+1} - M_n * M_1

    This single identity generates ALL cumulant relations.
    Applied repeatedly:
    - n=1: d/drho M_1 = M_2 - M_1^2 = kappa_2 (= VRI)
    - n=2: d/drho M_2 = M_3 - M_2*M_1 (raw moment evolution)
    - Combined: d/drho kappa_2 = kappa_3 (third cumulant)

    **Proof.** quotient rule on Z^{(n)}/Z, using the derivative chain. -/
theorem escortRawMoment_hasDerivAt [NeZero J]
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) (n : ℕ) :
    HasDerivAt (fun p => escortRawMoment x p n)
      (escortRawMoment x ρ (n + 1) -
       escortRawMoment x ρ n * escortRawMoment x ρ 1) ρ := by
  unfold escortRawMoment
  have hZ := ne_of_gt (escortPartitionZ_pos x hx ρ)
  have hquot := (escortPartitionZn_hasDerivAt x hx ρ n).div
    (escortPartitionZ_hasDerivAt x hx ρ) hZ
  refine hquot.congr_deriv ?_
  rw [← escortPartitionZn_one]
  field_simp

-- ============================================================
-- Part C: Cumulant Definitions
-- ============================================================

/-- The second cumulant kappa_2 = Var_P[log x] = M_2 - M_1^2.

    This is the VRI (Variance-Response Identity), which equals the
    Fisher information for rho. Equivalently, the second derivative
    of the log-partition function A''(rho). -/
def escortCumulant2 (x : Fin J → ℝ) (ρ : ℝ) : ℝ :=
  escortRawMoment x ρ 2 - escortRawMoment x ρ 1 ^ 2

/-- The third cumulant kappa_3 = M_3 - 3*M_2*M_1 + 2*M_1^3.

    For the escort distribution, this equals the third central moment
    E_P[(log x - mu)^3] where mu = E_P[log x].

    Economic interpretation: CES prudence. Controls precautionary
    behavior (Kimball 1990). Positive kappa_3 means the economy
    responds asymmetrically to positive vs negative shocks:
    concentration shocks (one sector dominates) have larger effects
    than diversification shocks (sectors equalize).

    In expected utility, prudence -u'''/u'' is a free parameter.
    In CES, it is LOCKED to rho through the escort distribution:
    kappa_3 is fully determined by rho and the input vector x. -/
def escortCumulant3 (x : Fin J → ℝ) (ρ : ℝ) : ℝ :=
  escortRawMoment x ρ 3 - 3 * escortRawMoment x ρ 2 * escortRawMoment x ρ 1
    + 2 * escortRawMoment x ρ 1 ^ 3

/-- The fourth cumulant kappa_4 = M_4 - 4*M_3*M_1 - 3*M_2^2 + 12*M_2*M_1^2 - 6*M_1^4.

    Economic interpretation: CES temperance. Controls response to
    background risk (Kimball 1992). Again fully LOCKED to rho.

    In expected utility, temperance u''''/u'' is independent of
    prudence u'''/u''. In CES, both are determined by rho. This
    is a falsifiable prediction: temperance and prudence should
    covary in a specific way across sectors with different rho. -/
def escortCumulant4 (x : Fin J → ℝ) (ρ : ℝ) : ℝ :=
  escortRawMoment x ρ 4 - 4 * escortRawMoment x ρ 3 * escortRawMoment x ρ 1
    - 3 * escortRawMoment x ρ 2 ^ 2
    + 12 * escortRawMoment x ρ 2 * escortRawMoment x ρ 1 ^ 2
    - 6 * escortRawMoment x ρ 1 ^ 4

-- ============================================================
-- Part D: kappa_2 Equals Escort Variance (VRI Connection)
-- ============================================================

/-- kappa_2 equals the escort variance of log x.
    This connects our cumulant definition to the existing VRI
    infrastructure in InformationGeometry.lean.

    **Proof.** Unfold $\kappa_2 = M_2 - M_1^2$ and expand each raw moment $M_n = Z^{(n)}/Z$ where $Z^{(n)} = \sum_j x_j^\rho (\log x_j)^n$. After unfolding the escort variance $\text{Var}_P[\log x] = E_P[(\log x)^2] - (E_P[\log x])^2$, both sides reduce to the same ratio of sums. -/
theorem escortCumulant2_eq_variance [NeZero J]
    (x : Fin J → ℝ) (_hx : ∀ j, 0 < x j) (ρ : ℝ) :
    escortCumulant2 x ρ =
    escortVariance x ρ (fun j => Real.log (x j)) := by
  unfold escortCumulant2 escortVariance escortRawMoment
    escortPartitionZn escortExpectation escortProbability
  simp only [pow_one]
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]

-- ============================================================
-- Part E: The Third Cumulant is the Derivative of Variance
-- ============================================================

/-- **Third Cumulant Identity**: kappa_3 = d/drho kappa_2.

    The third cumulant is the rho-derivative of the variance.
    Since kappa_2 = A''(rho) (VRI), this gives kappa_3 = A'''(rho):
    the third cumulant equals the third derivative of the
    log-partition function.

    **Proof.** uses the moment recursion twice:
    - d/drho M_2 = M_3 - M_2*M_1
    - d/drho M_1 = M_2 - M_1^2 = kappa_2
    Then d/drho kappa_2 = d/drho(M_2 - M_1^2)
    = (M_3 - M_2*M_1) - 2*M_1*(M_2 - M_1^2) = kappa_3. -/
theorem cumulant3_is_derivative_of_variance [NeZero J]
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    HasDerivAt (fun p => escortCumulant2 x p)
      (escortCumulant3 x ρ) ρ := by
  unfold escortCumulant2 escortCumulant3
  -- Get the moment recursion for M_2 and M_1
  have hM2 := escortRawMoment_hasDerivAt x hx ρ 2
  have hM1 := escortRawMoment_hasDerivAt x hx ρ 1
  -- Derivative of M_1^2 via chain rule
  have hM1sq := hM1.pow 2
  -- Combine: d/drho (M_2 - M_1^2) = dM_2 - d(M_1^2)
  have h := hM2.sub hM1sq
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

-- ============================================================
-- Part F: Fourth Cumulant as Second Derivative of Variance
-- ============================================================

/-- **Fourth Cumulant Identity**: kappa_4 = d/drho kappa_3 = d^2/drho^2 kappa_2.

    The fourth cumulant is the rho-derivative of the third cumulant,
    or equivalently the second derivative of the variance. Since
    kappa_2 = A''(rho), this gives kappa_4 = A''''(rho).

    This extends the tower: each new cumulant is the derivative
    of the previous one, because the log-partition function A(rho)
    is the cumulant generating function. -/
theorem cumulant4_is_derivative_of_cumulant3 [NeZero J]
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    HasDerivAt (fun p => escortCumulant3 x p)
      (escortCumulant4 x ρ) ρ := by
  unfold escortCumulant3 escortCumulant4
  have hM := fun n => escortRawMoment_hasDerivAt x hx ρ n
  -- kappa_3 = M_3 - 3*M_2*M_1 + 2*M_1^3
  -- Build HasDerivAt in left-associative order to match function syntax:
  -- Term 1: M_3
  -- Term 2: 3*M_2*M_1 (build as (const_mul 3 of M_2).mul M_1)
  -- Term 3: 2*M_1^3 (build as (pow 3 of M_1).const_mul 2)
  have h := (hM 3).sub (((hM 2).const_mul 3).mul (hM 1))
    |>.add (((hM 1).pow 3).const_mul 2)
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

-- ============================================================
-- Part G: Generalized Estimation Paradox
-- ============================================================

/-- At the symmetric equilibrium x = c*1, the n-th raw moment
    of log x under the escort distribution is simply (log c)^n.

    Since all inputs equal c, log x_j = log c for every j, and
    the escort distribution is uniform. So E_P[(log x)^n] = (log c)^n. -/
theorem escortRawMoment_at_symmetry [NeZero J]
    {c : ℝ} (hc : 0 < c) (ρ : ℝ) (n : ℕ) :
    escortRawMoment (fun _ : Fin J => c) ρ n = (Real.log c) ^ n := by
  simp only [escortRawMoment, escortPartitionZn, escortPartitionZ]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hcr : c ^ ρ ≠ 0 := ne_of_gt (rpow_pos_of_pos hc ρ)
  have hJ : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne J)
  field_simp

/-- **Generalized Estimation Paradox**: ALL cumulants vanish at the
    symmetric equilibrium for n >= 2.

    At x = c*1:
    - kappa_1 = log c (constant, trivially determined)
    - kappa_n = 0 for all n >= 2 (no information of ANY order)

    This goes far beyond the VRI result (kappa_2 = 0 at symmetry).
    Not only is the variance zero — the skewness, kurtosis, and ALL
    higher-order statistical features are zero. The escort distribution
    at symmetry is a point mass on log c, containing literally zero
    information about rho at every order.

    Economic implication: at the symmetric equilibrium, not only is rho
    unestimable (kappa_2 = 0), but there is no way to detect asymmetric
    shock sensitivity (kappa_3 = 0) or fat-tail behavior (kappa_4 = 0).
    ALL curvature information is hidden. Any departure from symmetry
    simultaneously activates curvature at EVERY order.

    **Proof.** At $x = c \cdot \mathbf{1}$, every raw moment is $M_n = (\log c)^n$ (since the escort distribution is uniform and $\log x_j = \log c$ for all $j$). Thus $\kappa_2 = (\log c)^2 - ((\log c)^1)^2 = 0$ by `ring`, and similarly for $\kappa_3, \kappa_4$. -/
theorem escortCumulant2_zero_at_symmetry [NeZero J]
    {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    escortCumulant2 (fun _ : Fin J => c) ρ = 0 := by
  simp only [escortCumulant2, escortRawMoment_at_symmetry hc]
  ring

theorem escortCumulant3_zero_at_symmetry [NeZero J]
    {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    escortCumulant3 (fun _ : Fin J => c) ρ = 0 := by
  simp only [escortCumulant3, escortRawMoment_at_symmetry hc]
  ring

theorem escortCumulant4_zero_at_symmetry [NeZero J]
    {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    escortCumulant4 (fun _ : Fin J => c) ρ = 0 := by
  simp only [escortCumulant4, escortRawMoment_at_symmetry hc]
  ring

-- ============================================================
-- Part H: Escort Central Moments
-- ============================================================

/-- The n-th central moment of log x under the escort distribution:
    mu_n = E_P[(log x - E_P[log x])^n].

    Central moments measure the shape of the escort distribution
    around its mean. For the CES escort family:
    - mu_2 = kappa_2 (variance = Fisher info)
    - mu_3 = kappa_3 (skewness = prudence)
    - mu_4 = kappa_4 + 3*kappa_2^2 (kurtosis, differs from cumulant at order 4) -/
def escortCentralMoment (x : Fin J → ℝ) (ρ : ℝ) (n : ℕ) : ℝ :=
  escortExpectation x ρ
    (fun j => (Real.log (x j) -
      escortExpectation x ρ (fun k => Real.log (x k))) ^ n)

/-- **All central moments vanish at symmetry** for n >= 1.

    At x = c*1, each log x_j = log c, the escort mean mu = log c,
    so (log x_j - mu)^n = 0 for n >= 1.

    This is the most general form of the estimation paradox:
    the escort distribution at symmetry carries zero information
    at every statistical order. -/
theorem escortCentralMoment_zero_at_symmetry [NeZero J]
    {c : ℝ} (hc : 0 < c) (ρ : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    escortCentralMoment (fun _ : Fin J => c) ρ n = 0 := by
  unfold escortCentralMoment
  -- The mean is log c
  have hmean : escortExpectation (fun _ : Fin J => c) ρ
      (fun _ => Real.log c) = Real.log c :=
    escort_expectation_const _ (fun _ => hc) ρ (Real.log c)
  -- Simplify: log(c) for constant input
  simp only [hmean, sub_self, zero_pow (by omega : n ≠ 0)]
  exact escort_expectation_const _ (fun _ => hc) ρ 0

-- ============================================================
-- Part I: The Moment Recursion Specializations
-- ============================================================

/-- **VRI from moment recursion (n=1)**: d/drho M_1 = M_2 - M_1^2 = kappa_2.

    The variance-response identity is the n=1 specialization of the
    moment recursion. This provides an alternative proof route to
    escort_vri in InformationGeometry.lean. -/
theorem vri_from_moment_recursion [NeZero J]
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    HasDerivAt (fun p => escortRawMoment x p 1)
      (escortCumulant2 x ρ) ρ := by
  unfold escortCumulant2
  have h := escortRawMoment_hasDerivAt x hx ρ 1
  refine h.congr_deriv ?_
  ring

-- ============================================================
-- Part J: The CES-Partition Transfer
-- ============================================================

/-- **CES-Partition Identity (restated for reference)**:
    rho * log F = log Z - log J.

    This identity transfers every cumulant to a statement about
    rho-derivatives of log F:

    d/drho (rho * log F) = log F + rho * d(log F)/drho = kappa_1
    d^2/drho^2 (rho * log F) = 2*d(log F)/drho + rho*d^2(log F)/drho^2 = kappa_2
    d^3/drho^3 (rho * log F) = 3*d^2(log F)/drho^2 + rho*d^3(log F)/drho^3 = kappa_3

    The n-th cumulant of the escort distribution equals the n-th
    rho-derivative of the log-partition function log Z, which by the
    CES-partition identity equals the n-th rho-derivative of
    (rho * log F + log J).

    Since log J is constant in rho, this reduces to: the cumulants
    of the escort distribution are fully determined by rho-derivatives
    of the CES aggregate F. -/
theorem ces_partition_identity_restated [NeZero J] {ρ : ℝ} (hρ : ρ ≠ 0)
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) :
    ρ * Real.log (powerMean J ρ hρ x) =
    Real.log (escortPartitionZ x ρ) - Real.log ↑J :=
  logCES_eq_logPartition hρ x hx

-- ============================================================
-- Part K: Prudence Locking
-- ============================================================

/-- **Prudence Locking Theorem**: In expected utility theory,
    the Arrow-Pratt risk aversion coefficient r(w) = -u''(w)/u'(w)
    and the Kimball prudence coefficient p(w) = -u'''(w)/u''(w) are
    independent parameters. Different utility functions can have the
    same risk aversion but different prudence.

    In CES production, both risk aversion (kappa_2) and prudence
    (kappa_3) are determined by a single parameter rho through the
    escort distribution. This means:

    1. kappa_3 = d/drho kappa_2: prudence is the sensitivity of
       risk aversion to the complementarity parameter.

    2. Both vanish simultaneously at symmetry and activate
       simultaneously away from symmetry.

    3. The ratio kappa_3/kappa_2 is fully determined by rho and x.

    This is a strong testable prediction: sectors with the same rho
    should exhibit the same prudence-to-variance ratio in their
    share distributions.

    **Proof.** Part (i) is `cumulant3_is_derivative_of_variance`, which differentiates $\kappa_2 = M_2 - M_1^2$ using the moment recursion $dM_n/d\rho = M_{n+1} - M_n M_1$ and the chain rule on $M_1^2$, yielding $d\kappa_2/d\rho = \kappa_3$. Part (ii) substitutes $x = c \cdot \mathbf{1}$ and applies `escortCumulant2_zero_at_symmetry` and `escortCumulant3_zero_at_symmetry`. -/
theorem prudence_locking [NeZero J]
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    -- (i) kappa_3 is the derivative of kappa_2
    HasDerivAt (fun p => escortCumulant2 x p) (escortCumulant3 x ρ) ρ ∧
    -- (ii) Both vanish at symmetry
    (∀ c : ℝ, 0 < c →
      escortCumulant2 (fun _ : Fin J => c) ρ = 0 ∧
      escortCumulant3 (fun _ : Fin J => c) ρ = 0) :=
  ⟨cumulant3_is_derivative_of_variance x hx ρ,
   fun _ hc => ⟨escortCumulant2_zero_at_symmetry hc ρ,
                 escortCumulant3_zero_at_symmetry hc ρ⟩⟩

-- ============================================================
-- Part L: The Full Tower Summary
-- ============================================================

/-- **Cumulant Tower Summary**: The full tower of results connecting
    CES curvature to escort statistics.

    The log-partition function A(rho) = log Z(rho) is the cumulant
    generating function of log x under the escort distribution.
    Its successive derivatives give:

    A'   = kappa_1 = E[log x]           (mean)
    A''  = kappa_2 = Var[log x]         (variance = Fisher info)
    A''' = kappa_3 = E[(log x - mu)^3]  (skewness = prudence)

    All three identities are proved as HasDerivAt theorems, chaining
    through the moment recursion d/drho M_n = M_{n+1} - M_n * M_1.

    All cumulants vanish simultaneously at the symmetric equilibrium
    x = c*1, and activate simultaneously with any perturbation.
    This is the generalized estimation paradox. -/
theorem cumulant_tower_summary [NeZero J]
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    -- (i) Moment recursion holds for all n
    (∀ n, HasDerivAt (fun p => escortRawMoment x p n)
      (escortRawMoment x ρ (n + 1) -
       escortRawMoment x ρ n * escortRawMoment x ρ 1) ρ) ∧
    -- (ii) kappa_2 = d/drho M_1 (VRI)
    HasDerivAt (fun p => escortRawMoment x p 1)
      (escortCumulant2 x ρ) ρ ∧
    -- (iii) kappa_3 = d/drho kappa_2
    HasDerivAt (fun p => escortCumulant2 x p)
      (escortCumulant3 x ρ) ρ ∧
    -- (iv) kappa_4 = d/drho kappa_3
    HasDerivAt (fun p => escortCumulant3 x p)
      (escortCumulant4 x ρ) ρ ∧
    -- (v) All cumulants vanish at symmetry
    (∀ c : ℝ, 0 < c →
      escortCumulant2 (fun _ : Fin J => c) ρ = 0 ∧
      escortCumulant3 (fun _ : Fin J => c) ρ = 0 ∧
      escortCumulant4 (fun _ : Fin J => c) ρ = 0) :=
  ⟨fun n => escortRawMoment_hasDerivAt x hx ρ n,
   vri_from_moment_recursion x hx ρ,
   cumulant3_is_derivative_of_variance x hx ρ,
   cumulant4_is_derivative_of_cumulant3 x hx ρ,
   fun _ hc => ⟨escortCumulant2_zero_at_symmetry hc ρ,
                 escortCumulant3_zero_at_symmetry hc ρ,
                 escortCumulant4_zero_at_symmetry hc ρ⟩⟩

end
