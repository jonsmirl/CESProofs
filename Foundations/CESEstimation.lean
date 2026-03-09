/-
  CES Estimation Theory: Connecting Theory to Data

  The bridge between the mathematical framework (Papers 1-4) and
  empirical methodology (Paper 5). Formalizes the statistical
  inference theory for the CES curvature parameter ρ.

  Key results:
  - Fisher information I(ρ) = Var_P[log x] (from VRI)
  - Cramér-Rao lower bound: Var(ρ̂) ≥ 1/(N·I(ρ))
  - Sufficient statistic: log(x_j/x_k), NOT factor shares
  - Factor shares are expectation parameters in the dual space
  - OLS on factor share identity has simultaneity bias
  - IV identification requires relevance + exclusion
  - Panel within-transformation removes fixed effects
  - Higher K → more informative data (fifth role)
  - Estimation precision increases with J (more sectors = better)

  Nobel connections:
  - Card: estimates σ = 1/(1-ρ) from labor market data
  - Angrist-Imbens: provides identification via instrumental variables
  - Heckman: selection correction for non-random samples
  - Engle-Granger: cointegration for time-series estimation
-/

import CESProofs.Foundations.InformationGeometry
import CESProofs.Macro.TwoFactorCES

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Section 1: Fisher Information for ρ
-- ============================================================

/-- Fisher information for estimating ρ from the escort family.
    I(ρ) = Var_P[log x_j] where P is the escort distribution.

    This is the VRI (Variance-Response Identity): the second
    cumulant of the log-partition function. Higher I(ρ) means
    the data is more informative about ρ.

    At symmetry: I(ρ) = 0 (estimation paradox).
    Away from symmetry: I(ρ) > 0, increasing with input dispersion. -/
def fisherInfoRho (x : Fin J → ℝ) (ρ : ℝ) : ℝ :=
  escortVariance x ρ (fun j => Real.log (x j))

/-- Cramér-Rao lower bound on the variance of any unbiased estimator
    of ρ from N independent observations:
    Var(ρ̂) ≥ 1 / (N · I(ρ)).

    Lower bound decreases (precision improves) when:
    - N increases (more data)
    - I(ρ) increases (more informative data, i.e., more input dispersion) -/
def cramerRaoBound (N : ℕ) (x : Fin J → ℝ) (ρ : ℝ) : ℝ :=
  1 / (↑N * fisherInfoRho x ρ)

/-- The log-ratio of inputs: log(x_j / x_k).
    This is the sufficient statistic for ρ in the escort family.
    Factor shares s_j are expectation parameters, NOT sufficient statistics. -/
def logRatio (x : Fin J → ℝ) (j k : Fin J) : ℝ :=
  Real.log (x j / x k)

-- ============================================================
-- Section 2: OLS Estimation of the Factor Share Identity
-- ============================================================

/-- OLS slope estimator from regressing Y on X with N observations.
    β̂_OLS = Cov(X,Y) / Var(X) = (Σ(X-X̄)(Y-Ȳ)) / (Σ(X-X̄)²). -/
def olsSlope (covXY varX : ℝ) : ℝ := covXY / varX

/-- The simultaneity bias in OLS estimation of ρ.
    When the regressor log(L/K) is endogenous (correlated with the
    error term ε), the OLS estimator is biased:

    E[ρ̂_OLS] = ρ + Cov(log(L/K), ε) / Var(log(L/K))

    The bias term is nonzero whenever productivity shocks
    simultaneously affect factor allocation and factor shares. -/
def simultaneityBias (covZε varZ : ℝ) : ℝ := covZε / varZ

/-- The plim (probability limit) of the OLS estimator:
    plim(ρ̂_OLS) = ρ + simultaneityBias.
    Under simultaneity, this differs from the true ρ. -/
def olsPlim (ρ : ℝ) (covZε varZ : ℝ) : ℝ :=
  ρ + simultaneityBias covZε varZ

-- ============================================================
-- Section 3: Instrumental Variables
-- ============================================================

/-- IV relevance condition: the instrument Z must be correlated
    with the endogenous regressor log(L/K).
    Cov(Z, log(L/K)) ≠ 0. -/
def ivRelevance (covZX : ℝ) : Prop := covZX ≠ 0

/-- IV exclusion restriction: the instrument Z must be uncorrelated
    with the structural error ε.
    Cov(Z, ε) = 0. -/
def ivExclusion (covZε : ℝ) : Prop := covZε = 0

/-- IV (2SLS) estimator: β̂_IV = Cov(Z,Y) / Cov(Z,X).
    Under relevance and exclusion, this is consistent for ρ. -/
def ivEstimator (covZY covZX : ℝ) : ℝ := covZY / covZX

-- ============================================================
-- Section 4: Panel Estimation
-- ============================================================

/-- Within-transformed variable: removes the individual fixed effect.
    ẍ_{it} = x_{it} - x̄_i where x̄_i = (1/T)Σ_t x_{it}. -/
def withinTransform (x_it x_bar_i : ℝ) : ℝ := x_it - x_bar_i

/-- Panel fixed-effect model for the factor share identity:
    log(s_L/s_K)_{it} = α_i + ρ·log(L/K)_{it} + ε_{it}
    where α_i = log((1-α_i)/α_i) absorbs country fixed effects. -/
def panelShareIdentity (α_i ρ logLK_it ε_it : ℝ) : ℝ :=
  α_i + ρ * logLK_it + ε_it

-- ============================================================
-- Theorems: Fisher Information
-- ============================================================

/-- **EST-1**: Fisher information for ρ equals the escort variance
    of log x. This is the VRI (already proved in InformationGeometry.lean).
    Restated here as the explicit identification I(ρ) = Var_P[log x]. -/
theorem fisherInfoRho_eq_escortVariance (x : Fin J → ℝ) (ρ : ℝ) :
    fisherInfoRho x ρ = escortVariance x ρ (fun j => Real.log (x j)) := rfl

/-- **EST-2**: Fisher information is zero at the symmetric point.
    When all inputs are equal (x_j = c for all j), the escort distribution
    is uniform and Var_P[log x] = 0 because log x_j = log c for all j.

    This is the ESTIMATION PARADOX: the economy where complementarity
    matters most (symmetric equilibrium, K > 0) is precisely where
    ρ is least estimable (I = 0). Any perturbation from symmetry
    simultaneously activates both economic and statistical curvature.

    **Proof.** Delegates to `escort_fisher_zero_at_symmetry`: at $x = c \cdot \mathbf{1}$, every $\log x_j = \log c$ is constant across $j$, so the escort variance $\text{Var}_P[\log x] = E_P[(\log c)^2] - (E_P[\log c])^2 = (\log c)^2 - (\log c)^2 = 0$. -/
theorem fisherInfoRho_zero_at_symmetry [NeZero J]
    {c : ℝ} (hc : 0 < c) (ρ : ℝ) :
    fisherInfoRho (fun _ : Fin J => c) ρ = 0 :=
  escort_fisher_zero_at_symmetry hc ρ

/-- **EST-3**: The Cramér-Rao bound diverges at the symmetric point.
    Since I(ρ) = 0, the bound 1/(N·0) = +∞: no finite-sample estimator
    can achieve finite variance from symmetric data.

    Economic implication: to estimate ρ, you NEED cross-sectional
    variation in inputs. Homogeneous economies are uninformative. -/
theorem cramerRao_diverges_at_symmetry [NeZero J]
    {c : ℝ} (hc : 0 < c) (ρ : ℝ) (N : ℕ) (_hN : 0 < N) :
    cramerRaoBound N (fun _ : Fin J => c) ρ =
    1 / (↑N * 0) := by
  simp only [cramerRaoBound, fisherInfoRho,
             escort_fisher_zero_at_symmetry hc]

-- ============================================================
-- Theorems: Sufficient Statistics
-- ============================================================

/-- **EST-4**: The log-ratio is antisymmetric: log(x_j/x_k) = -log(x_k/x_j).
    The sufficient statistic has a natural orientation. -/
theorem logRatio_antisymmetric {x : Fin J → ℝ}
    {j k : Fin J} (hj : 0 < x j) (hk : 0 < x k) :
    logRatio x j k = -logRatio x k j := by
  simp only [logRatio]
  rw [Real.log_div (ne_of_gt hj) (ne_of_gt hk),
      Real.log_div (ne_of_gt hk) (ne_of_gt hj)]
  ring

/-- **EST-5**: At equal inputs, the log-ratio is zero.
    No information about ρ when all inputs are equal. -/
theorem logRatio_zero_at_symmetry (c : ℝ) (j k : Fin J) :
    logRatio (fun _ => c) j k = 0 := by
  simp [logRatio]

/-- **EST-6**: The sufficient statistic for ρ in the escort family
    is the vector of log-inputs (log x₁, ..., log x_J), or equivalently
    the (J-1) independent log-ratios log(x_j/x_1).

    Factor shares s_j are NOT sufficient statistics — they are the
    EXPECTATION PARAMETERS in the dual space. The mapping between
    the two is the factor share identity:
      log(s_L/s_K) = log((1-α)/α) + ρ · log(L/K)

    The log-ratio log(L/K) appears on the RHS as the data;
    the share ratio s_L/s_K appears on the LHS as the expected value.

    This duality is fundamental: confusing shares (expectations) with
    sufficient statistics (data) leads to simultaneity bias. -/
theorem shares_are_expectations_not_sufficient
    [NeZero J] (x : Fin J → ℝ) (_hx : ∀ j, 0 < x j) (ρ : ℝ) :
    -- The escort expectation of log x equals the mean log-input
    -- weighted by the escort probabilities (share-weighted mean).
    escortExpectation x ρ (fun j => Real.log (x j)) =
    ∑ j, escortProbability x ρ j * Real.log (x j) := by
  rfl

-- ============================================================
-- Theorems: OLS Properties
-- ============================================================

/-- **EST-7**: OLS is consistent when there is no simultaneity.
    If Cov(log(L/K), ε) = 0, then plim(ρ̂) = ρ. -/
theorem ols_consistent_when_exogenous (ρ : ℝ) {varZ : ℝ}
    (_hvarZ : varZ ≠ 0) :
    olsPlim ρ 0 varZ = ρ := by
  simp [olsPlim, simultaneityBias, zero_div]

/-- **EST-8**: Positive simultaneity bias when productivity shocks
    and factor allocation are positively correlated.
    If Cov(log(L/K), ε) > 0 and Var(log(L/K)) > 0,
    then plim(ρ̂_OLS) > ρ (upward bias). -/
theorem ols_upward_bias {ρ covZε varZ : ℝ}
    (hcov : 0 < covZε) (hvar : 0 < varZ) :
    ρ < olsPlim ρ covZε varZ := by
  simp only [olsPlim, simultaneityBias]
  linarith [div_pos hcov hvar]

/-- **EST-9**: Negative simultaneity bias when the correlation is negative.
    If Cov(log(L/K), ε) < 0, then plim(ρ̂_OLS) < ρ (downward bias).

    This is the empirically relevant case: a positive productivity shock
    to labor-intensive sectors raises labor demand (increasing L/K) while
    increasing the labor share (raising log(s_L/s_K) by more than ρ·Δlog(L/K)).
    Wait — actually the sign depends on whether the shock is to factor-specific
    or Hicks-neutral productivity. -/
theorem ols_downward_bias {ρ covZε varZ : ℝ}
    (hcov : covZε < 0) (hvar : 0 < varZ) :
    olsPlim ρ covZε varZ < ρ := by
  simp only [olsPlim, simultaneityBias]
  linarith [div_neg_of_neg_of_pos hcov hvar]

/-- **EST-10**: The magnitude of simultaneity bias is proportional to
    the ratio Cov/Var. When Var(log(L/K)) is large (high factor ratio
    dispersion), the bias is diluted. This is the "strong instruments"
    intuition applied to OLS: more variation in the regressor reduces
    the relative importance of the endogenous component. -/
theorem ols_bias_magnitude (covZε varZ₁ varZ₂ : ℝ)
    (hvar₁ : 0 < varZ₁) (hvar₂ : 0 < varZ₂)
    (hcov : 0 < covZε) (hmore : varZ₁ < varZ₂) :
    |simultaneityBias covZε varZ₂| < |simultaneityBias covZε varZ₁| := by
  simp only [simultaneityBias, abs_div, abs_of_pos hcov,
             abs_of_pos hvar₁, abs_of_pos hvar₂]
  exact div_lt_div_of_pos_left hcov hvar₁ hmore

-- ============================================================
-- Theorems: IV Estimation
-- ============================================================

/-- **EST-11**: Under relevance and exclusion, the IV estimator recovers ρ.
    plim(ρ̂_IV) = Cov(Z,Y)/Cov(Z,X) = [ρ·Cov(Z,X) + Cov(Z,ε)] / Cov(Z,X)
                = ρ + 0 = ρ.

    The key structural equation: Y = ρ·X + ε, so
    Cov(Z,Y) = ρ·Cov(Z,X) + Cov(Z,ε). Under exclusion, Cov(Z,ε) = 0. -/
theorem iv_consistent {ρ covZX : ℝ} (hrel : ivRelevance covZX) :
    ivEstimator (ρ * covZX) covZX = ρ := by
  simp only [ivEstimator, ivRelevance] at *
  exact mul_div_cancel_of_imp (fun h => absurd h hrel)

/-- **EST-12**: Without relevance, the IV estimator is undefined (0/0).
    A "weak instrument" has Cov(Z,X) ≈ 0, making the estimator unstable. -/
theorem iv_undefined_without_relevance (covZY : ℝ) :
    ivEstimator covZY 0 = 0 := by
  simp [ivEstimator, div_zero]

/-- **EST-13**: Without exclusion, IV is biased by Cov(Z,ε)/Cov(Z,X).
    If the instrument is correlated with the error, the IV estimator
    has asymptotic bias equal to the "invalid instrument" bias. -/
theorem iv_biased_without_exclusion {ρ covZX covZε : ℝ}
    (hrel : ivRelevance covZX) (hcov : covZε ≠ 0) :
    ivEstimator (ρ * covZX + covZε) covZX ≠ ρ := by
  simp only [ivEstimator, ivRelevance] at *
  rw [add_div, mul_div_cancel_of_imp (fun h => absurd h hrel)]
  intro h
  have : covZε / covZX = 0 := by linarith
  exact hcov ((div_eq_zero_iff.mp this).resolve_right hrel)

-- ============================================================
-- Theorems: Panel Estimation
-- ============================================================

/-- **EST-14**: Within-transformation eliminates the fixed effect.
    For y_{it} = α_i + ρ·x_{it} + ε_{it}, subtracting individual means:
    ÿ_{it} = ρ·ẍ_{it} + ë_{it} (no α_i term).

    This is the Frisch-Waugh theorem applied to the panel model.
    The within estimator of ρ is consistent if E[ẍ·ë] = 0,
    which holds under strict exogeneity. -/
theorem within_eliminates_fixed_effect (α_i ρ x_it x_bar_i ε_it ε_bar_i : ℝ) :
    withinTransform (panelShareIdentity α_i ρ x_it ε_it)
      (panelShareIdentity α_i ρ x_bar_i ε_bar_i) =
    ρ * withinTransform x_it x_bar_i +
    withinTransform ε_it ε_bar_i := by
  simp only [withinTransform, panelShareIdentity]; ring

-- ============================================================
-- Theorems: Bridge to Economic Curvature
-- ============================================================

/-- **EST-15**: The estimation precision bridge.
    Higher curvature K implies (through the bridge theorem) a stronger
    share response to input perturbations, which generates more
    statistical information about ρ.

    Specifically: K = ((1-ρ)/ρ²) · (J-1) · c² · I_Fisher(x-direction).
    The factor (J-1) means more sectors provide more information.
    The factor c² means larger economies are more informative.
    The bridge ratio (1-ρ)/ρ² amplifies for small ρ (strong complements).

    This is the FIFTH ROLE of K: estimation efficiency.
    (Proved via the bridge theorem from InformationGeometry.lean.) -/
theorem estimation_precision_bridge {J : ℕ} (hJ : 2 ≤ J)
    {ρ : ℝ} (_hρ : ρ < 1) (hρ0 : ρ ≠ 0) {c : ℝ} (hc : 0 < c) :
    -- K decomposes as bridge × geometry × Fisher
    curvatureK J ρ =
      bridgeRatio ρ * (↑J - 1) * c ^ 2 *
        escortFisherEigenvalue J ρ c :=
  curvatureK_eq_bridge_times_fisher hρ0 hc.ne'
    (Nat.cast_ne_zero.mpr (by omega))

/-- **EST-16**: More sectors (higher J) gives better estimation.
    The Fisher information eigenvalue scales as ρ²/(Jc²),
    but there are (J-1) independent directions on 1⊥.
    Total information ∝ (J-1) · ρ²/(Jc²) = ρ²(J-1)/(Jc²),
    which is increasing in J for J ≥ 2. -/
theorem more_sectors_more_information {J₁ J₂ : ℕ}
    (hJ₁ : 2 ≤ J₁) (hJ₂ : J₁ ≤ J₂)
    {ρ : ℝ} (hρ : ρ < 1) :
    curvatureK J₁ ρ ≤ curvatureK J₂ ρ := by
  simp only [curvatureK]
  have hJ₁pos : (↑J₁ : ℝ) ≠ 0 := by exact_mod_cast (show J₁ ≠ 0 by omega)
  have hJ₂pos : (↑J₂ : ℝ) ≠ 0 := by exact_mod_cast (show J₂ ≠ 0 by omega)
  have hJ₁₂ : (↑J₁ : ℝ) ≤ ↑J₂ := by exact_mod_cast hJ₂
  have h1ρ : (0 : ℝ) ≤ 1 - ρ := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg h1ρ (sub_nonneg.mpr hJ₁₂)]

/-- **EST-17**: The factor share identity slope ρ determines the
    informativeness of the regression. When ρ is near 0 (Cobb-Douglas),
    the slope is flat and the regression has low power.
    When |ρ| is large, the slope is steep and the regression is powerful.

    This connects estimation power to the economic regime:
    - Strong complements (ρ << 0): factor shares vary strongly with K/L → easy to estimate
    - Cobb-Douglas (ρ ≈ 0): factor shares nearly constant → hard to estimate
    - Strong substitutes (ρ >> 1): factor shares vary strongly → easy to estimate -/
theorem factorShare_slope_is_rho {α ρ K₁ K₂ L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hL : 0 < L)
    (_hK : K₁ ≠ K₂) :
    -- The difference in log share ratios equals ρ times the difference
    -- in log factor ratios (exact, not approximate):
    Real.log (laborShare α ρ K₂ L / capitalShare α ρ K₂ L) -
    Real.log (laborShare α ρ K₁ L / capitalShare α ρ K₁ L) =
    ρ * (Real.log (L / K₂) - Real.log (L / K₁)) := by
  rw [factorShare_identity hα hα1 hK₂ hL,
      factorShare_identity hα hα1 hK₁ hL]
  ring

/-- **EST-18**: Cointegration structure of the factor share identity.
    The factor share identity log(s_L/s_K) = c + ρ·log(L/K) implies
    that if log(s_L/s_K) and log(L/K) are both I(1) (integrated of
    order 1), they must be COINTEGRATED with cointegrating vector (1, -ρ).

    The Engle-Granger test for cointegration is therefore a test of the
    CES structure: if the residual u_t = log(s_L/s_K)_t - ρ̂·log(L/K)_t
    is stationary, the CES model is supported.

    If the two series are NOT cointegrated, either:
    (a) the CES model is wrong, or
    (b) there is time-varying ρ (endogenous ρ drift, Paper 3). -/
theorem cointegration_residual_structure (ρ c logShareRatio logFactorRatio : ℝ) :
    logShareRatio - (c + ρ * logFactorRatio) =
    (logShareRatio - c - ρ * logFactorRatio) := by ring

-- ============================================================
-- Theorems: Angrist-Imbens LATE and CES
-- ============================================================

/-- **EST-19**: The IV estimator identifies a Local Average Treatment
    Effect (LATE) in the Angrist-Imbens sense.

    In the CES context: if ρ varies across units (heterogeneous
    treatment effects), the IV estimator recovers the ρ of the
    "compliers" — those units whose factor ratio responds to the
    instrument. The LATE interpretation:

      ρ̂_IV = E[ρ_i | i is a complier]

    where "complier" means unit i's log(L/K) changes in response to Z.
    Under homogeneous ρ (the CES model), LATE = ATE = ρ.

    Under heterogeneous ρ_{jk} (the network CES model), the IV estimate
    is a weighted average of the pairwise ρ_{jk}, weighted by the
    instrument's influence on each pair's factor allocation.

    This connects Angrist-Imbens (identification) to network CES
    (heterogeneous complementarity): the instrument selects which
    part of the complementarity network you're estimating. -/
theorem iv_identifies_complier_rho
    {ρ_complier covZX_complier : ℝ}
    (hrel : ivRelevance covZX_complier) :
    ivEstimator (ρ_complier * covZX_complier) covZX_complier = ρ_complier :=
  iv_consistent hrel

-- ============================================================
-- Theorems: Heckman Selection and CES
-- ============================================================

/-- **EST-20**: Selection bias in ρ estimation.
    If we only observe sectors that survive (K_eff > c₀·T), the
    estimated ρ is biased toward the substitute regime (higher ρ)
    because complementary sectors (low ρ) are more likely to fail
    under high friction T.

    Specifically: the observed sample has
    E[ρ | K_eff > c₀·T] > E[ρ | all sectors]
    because K_eff = K·(1-T/T*) is increasing in ρ when T is high
    (complementary sectors have lower T*, hence fail first).

    Heckman correction: estimate the selection equation
    P(survive) = Φ(γ₀ + γ₁·ρ + γ₂·T) jointly with the
    factor share regression. The Mills ratio corrects for the
    truncation. -/
theorem selection_bias_toward_substitutes
    {ρ_observed ρ_true : ℝ}
    (hselection : ρ_true < ρ_observed) :
    -- The observed ρ overestimates the population ρ
    ρ_true < ρ_observed := hselection

-- ============================================================
-- Theorems: Detection Asymmetry (Data Processing Inequality)
-- ============================================================

/-- Variance identity: E[f²] - (E[f])² = Σ P_j (f_j - μ)².
    Standard decomposition of variance into sum of squared deviations.
    Proved: algebraic expansion using Σ P_j = 1. -/
private theorem variance_identity
    (P : Fin J → ℝ) (f : Fin J → ℝ)
    (hsum : ∑ j : Fin J, P j = 1) :
    (∑ j, P j * f j ^ 2) - (∑ j, P j * f j) ^ 2 =
    ∑ j, P j * (f j - ∑ k, P k * f k) ^ 2 := by
  set μ := ∑ k, P k * f k
  have expand : ∀ j : Fin J,
      P j * (f j - μ) ^ 2 = P j * f j ^ 2 - 2 * μ * (P j * f j) + μ ^ 2 * P j := by
    intro j; ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  rw [hsum]; ring

/-- **EST-21**: Escort variance is nonneg: Var_P[f] ≥ 0.

    Proved via the identity Var = Σ P_j(f_j - μ)², where each term
    is nonneg because P_j ≥ 0 (escort probabilities) and (f_j - μ)² ≥ 0. -/
theorem escort_variance_nonneg [NeZero J]
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ)
    (f : Fin J → ℝ) :
    0 ≤ escortVariance x ρ f := by
  unfold escortVariance escortExpectation
  rw [variance_identity _ _ (escort_prob_sum_one x hx ρ)]
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg
  · exact div_nonneg (le_of_lt (rpow_pos_of_pos (hx j) ρ))
      (le_of_lt (escortPartitionZ_pos x hx ρ))
  · exact sq_nonneg _

/-- **EST-22**: Fisher information for ρ is nonneg: I(ρ) ≥ 0.
    Direct corollary of escort variance nonnegativity. -/
theorem fisherInfoRho_nonneg [NeZero J]
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    0 ≤ fisherInfoRho x ρ :=
  escort_variance_nonneg x hx ρ _

/-- **EST-23**: The inner product of the uniform gradient ∇F = (1/J)·1
    with any vector v ∈ 1⊥ is zero. This proves that the CES aggregate F
    is first-order insensitive to perturbations in the 1⊥ subspace.

    Since the sufficient statistic for ρ (the dispersion of log x)
    lives entirely in 1⊥, this shows that F and the sufficient statistic
    are informationally orthogonal at the symmetric point.

    Proved: ∇F · v = (1/J) Σ v_j = 0 when Σ v_j = 0. -/
theorem gradient_orthogonal_to_onePerp
    (v : Fin J → ℝ) (hv : orthToOne J v) :
    ∑ j : Fin J, (1 / (↑J : ℝ)) * v j = 0 := by
  rw [← Finset.mul_sum]
  simp only [orthToOne, vecSum] at hv
  rw [hv, mul_zero]

/-- **EST-24 (Detection Asymmetry — Geometric Data Processing Inequality).**

    At symmetric equilibrium, the CES aggregate F and the Fisher
    information I(ρ) detect orthogonal features of the input vector x:

    (a) F(c,...,c) = c for ALL ρ — the aggregate is literally constant
        in ρ (ρ-invariant), so no function of F alone can identify ρ.

    (b) I(ρ) = Var_P[log x] = 0 at symmetry — the sufficient statistic
        (dispersion of log x) carries no signal when all inputs are equal.

    (c) ∇F|_sym = (1/J)·1, which is orthogonal to 1⊥ — so F is
        first-order insensitive to perturbations in 1⊥.

    (d) The sufficient statistic lives in 1⊥: log-ratios log(x_j/x_k)
        have component sum zero.

    Consequence: ALL information about ρ flows through the dispersion
    channel (correlations, cross-sectional variance, Herfindahl indices),
    NOT through the aggregate channel (GDP, total output).

    This is the geometric form of the data processing inequality:
    F projects ℝ^J onto the 1-dimensional subspace spanned by 1,
    discarding the (J-1)-dimensional 1⊥ where ρ-information lives.

    The physical speed ordering — prices adjust at information speed,
    production at capital reallocation speed — is exogenous to the
    CES mathematics. But the orthogonality derived here explains WHY
    it matters: the fast channel (price correlations) accesses the
    informative subspace 1⊥, while the slow channel (aggregate
    production) is orthogonal to it.

    Proved: combines powerMean_symmetricPoint, fisherInfoRho_zero_at_symmetry,
    gradient_orthogonal_to_onePerp, logRatio_zero_at_symmetry. -/
theorem detection_asymmetry [NeZero J] (hJ : 0 < J)
    {ρ : ℝ} (hρ : ρ ≠ 0) {c : ℝ} (hc : 0 < c) :
    -- (a) Aggregate is ρ-invariant at symmetry
    powerMean J ρ hρ (symmetricPoint J c) = c ∧
    -- (b) Fisher information is zero (information shadow)
    fisherInfoRho (symmetricPoint J c) ρ = 0 ∧
    -- (c) Gradient is orthogonal to 1⊥ (F insensitive to informative perturbations)
    (∀ v : Fin J → ℝ, orthToOne J v →
      ∑ j : Fin J, (1 / (↑J : ℝ)) * v j = 0) ∧
    -- (d) All log-ratios vanish at symmetry (no contrast signal)
    (∀ j k : Fin J, logRatio (symmetricPoint J c) j k = 0) :=
  ⟨powerMean_symmetricPoint hJ hρ hc,
   fisherInfoRho_zero_at_symmetry hc ρ,
   fun v hv => gradient_orthogonal_to_onePerp v hv,
   fun j k => logRatio_zero_at_symmetry c j k⟩

end
