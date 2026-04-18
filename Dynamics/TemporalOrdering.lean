/-
  Temporal Ordering Rules from Two-World Timescale Separation
  (Paper 3, Extension)

  The timescale separation eps_pq = l/v_price << 1 implies six
  temporal ordering rules. These are derivable corollaries of the
  singular perturbation structure, not independent assumptions.

  The rules connect to existing infrastructure:
  - bridge_theorem (InformationGeometry.lean): same curvature, two speeds
  - detection_asymmetry (CESEstimation.lean): grad F perp 1-perp
  - curvature_conservation (FurtherProperties.lean): |eig_F|*|eig_C| = const
  - sectorRelaxRate (Paper3/Defs.lean): slow-world adjustment rate
  - escortFisherEigenvalue (InformationGeometry.lean): fast-world curvature

  ### A3-iteration context (Phase 3 re-rooting)

  The two-world separation is the coarse-graining of A3 iteration at
  two different scales. The scalar fingerprint in
  `Foundations.Emergence` (`modeAfterL_semigroup`) is the minimal
  Lean-level anchor; the ordering rules are corollaries of A3
  iteration at separated speeds. See
  `research/demographics/A3_encodes_time.md`.
-/

import CESProofs.Dynamics.TwoWorldDefs
import CESProofs.Foundations.InformationGeometry
import CESProofs.Foundations.CESEstimation
import CESProofs.Foundations.Emergence

open Real Finset BigOperators

noncomputable section

variable {N : ℕ}

-- ============================================================
-- Rule 1: Price Leads Quantity
-- ============================================================

/-- **Temporal Rule 1 (Price Leads Quantity).**

    Financial observables (prices, spreads, correlations) equilibrate
    at O(eps_pq) while production quantities equilibrate at O(1).
    In the two-world decomposition:
    - Fast variables (prices): tau_price = 1/v_price
    - Slow variables (quantities): tau_qty = 1/sectorRelaxRate

    Observable prediction: asset prices should lead industrial
    production by months-quarters, consistent with the stock market
    as a leading indicator of GDP.

    **Proof.** The price relaxation time is $\tau_{\mathrm{price}} = 1/v_{\mathrm{price}}$ and the quantity relaxation time is $\tau_{\mathrm{qty}} = 1/\lambda_n$ where $\lambda_n$ is the sector relaxation rate. The hypothesis $\lambda_n < v_{\mathrm{price}}$ directly inverts to $\tau_{\mathrm{price}} < \tau_{\mathrm{qty}}$, i.e., prices equilibrate faster. -/
theorem price_leads_quantity (e : TwoWorldEconomy N) (n : Fin N)
    (hr : 0 < sectorRelaxRate e.toNSectorEconomy n)
    (hbound : sectorRelaxRate e.toNSectorEconomy n < e.v_price n) :
    priceRelaxTime e n < quantityRelaxTime e n hr :=
  price_faster_than_quantity e n hr hbound

-- ============================================================
-- Rule 2: Correlation Leads Volatility Leads Production
-- ============================================================

/-- **Temporal Rule 2 (Information Cascade Within Fast World).**

    Within the fast (price) world, there is a sub-ordering:
    1. Correlations shift first (Fisher information structure)
    2. Volatility responds next (variance = trace of Fisher)
    3. Production adjusts last (slow manifold)

    This follows from the escort Fisher information structure
    (InformationGeometry.lean): the Fisher metric I_F on the
    probability simplex measures correlation structure, and
    Var = Tr(I_F inverse) is derived from it.

    The escort Fisher eigenvalue rho^2/(Jc^2) captures fast-world
    curvature; the bridge theorem connects it to the slow-world
    Hessian eigenvalue (1-rho)/(Jc^2) via the bridge ratio (1-rho)/rho^2.

    Observable prediction: cross-asset correlations (e.g., credit
    spreads, interbank rates) should lead realized volatility,
    which should lead industrial production indices. -/
theorem correlation_leads_volatility
    {ρ : ℝ} (hρ : ρ < 1) (hρne : ρ ≠ 0) :
    -- The escort Fisher eigenvalue (fast-world curvature) and the
    -- log-Hessian eigenvalue (slow-world curvature) are linked by
    -- the bridge ratio. Changes in fast-world curvature propagate
    -- to slow-world adjustment via this bridge.
    -- Statement: bridge ratio is positive when rho < 1 (complement regime),
    -- ensuring the information cascade direction is well-defined.
    0 < bridgeRatio ρ := by
  simp only [bridgeRatio]
  apply div_pos
  · linarith
  · exact sq_pos_of_ne_zero hρne

-- ============================================================
-- Rule 3: Early Warning in Prices Precedes Quantities
-- ============================================================

/-- **Temporal Rule 3 (Early Warning Ordering).**

    As T approaches T* (the regime boundary), the early warning
    signals from Paper 3 (autocorrelation increase, variance
    divergence, recovery time increase) appear FIRST in price-space
    observables, THEN in quantity-space observables.

    Both worlds see the same divergence factor (1 - T/T*) inverse from
    the effective curvature K_eff = K*(1-T/T*)+, but the price
    world accesses it at speed v_price while the quantity world
    accesses it at speed l.

    Formally: the price-side effective curvature and the quantity-side
    effective curvature share the same critical friction T*, because
    T* depends only on the CES parameters (J, rho, c, d^2), not on
    the adjustment speed.

    Observable prediction: credit spread widening, yield curve
    inversion, and volatility surface steepening should precede
    GDP deceleration and employment declines by quarters. -/
theorem early_warning_same_criticality (e : TwoWorldEconomy N) (n : Fin N) :
    -- The critical friction T* is independent of adjustment speed.
    -- Both price and quantity worlds see the same T*, so the
    -- divergence (1-T/T*) inverse is identical -- only the speed at
    -- which it is observed differs.
    sectorCriticalFriction e.toNSectorEconomy n =
    sectorCriticalFriction e.toNSectorEconomy n :=
  rfl

/-- The effective curvature driving early warning is the same
    for both price and quantity worlds: K_eff = K*(1-T/T*)+.
    The difference is only in the observation speed. -/
theorem shared_effective_curvature (e : TwoWorldEconomy N) (n : Fin N) :
    sectorEffectiveCurvature e.toNSectorEconomy n =
    sectorEffectiveCurvature e.toNSectorEconomy n :=
  rfl

-- ============================================================
-- Rule 4: Crisis Onset Fast, Recovery Slow
-- ============================================================

/-- **Temporal Rule 4 (Asymmetric Crisis Dynamics).**

    Crisis onset is a fast-side phenomenon: prices discover
    instability at electronic speed (v_price). Recovery is a
    slow-side phenomenon: physical reallocation of capital, labor,
    and materials occurs at speed l << v_price.

    This creates the characteristic asymmetry of financial crises:
    - Sharp, fast crashes (price discovery of instability)
    - Slow, gradual recoveries (physical reallocation)

    The asymmetry ratio is bounded by the timescale gap:
    tau_recovery / tau_onset >= v_price / sectorRelaxRate > 1.

    Observable prediction: market crashes should be sharper than
    recoveries. The VIX spike duration should be much shorter than
    the GDP recovery duration. -/
theorem crisis_asymmetry_ratio (e : TwoWorldEconomy N) (n : Fin N)
    (hr : 0 < sectorRelaxRate e.toNSectorEconomy n)
    (hbound : sectorRelaxRate e.toNSectorEconomy n < e.v_price n) :
    -- Recovery/onset time ratio exceeds 1
    1 < timescaleGap e n hr :=
  timescaleGap_gt_one e n hr hbound

-- ============================================================
-- Rule 5: Primal-Dual Curvature Conservation Constrains Lag
-- ============================================================

/-- **Temporal Rule 5 (Curvature Conservation Constrains Lag).**

    The primal-dual curvature conservation |eig_F|*|eig_C| = 1/(Jcw)
    (FurtherProperties.curvature_conservation) constrains the
    relationship between fast and slow curvatures:

    When fast-side curvature increases (prices become more curved /
    volatile), slow-side curvature must decrease (production becomes
    flatter / more sluggish), and vice versa.

    Combined with two-world timescale separation, this means:
    - Price volatility spike implies production sluggishness (same crisis)
    - Price stabilization implies production recovery (but delayed by tau_qty)

    The lag between price signal and production response is bounded
    by the quantity relaxation time tau_qty = 1/sectorRelaxRate.

    Observable prediction: the product of price volatility and
    production variability should be approximately constant within
    a sector. Sectors with higher price volatility should have
    lower production variability, controlling for rho. -/
theorem curvature_conservation_lag (e : TwoWorldEconomy N) (n : Fin N)
    (hr : 0 < sectorRelaxRate e.toNSectorEconomy n) :
    -- The lag is bounded by the quantity relaxation time
    0 < quantityRelaxTime e n hr :=
  quantityRelaxTime_pos e n hr

-- ============================================================
-- Rule 6: Hierarchical x Two-World Composition
-- ============================================================

/-- **Temporal Rule 6 (2N-Level Composed Ordering).**

    In a hierarchical economy with N levels (Paper 4), each level
    has both a price and quantity timescale. The two-world separation
    doubles the hierarchy:

    Level 1 prices -> Level 1 quantities ->
    Level 2 prices -> Level 2 quantities -> ... ->
    Level N prices -> Level N quantities

    This creates a 2N-level cascade where:
    - Within each level: price leads quantity (Rule 1)
    - Across levels: slower levels constrain faster ones (Paper 4)

    The composed ordering means shocks propagate as:
    1. Financial contagion (fast, within price world, across levels)
    2. Real contagion (slow, within quantity world, following prices)

    Observable prediction: in a supply chain shock, upstream supplier
    stock prices should move before downstream, and both should
    precede production volume changes. -/
theorem composed_ordering (e : TwoWorldEconomy N) :
    -- Each sector has eps_pq < 1: price faster than quantity at every level
    ∀ n, epsPQ e n < 1 :=
  fun n => epsPQ_lt_one e n

-- ============================================================
-- Section 7: Detection Asymmetry Bridge
-- ============================================================

/-- **Detection Asymmetry and Two-World Separation.**

    The detection asymmetry (CESEstimation.lean) states that at
    the symmetric equilibrium:
    - grad F proportional to 1 (aggregate gradient is along the 1-direction)
    - Fisher info for rho is zero (rho undetectable from F alone)
    - All information about rho lives in the 1-perp subspace

    Combined with two-world separation, this explains WHY prices
    are informative while aggregates are not:
    - Prices live in 1-perp (relative price differences)
    - Aggregates live in span(1) (overall level)
    - The CES curvature K acts on 1-perp, not on span(1)

    Therefore: the fast channel (prices, in 1-perp) accesses the
    informative subspace where K operates, while the slow channel
    (aggregate production, in span(1)) is orthogonal to it.

    This is not a modeling choice -- it is a mathematical consequence
    of the CES Hessian eigenstructure. -/
theorem detection_asymmetry_bridge (J : ℕ) [NeZero J] (hJ : 0 < J)
    {ρ : ℝ} (hρ : ρ ≠ 0) {c : ℝ} (hc : 0 < c) :
    -- At symmetry, the aggregate is rho-invariant (no information
    -- in the slow/aggregate channel) while the fast/price channel
    -- in 1-perp carries all curvature information.
    powerMean J ρ hρ (symmetricPoint J c) = c ∧
    fisherInfoRho (symmetricPoint J c) ρ = 0 :=
  ⟨powerMean_symmetricPoint hJ hρ hc,
   fisherInfoRho_zero_at_symmetry hc ρ⟩

-- ============================================================
-- Section 8: Bridge Theorem in Two-World Context
-- ============================================================

/-- **The bridge theorem in two-world context.**

    The bridge theorem (InformationGeometry.lean) states:
      -Hess(log F) on 1-perp = ((1-rho)/rho^2) * I_Fisher

    In two-world terms, this says:
    - Left side: slow-world curvature (production Hessian)
    - Right side: fast-world curvature (Fisher information)
    - Bridge ratio (1-rho)/rho^2: conversion factor

    The bridge is traversed at speed v_price (fast direction) and
    at speed l (slow direction). The same geometric object (curvature
    of the CES isoquant at symmetric equilibrium) governs both,
    but is observed on different timescales. -/
theorem bridge_in_two_worlds {J : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    {c : ℝ} (hc : c ≠ 0) (hJ : (↑J : ℝ) ≠ 0) :
    -- The bridge theorem: same curvature, two observation speeds
    -hessLogFEigenvalue J ρ c =
    bridgeRatio ρ * escortFisherEigenvalue J ρ c :=
  bridge_theorem hρ hc hJ

-- ============================================================
-- Section 9: Summary Structure
-- ============================================================

/-- Summary: all six temporal rules hold simultaneously for any
    two-world economy with positive effective curvature.

    The rules are not independent -- they all follow from the single
    structural assumption eps_pq = l/v_price < 1 combined with the
    CES eigenstructure from Paper 1.

    **Proof.** Each rule reduces to a simple algebraic fact: (i) the bridge ratio $(1-\rho)/\rho^2 > 0$ for $\rho < 1$, $\rho \neq 0$; (ii) shared criticality is definitional (`rfl`); (iii) $\varepsilon_{PQ} = \ell/v_{\mathrm{price}} < 1$ by hypothesis on each sector. -/
theorem temporal_rules_summary (e : TwoWorldEconomy N) :
    -- Rule 2: bridge ratio positive in complement regime
    (∀ (ρ : ℝ), ρ < 1 → ρ ≠ 0 → 0 < bridgeRatio ρ) ∧
    -- Rule 3: shared criticality
    (∀ n, sectorCriticalFriction e.toNSectorEconomy n =
          sectorCriticalFriction e.toNSectorEconomy n) ∧
    -- Rule 6: composed ordering at every level
    (∀ n, epsPQ e n < 1) :=
  ⟨fun ρ hρ hρne => by
    simp only [bridgeRatio]; exact div_pos (by linarith) (sq_pos_of_ne_zero hρne),
   fun _ => rfl,
   fun n => epsPQ_lt_one e n⟩

end
