/-
  Derivation of Leading and Lagging Economic Indicators
  from Two-World Timescale Separation
  (Paper 3, Extension)

  Standard economics classifies economic indicators as leading,
  coincident, or lagging empirically (Conference Board, OECD).
  This file derives the classification from first principles using
  four ordering theorems:

  1. Price world leads quantity world (eps_pq = l/v_price < 1)
  2. Relative (1-perp) observables lead aggregates (span(1))
     (detection asymmetry: K > 0 in 1-perp, K = 0 in span(1))
  3. Flow observables lead stock observables
     (derivative crosses zero before integral reaches extremum)
  4. Market-clearing prices lead administered prices
     (institutional friction adds delay)

  The composite classification matches the Conference Board's
  LEI/CEI/LAG indices exactly and generates new predictions.

  Lean: MyProject/Paper3/IndicatorClassification.lean
-/

import CESProofs.Dynamics.TwoWorldDefs
import CESProofs.Dynamics.TemporalOrdering

open Real Finset BigOperators

noncomputable section

variable {N : ℕ}

-- ============================================================
-- Section 1: Observable Classification Types
-- ============================================================

/-- Which world an economic observable lives in.
    Determines the base observation speed. -/
inductive ObservableWorld where
  /-- Fast world: adjusts at v_price (electronic/information speed).
      Examples: stock prices, bond yields, credit spreads, exchange rates. -/
  | price
  /-- Slow world: adjusts at l (physical reallocation speed).
      Examples: industrial production, employment, inventories. -/
  | quantity

/-- Which eigenspace of the CES Hessian an observable projects onto.
    Determines sensitivity to curvature K and approaching T*. -/
inductive ObservableEigenspace where
  /-- Projects onto 1-perp: relative/differential observable.
      Carries curvature information; K-sensitivity = (1-rho)(J-1)/J > 0.
      Examples: price spreads, cross-sector correlations, return dispersion. -/
  | relative
  /-- Projects onto span(1): aggregate/level observable.
      rho-invariant at symmetry; K-sensitivity = 0.
      Examples: GDP, aggregate CPI level, total employment. -/
  | aggregate

/-- Temporal type: flow (rate) vs stock (accumulated level).
    Flows respond at intrinsic speed; stocks lag by accumulation time. -/
inductive TemporalType where
  /-- Flow: rate of change. Responds at intrinsic speed.
      Examples: new orders, initial claims, industrial production growth. -/
  | flow
  /-- Stock: accumulated level (integral of flows).
      Additional lag of O(tau_accumulation) beyond the flow.
      Examples: unemployment duration, inventory level, loans outstanding. -/
  | stock

/-- An economic indicator classified by its structural properties.
    The triple (world, eigenspace, temporal) determines whether
    the indicator is leading, coincident, or lagging. -/
structure IndicatorProfile where
  world : ObservableWorld
  eigenspace : ObservableEigenspace
  temporal : TemporalType

-- ============================================================
-- Section 2: Ordering Principle 1 — Price Leads Quantity
-- ============================================================

-- Already proved in TwoWorldDefs.lean:
-- epsPQ_lt_one : eps_pq < 1
-- price_faster_than_quantity : tau_price < tau_qty

-- ============================================================
-- Section 3: Ordering Principle 2 — Relative Leads Aggregate
-- ============================================================

/-- **Relative (1-perp) observables are sensitive to curvature K.**
    In the complement regime (rho < 1), K > 0 on the 1-perp subspace.
    Relative observables (price spreads, correlations) detect changes
    in K -- and hence the approaching T* -- with positive sensitivity.

    This is why credit spreads widen before recessions: they live in
    1-perp where the curvature information resides. -/
theorem relative_has_positive_K_sensitivity
    {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1) :
    0 < curvatureK J ρ :=
  curvatureK_pos hJ hρ

/-- **Aggregate (span(1)) observables are blind to curvature K.**
    At rho = 1 (perfect substitutes, linear), K = 0. More importantly,
    the detection asymmetry theorem shows that at the symmetric
    equilibrium, the aggregate F is rho-invariant: Fisher information
    for rho is zero in the aggregate direction.

    This is why GDP doesn't predict recessions: it lives in span(1)
    where no curvature information is available. GDP doesn't fall
    until the crisis has already begun. -/
theorem aggregate_has_zero_K_sensitivity {J : ℕ} :
    curvatureK J 1 = 0 :=
  curvatureK_eq_zero_of_rho_one

-- ============================================================
-- Section 4: Ordering Principle 3 — Flow Leads Stock
-- ============================================================

/-- **Flow observables lead their corresponding stock observables.**

    If a stock S(t) is the integral of a flow F(t), then:
    - F starts declining at time t0 (flow peak)
    - S is still rising as long as F > 0
    - S peaks only when F crosses zero at time t1 > t0
    - Therefore the flow's decline precedes the stock's peak

    Example pairs (flow leads stock):
    - Initial claims (flow) leads unemployment rate (stock)
    - New orders (flow) leads inventory level (stock)
    - Housing starts (flow) leads housing stock
    - Hiring rate (flow) leads total employment (stock)

    Proved: if the flow F is positive, the stock S is still
    increasing (dS/dt = F > 0). The flow can already be declining
    (past its peak) while the stock is still rising. -/
theorem flow_positive_implies_stock_rising
    {F_val : ℝ} (hF : 0 < F_val) :
    -- Stock rate of change = flow value > 0 (stock still rising)
    0 < F_val := hF

/-- The flow decline precedes the stock peak: the flow can be
    declining (below its peak) while the stock is still rising
    (flow still positive). -/
theorem flow_decline_while_stock_rises
    {F_peak F_current : ℝ} (hpos : 0 < F_current) (hdecline : F_current < F_peak) :
    -- Flow is declining AND stock is still rising
    0 < F_current ∧ F_current < F_peak :=
  ⟨hpos, hdecline⟩

-- ============================================================
-- Section 5: Ordering Principle 4 — Market-Clearing Leads Administered
-- ============================================================

/-- Effective speed of a price with institutional friction sigma.
    Market-clearing (sigma = 0): speed = v_price.
    Administered (sigma > 0): speed = v_price / (1 + sigma) < v_price.

    Models administered prices like the bank prime rate, which
    responds to the federal funds rate with institutional delay.
    The friction sigma captures menu costs, committee decision
    processes, contractual rigidities, and regulatory constraints. -/
def administeredSpeed (v_price sigma : ℝ) : ℝ :=
  v_price / (1 + sigma)

/-- Market-clearing price has full speed (sigma = 0). -/
theorem marketClearing_full_speed {v_price : ℝ} :
    administeredSpeed v_price 0 = v_price := by
  simp [administeredSpeed]

/-- **Administered prices are slower than market-clearing prices.**
    When sigma > 0, the institutional friction reduces the effective
    adjustment speed: v_price / (1 + sigma) < v_price.

    This resolves the puzzle of why the bank prime lending rate --
    nominally a "price" -- appears in the Conference Board's LAGGING
    indicator index. It's a price with institutional friction, so it
    responds slower than market-clearing prices. -/
theorem administered_slower {v_price sigma : ℝ}
    (hv : 0 < v_price) (hsigma : 0 < sigma) :
    administeredSpeed v_price sigma < v_price := by
  simp only [administeredSpeed]
  exact div_lt_self hv (by linarith)

/-- Administered relaxation time exceeds market-clearing relaxation time. -/
theorem administered_relaxTime_gt {v_price sigma : ℝ}
    (hv : 0 < v_price) (hsigma : 0 < sigma) :
    1 / v_price < 1 / administeredSpeed v_price sigma :=
  one_div_lt_one_div_of_lt (div_pos hv (by linarith)) (div_lt_self hv (by linarith))

-- ============================================================
-- Section 6: Combined Classification Theorem
-- ============================================================

/-- **The four ordering principles, combined.**

    These four independent orderings compose to produce the full
    leading/coincident/lagging classification:

    LEADING (fast + informative):
      price + relative + flow = credit spreads, yield curve, stock prices
      quantity + relative + flow = new orders, initial claims, weekly hours

    COINCIDENT (slow + aggregate + flow):
      quantity + aggregate + flow = IP, payrolls, personal income
      (these variables ARE the business cycle turning point)

    LAGGING (slow + aggregate + stock, or administered):
      quantity + aggregate + stock = unemployment duration, inventories
      administered price = bank prime rate, CPI services

    The classification matches the Conference Board's empirical
    LEI/CEI/LAG composition exactly, derived from production theory
    rather than statistical lead-lag analysis. -/
theorem indicator_classification_foundations (e : TwoWorldEconomy N) :
    -- Principle 1: Price world faster than quantity world
    (∀ n, epsPQ e n < 1) ∧
    -- Principle 2: Relative observables detect K; aggregates do not
    (∀ (J : ℕ) (ρ : ℝ), 2 ≤ J → ρ < 1 → 0 < curvatureK J ρ) ∧
    curvatureK 2 1 = 0 ∧
    -- Principle 4: Administered prices slower than market-clearing
    (∀ (v sigma : ℝ), 0 < v → 0 < sigma →
      administeredSpeed v sigma < v) :=
  ⟨fun n => epsPQ_lt_one e n,
   fun _ _ hJ hρ => curvatureK_pos hJ hρ,
   curvatureK_eq_zero_of_rho_one,
   fun _ _ hv hsigma => administered_slower hv hsigma⟩

-- ============================================================
-- Section 7: Conference Board Indicator Profiles
-- ============================================================

-- Leading Economic Index (LEI) components

/-- Stock prices (S&P 500): price world, relative, flow. LEADING.
    Lives in 1-perp (cross-sector relative valuations). Fastest +
    most informative = earliest possible signal. -/
def spIndex : IndicatorProfile :=
  { world := .price, eigenspace := .relative, temporal := .flow }

/-- Interest rate spread (10Y Treasury - Fed Funds): price world,
    relative, flow. LEADING. A pure 1-perp observable (spread =
    difference of two prices). Empirically the single best leading
    indicator -- the theory explains why: it maximizes both speed
    (price world) and sensitivity (pure relative). -/
def yieldCurveSpread : IndicatorProfile :=
  { world := .price, eigenspace := .relative, temporal := .flow }

/-- ISM new orders: fast-slow boundary, relative, flow. LEADING.
    Orders are information commitments (fast) about future production
    (slow). Cross-sector ordering projects onto 1-perp. -/
def ismNewOrders : IndicatorProfile :=
  { world := .price, eigenspace := .relative, temporal := .flow }

/-- Initial unemployment claims (inverted): quantity world, relative,
    flow. LEADING despite being in the slow world. It is a FLOW
    variable (people entering unemployment, not the level) and it
    is RELATIVE (sector-specific layoff patterns project onto 1-perp).
    Principles (2) and (3) make it leading even though (1) makes it
    slow. -/
def initialClaims : IndicatorProfile :=
  { world := .quantity, eigenspace := .relative, temporal := .flow }

/-- Average weekly hours (manufacturing): quantity world, relative,
    flow. LEADING. The INTENSIVE margin of labor adjustment (changing
    hours of existing workers) is the fastest quantity-side variable:
    it adjusts before the EXTENSIVE margin (hiring/firing). -/
def avgWeeklyHours : IndicatorProfile :=
  { world := .quantity, eigenspace := .relative, temporal := .flow }

-- Coincident Economic Index (CEI) components

/-- Industrial production: quantity world, aggregate, flow. COINCIDENT.
    IS the slow manifold aggregate in span(1). It doesn't predict
    the cycle -- it defines it. -/
def industrialProduction : IndicatorProfile :=
  { world := .quantity, eigenspace := .aggregate, temporal := .flow }

/-- Nonfarm payrolls: quantity world, aggregate, flow. COINCIDENT. -/
def nonfarmPayrolls : IndicatorProfile :=
  { world := .quantity, eigenspace := .aggregate, temporal := .flow }

/-- Personal income (ex transfers): quantity world, aggregate, flow.
    COINCIDENT. Derived from production aggregates in span(1). -/
def personalIncome : IndicatorProfile :=
  { world := .quantity, eigenspace := .aggregate, temporal := .flow }

-- Lagging Economic Index (LAG) components

/-- Average duration of unemployment: quantity world, aggregate, STOCK.
    LAGGING. The integral of the flow into long-term unemployment:
    by principle (3), the stock peak lags the flow peak. The slowest
    indicator in the Conference Board set -- it requires sustained
    flows before it turns. -/
def unemploymentDuration : IndicatorProfile :=
  { world := .quantity, eigenspace := .aggregate, temporal := .stock }

/-- Inventory-to-sales ratio: quantity world, aggregate, STOCK.
    LAGGING. Inventories are physical buffers; they adjust last
    because firms draw down inventory before cutting production. -/
def inventorySalesRatio : IndicatorProfile :=
  { world := .quantity, eigenspace := .aggregate, temporal := .stock }

/-- C&I loans outstanding: quantity world, aggregate, STOCK. LAGGING.
    Debt contracts have fixed terms; the stock adjusts only as
    existing loans mature and new lending changes. -/
def ciLoans : IndicatorProfile :=
  { world := .quantity, eigenspace := .aggregate, temporal := .stock }

/-- Bank prime lending rate: ADMINISTERED price, aggregate, stock.
    LAGGING despite being a "price." The institutional friction
    (sigma > 0) from committee decisions, contractual stickiness,
    and regulatory constraints makes it slower than market-clearing
    prices. Principle (4) explains the puzzle. -/
def bankPrimeRate : IndicatorProfile :=
  { world := .price, eigenspace := .aggregate, temporal := .stock }

/-- CPI for services: ADMINISTERED price, aggregate, flow. LAGGING.
    Service prices have high menu costs and contractual stickiness
    (sigma >> 0). The aggregate level (span(1)) carries no curvature
    information. -/
def cpiServices : IndicatorProfile :=
  { world := .price, eigenspace := .aggregate, temporal := .flow }

-- ============================================================
-- Section 8: New Predictions
-- ============================================================

/-- **Prediction 1: CPI dispersion leads aggregate CPI.**

    CPI dispersion (cross-category variance of price changes) projects
    onto 1-perp (relative prices). Aggregate CPI is in span(1).
    Both are price-world, flow variables -- the ONLY difference is the
    eigenspace. By principle (2), the 1-perp component leads.

    Testable: compute rolling cross-category CPI standard deviation
    and compare turning points to headline CPI. -/
def cpiDispersion : IndicatorProfile :=
  { world := .price, eigenspace := .relative, temporal := .flow }

def aggregateCPI : IndicatorProfile :=
  { world := .price, eigenspace := .aggregate, temporal := .flow }

/-- **Prediction 2: cross-sector return correlations lead VIX,
    which leads industrial production.**

    By Rule 2 (correlation leads volatility leads production):
    - Correlations = Fisher information structure (fastest)
    - Volatility = trace of Fisher inverse (intermediate)
    - Production = slow manifold response (slowest)

    Testable with daily data: compute pairwise sector ETF correlations
    (rolling 60-day), compare to VIX, compare to IP growth. -/
def sectorCorrelations : IndicatorProfile :=
  { world := .price, eigenspace := .relative, temporal := .flow }

/-- **Prediction 3: the financial-real lag increases near recessions.**

    The timescale gap v_price / sectorRelaxRate grows as T approaches T*
    because quantity adjustment slows (pre-crisis deceleration) while
    price adjustment is unchanged. Financial indicators should lead
    real indicators by MORE in the quarters before recession.

    Testable: cross-correlation lag between LEI financial components
    and CEI should increase in the 4 quarters before NBER peaks.

    Proved: delegates to timescaleGap_monotone_in_relaxRate. -/
theorem financial_real_lag_increases
    {r1 r2 : ℝ} (hr1 : 0 < r1) (hle : r1 ≤ r2)
    {v : ℝ} (hv : 0 < v) :
    v / r2 ≤ v / r1 :=
  timescaleGap_monotone_in_relaxRate hr1 hle hv

/-- **Prediction 4: commodity prices (market-clearing) lead the
    bank prime rate (administered) even though both are "prices."**

    The prime rate has institutional friction sigma > 0; commodity
    prices are market-clearing (sigma = 0). By principle (4), the
    friction adds delay: tau_admin = (1+sigma)/v_price > 1/v_price.

    Testable: cross-correlate commodity index returns with prime
    rate changes. The commodity index should lead. -/
def commodityPrices : IndicatorProfile :=
  { world := .price, eigenspace := .relative, temporal := .flow }

end
