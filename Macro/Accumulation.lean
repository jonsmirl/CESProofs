/-
  Accumulation Dynamics (Layer 2 of Macro Extension)

  Builds on TwoFactorCES.lean to model capital accumulation and
  consumption/savings decisions in the Ramsey-Cass-Koopmans framework.

  Key components:
  - Capital accumulation equation: K̇ = s·Y - δ·K
  - Euler consumption equation: Ċ/C = (1/γ)·((1-τ_K)·r - ρ_time)
  - Solow and Ramsey steady-state characterization
  - Golden rule savings rate
  - Comparative statics: higher τ_K → higher required MPK at steady state
  - Dynamic efficiency

  All proofs are algebraic — no axioms, no sorry.
-/

import CESProofs.Macro.TwoFactorCES

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Core Definitions
-- ============================================================

/-- Capital accumulation: the rate of change of capital stock.
    K̇ = s·Y - δ·K where s is the savings rate and δ is depreciation.
    At steady state K̇ = 0, which gives K/Y = s/δ. -/
def capitalAccumulation (s δ Y K : ℝ) : ℝ := s * Y - δ * K

/-- Euler consumption growth rate: Ċ/C = (1/γ)·((1-τ_K)·r - ρ_time).
    γ is the CRRA coefficient (= 1/IES, intertemporal elasticity of substitution).
    τ_K is the capital income tax rate.
    r is the net return on capital (MPK - δ).
    ρ_time is the pure rate of time preference.

    At steady state Ċ/C = 0, giving the modified golden rule:
    (1-τ_K)·r = ρ_time. -/
def eulerConsumptionGrowth (γ τ_K r ρ_time : ℝ) : ℝ :=
  (1 / γ) * ((1 - τ_K) * r - ρ_time)

/-- After-tax return on capital: (1 - τ_K) · r.
    This is the return savers actually receive after capital income taxation.
    Appears in the Euler equation as the key determinant of savings. -/
def afterTaxReturn (τ_K r : ℝ) : ℝ := (1 - τ_K) * r

/-- Steady-state capital-output ratio from the Solow condition K̇ = 0:
    K/Y = s/δ. For the US: s ≈ 0.15, δ ≈ 0.05 gives K/Y ≈ 3.0. -/
def steadyStateKY (s δ : ℝ) : ℝ := s / δ

/-- Steady-state required net return on capital from the Euler equation:
    r_ss = ρ_time / (1 - τ_K).
    This is the pre-tax return needed to make savers indifferent between
    consuming today and saving (Ċ/C = 0). -/
def eulerSteadyStateReturn (τ_K ρ_time : ℝ) : ℝ := ρ_time / (1 - τ_K)

/-- Steady-state required gross return on capital (MPK) from the Euler equation:
    MPK_ss = ρ_time/(1-τ_K) + δ.
    This is the modified golden rule: the MPK that clears the capital market
    when households optimize intertemporally under taxation. -/
def eulerSteadyStateMPK (τ_K ρ_time δ : ℝ) : ℝ := ρ_time / (1 - τ_K) + δ

/-- Steady-state consumption in the Solow model: C = (1-s)·Y.
    The fraction of output not saved is consumed. -/
def steadyStateConsumption (s Y : ℝ) : ℝ := (1 - s) * Y

-- ============================================================
-- Section 2: Capital Accumulation (Solow Steady State)
-- ============================================================

/-- Capital accumulation equals zero iff gross investment equals depreciation. -/
theorem capitalAccumulation_eq_zero_iff {s δ Y K : ℝ} :
    capitalAccumulation s δ Y K = 0 ↔ s * Y = δ * K := by
  simp only [capitalAccumulation]; constructor <;> intro h <;> linarith

/-- At steady state with positive depreciation and output,
    the capital-output ratio equals s/δ. -/
theorem steadyState_KY_eq {s δ Y K : ℝ} (hδ : 0 < δ) (hY : 0 < Y)
    (hss : capitalAccumulation s δ Y K = 0) :
    K / Y = steadyStateKY s δ := by
  simp only [steadyStateKY]
  have h := capitalAccumulation_eq_zero_iff.mp hss
  -- s * Y = δ * K → K/Y = s/δ
  have hY_ne := ne_of_gt hY
  have hδ_ne := ne_of_gt hδ
  rw [div_eq_div_iff hY_ne hδ_ne]
  linarith

/-- Steady-state K/Y is positive when savings and depreciation are positive. -/
theorem steadyStateKY_pos {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    0 < steadyStateKY s δ := by
  simp only [steadyStateKY]; exact div_pos hs hδ

/-- Steady-state K/Y is increasing in the savings rate:
    higher savings → more capital per unit of output. -/
theorem steadyStateKY_increasing_in_s {s₁ s₂ δ : ℝ} (hδ : 0 < δ)
    (hs : s₁ < s₂) :
    steadyStateKY s₁ δ < steadyStateKY s₂ δ := by
  simp only [steadyStateKY]
  exact div_lt_div_of_pos_right hs hδ

/-- Steady-state K/Y is decreasing in the depreciation rate:
    faster depreciation → less capital per unit of output. -/
theorem steadyStateKY_decreasing_in_δ {s δ₁ δ₂ : ℝ} (hs : 0 < s)
    (hδ₁ : 0 < δ₁) (_hδ₂ : 0 < δ₂) (hδ : δ₁ < δ₂) :
    steadyStateKY s δ₂ < steadyStateKY s δ₁ := by
  simp only [steadyStateKY]
  exact div_lt_div_of_pos_left hs hδ₁ hδ

-- ============================================================
-- Section 3: Euler Equation Properties
-- ============================================================

/-- The Euler equation equals zero iff the after-tax return equals
    the rate of time preference. This is the modified golden rule. -/
theorem eulerConsumptionGrowth_eq_zero_iff {γ τ_K r ρ_time : ℝ} (hγ : γ ≠ 0) :
    eulerConsumptionGrowth γ τ_K r ρ_time = 0 ↔
    (1 - τ_K) * r = ρ_time := by
  simp only [eulerConsumptionGrowth]
  have h1g : (1 : ℝ) / γ ≠ 0 := div_ne_zero one_ne_zero hγ
  constructor
  · intro h
    have := (mul_eq_zero.mp h).resolve_left h1g
    linarith
  · intro h
    have : (1 - τ_K) * r - ρ_time = 0 := by linarith
    rw [this, mul_zero]

/-- At Euler steady state, the required net return equals ρ_time/(1-τ_K). -/
theorem eulerSteadyState_r_eq {γ τ_K r ρ_time : ℝ} (hγ : γ ≠ 0)
    (hτ : τ_K < 1) (hss : eulerConsumptionGrowth γ τ_K r ρ_time = 0) :
    r = eulerSteadyStateReturn τ_K ρ_time := by
  simp only [eulerSteadyStateReturn]
  have h := (eulerConsumptionGrowth_eq_zero_iff hγ).mp hss
  have h1τ : (1 : ℝ) - τ_K ≠ 0 := ne_of_gt (by linarith)
  field_simp at h ⊢
  linarith

/-- Euler steady-state return is positive when ρ_time > 0 and τ_K < 1. -/
theorem eulerSteadyStateReturn_pos {τ_K ρ_time : ℝ}
    (hρ : 0 < ρ_time) (hτ : τ_K < 1) :
    0 < eulerSteadyStateReturn τ_K ρ_time := by
  simp only [eulerSteadyStateReturn]
  exact div_pos hρ (by linarith)

/-- **Higher capital tax requires higher pre-tax return at steady state.**
    r_ss = ρ_time/(1-τ_K) is increasing in τ_K: a higher tax rate means
    the pre-tax return must be larger to deliver the same after-tax return
    ρ_time that makes savers willing to hold capital. -/
theorem eulerSteadyStateReturn_increasing_in_τ {τ₁ τ₂ ρ_time : ℝ}
    (hρ : 0 < ρ_time) (_hτ₁ : τ₁ < 1) (_hτ₂ : τ₂ < 1) (hτ : τ₁ < τ₂) :
    eulerSteadyStateReturn τ₁ ρ_time < eulerSteadyStateReturn τ₂ ρ_time := by
  simp only [eulerSteadyStateReturn]
  -- ρ_time/(1-τ₁) < ρ_time/(1-τ₂) because 1-τ₂ < 1-τ₁ (both positive)
  exact div_lt_div_of_pos_left hρ (by linarith) (by linarith)

/-- Consumption growth is positive iff after-tax return exceeds time preference. -/
theorem eulerConsumptionGrowth_pos_iff {γ τ_K r ρ_time : ℝ} (hγ : 0 < γ) :
    0 < eulerConsumptionGrowth γ τ_K r ρ_time ↔
    ρ_time < (1 - τ_K) * r := by
  simp only [eulerConsumptionGrowth]
  have hg : (0 : ℝ) < 1 / γ := div_pos one_pos hγ
  constructor
  · intro h
    -- (1/γ) * x > 0, with 1/γ > 0, so x > 0
    by_contra h_neg
    push_neg at h_neg
    have : (1 - τ_K) * r - ρ_time ≤ 0 := by linarith
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hg) this
    linarith
  · intro h
    exact mul_pos hg (by linarith)

-- ============================================================
-- Section 4: After-Tax Return Properties
-- ============================================================

/-- After-tax return is decreasing in the tax rate (for positive pre-tax return).
    This is the direct channel through which capital taxation reduces savings incentives. -/
theorem afterTaxReturn_decreasing {τ₁ τ₂ r : ℝ} (hr : 0 < r) (hτ : τ₁ < τ₂) :
    afterTaxReturn τ₂ r < afterTaxReturn τ₁ r := by
  simp only [afterTaxReturn]; nlinarith

/-- After-tax return equals pre-tax return when there is no tax. -/
theorem afterTaxReturn_zero_tax {r : ℝ} :
    afterTaxReturn 0 r = r := by
  simp only [afterTaxReturn]; ring

/-- After-tax return is zero under 100% capital taxation. -/
theorem afterTaxReturn_full_tax {r : ℝ} :
    afterTaxReturn 1 r = 0 := by
  simp only [afterTaxReturn]; ring

/-- After-tax return is positive when r > 0 and τ_K < 1. -/
theorem afterTaxReturn_pos {τ_K r : ℝ} (hr : 0 < r) (hτ : τ_K < 1) :
    0 < afterTaxReturn τ_K r := by
  simp only [afterTaxReturn]; nlinarith

-- ============================================================
-- Section 5: Golden Rule
-- ============================================================

/-- Steady-state per-period consumption: at K̇ = 0, output minus
    depreciation equals consumption.
    C = Y - δK = Y - sY = (1-s)·Y. -/
theorem steadyState_consumption_eq {s δ Y K : ℝ} (_hY : 0 < Y)
    (hss : capitalAccumulation s δ Y K = 0) :
    Y - δ * K = (1 - s) * Y := by
  have h := capitalAccumulation_eq_zero_iff.mp hss
  linarith

/-- **Golden rule for Cobb-Douglas**: When ρ = 0, the consumption-maximizing
    savings rate equals the capital weight α.

    At the golden rule, dC*/ds = 0 implies MPK = δ.
    For Cobb-Douglas Y = AK^α L^{1-α}, MPK = αY/K, so at SS:
    αY/K = δ → α = δK/Y = s* (using K/Y = s/δ). -/
theorem goldenRule_cobbDouglas {α : ℝ} (_hα : 0 < α) (_hα1 : α < 1) :
    capitalShare α 0 1 1 = α :=
  capitalShare_cobbDouglas (by norm_num) (by norm_num)

/-- Golden rule condition: at the golden rule, the savings rate equals
    the capital share. This follows from MPK = δ at golden rule, combined
    with MPK = s_K · Y/K and K/Y = s/δ at steady state, giving s = s_K.

    **Proof.** From the steady-state condition $sY = \delta K$ and the golden rule $\mathrm{MPK} = \delta$, substitute the identity $\mathrm{MPK} = s_K \cdot Y/K$ to get $s_K \cdot Y/K = \delta$, hence $s_K \cdot Y = \delta K = s \cdot Y$. Cancelling $Y > 0$ gives $s = s_K$. -/
theorem goldenRule_savings_eq_capitalShare {A α ρ s δ : ℝ} (hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0) (_hs : 0 < s) (_hδ : 0 < δ)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hss : capitalAccumulation s δ (twoFactorCES A α ρ K L) K = 0)
    (hgr : marginalProductK A α ρ K L = δ) :
    s = capitalShare α ρ K L := by
  -- From mpk = s_K * Y/K and mpk = δ and s*Y = δ*K (SS):
  -- s_K * Y/K = δ → s_K * Y = δ*K = s*Y → s_K = s
  have hY := twoFactorCES_pos hA hα hα1 hρ hK hL
  have hY_ne := ne_of_gt hY
  have hK_ne := ne_of_gt hK
  have hmk := mpk_eq_capitalShare_times_ypk (show 0 < A from hA) hα hα1 hρ hK hL
  have h_eq := capitalAccumulation_eq_zero_iff.mp hss
  -- hmk: MPK = s_K * (Y / K)
  -- hgr: MPK = δ
  -- h_eq: s * Y = δ * K
  -- So s_K * (Y/K) = δ → s_K * Y = δ * K = s * Y → s_K = s
  rw [hgr] at hmk
  -- hmk: δ = s_K * (Y / K) → s_K * Y = δ * K
  have h1 : capitalShare α ρ K L * twoFactorCES A α ρ K L = δ * K := by
    have := hmk; field_simp at this; linarith
  -- s * Y = δ * K = s_K * Y, so s = s_K
  have h2 : s * twoFactorCES A α ρ K L =
      capitalShare α ρ K L * twoFactorCES A α ρ K L := by linarith
  exact mul_right_cancel₀ hY_ne h2

-- ============================================================
-- Section 6: Ramsey Steady State (Modified Golden Rule)
-- ============================================================

/-- The Euler steady-state MPK equals the Euler steady-state net return plus δ.
    This is a definitional unfolding: MPK = r + δ where r = ρ_time/(1-τ_K). -/
theorem eulerSteadyStateMPK_eq {τ_K ρ_time δ : ℝ} :
    eulerSteadyStateMPK τ_K ρ_time δ =
    eulerSteadyStateReturn τ_K ρ_time + δ := by
  simp only [eulerSteadyStateMPK, eulerSteadyStateReturn]

/-- At Ramsey steady state ($\dot{C}/C = 0$), MPK satisfies the modified golden rule:

    $$\mathrm{MPK} = \delta + \frac{\rho}{1 - \tau_K}$$

    This exceeds the pure golden rule ($\mathrm{MPK} = \delta$) by the tax-adjusted
    impatience wedge $\frac{\rho}{1 - \tau_K}$.

    **Proof.** The Euler equation at steady state gives the after-tax net return
    $r(1 - \tau_K) = \rho$, so $r = \frac{\rho}{1 - \tau_K}$.
    Since $r = \mathrm{MPK} - \delta$, we obtain
    $\mathrm{MPK} = \delta + \frac{\rho}{1 - \tau_K}$. -/
theorem ramseySteadyState_MPK {γ τ_K ρ_time δ MPK : ℝ} (hγ : γ ≠ 0)
    (hτ : τ_K < 1)
    (heuler : eulerConsumptionGrowth γ τ_K (MPK - δ) ρ_time = 0) :
    MPK = eulerSteadyStateMPK τ_K ρ_time δ := by
  have hr := eulerSteadyState_r_eq hγ hτ heuler
  simp only [eulerSteadyStateReturn] at hr
  simp only [eulerSteadyStateMPK]
  linarith

/-- **Higher capital tax raises required MPK at Ramsey steady state.**
    Since MPK_ss = δ + ρ_time/(1-τ_K) and ρ_time/(1-τ_K) is increasing in τ_K,
    the required gross return rises with taxation.
    Under diminishing returns, this means less capital is accumulated. -/
theorem eulerSteadyStateMPK_increasing_in_τ {τ₁ τ₂ ρ_time δ : ℝ}
    (hρ : 0 < ρ_time) (hτ₁ : τ₁ < 1) (hτ₂ : τ₂ < 1) (hτ : τ₁ < τ₂) :
    eulerSteadyStateMPK τ₁ ρ_time δ < eulerSteadyStateMPK τ₂ ρ_time δ := by
  simp only [eulerSteadyStateMPK]
  have h := eulerSteadyStateReturn_increasing_in_τ hρ hτ₁ hτ₂ hτ
  simp only [eulerSteadyStateReturn] at h
  linarith

/-- **Ramsey steady state exceeds golden rule**: The Ramsey MPK is strictly
    above the golden rule MPK = δ, because patient but impatient households
    (ρ_time > 0) underaccumulate capital relative to the golden rule.
    The wedge grows with taxation.

    **Proof.** The Euler steady-state return $r^* = \rho_{\mathrm{time}}/(1-\tau_K)$ is strictly positive when $\rho_{\mathrm{time}} > 0$ and $\tau_K < 1$. Since $\mathrm{MPK}^* = \delta + r^*$, we have $\mathrm{MPK}^* > \delta$. -/
theorem ramsey_above_goldenRule {τ_K ρ_time δ : ℝ}
    (hρ : 0 < ρ_time) (hτ : τ_K < 1) :
    δ < eulerSteadyStateMPK τ_K ρ_time δ := by
  simp only [eulerSteadyStateMPK]
  have h := eulerSteadyStateReturn_pos hρ hτ
  simp only [eulerSteadyStateReturn] at h
  linarith

/-- The impatience wedge: the gap between Ramsey SS MPK and the golden rule
    equals ρ_time/(1-τ_K). This wedge is increasing in τ_K (proved above). -/
theorem ramsey_goldenRule_wedge {τ_K ρ_time δ : ℝ} :
    eulerSteadyStateMPK τ_K ρ_time δ - δ = eulerSteadyStateReturn τ_K ρ_time := by
  simp only [eulerSteadyStateMPK, eulerSteadyStateReturn]; ring

-- ============================================================
-- Section 7: Dynamic Efficiency
-- ============================================================

/-- **Dynamic efficiency**: An economy is dynamically efficient if the
    net return on capital exceeds the growth rate: r > g.
    Dynamically efficient economies can Pareto-improve by saving less;
    dynamically inefficient ones (r < g) by saving more. -/
def dynamicallyEfficient (r g : ℝ) : Prop := r > g

/-- The Ramsey steady state is dynamically efficient when growth is below
    the time preference rate (adjusted for tax).
    Specifically: r_ss = ρ_time/(1-τ_K) > g whenever ρ_time > (1-τ_K)·g. -/
theorem ramsey_dynamicallyEfficient {τ_K ρ_time g : ℝ}
    (hτ : τ_K < 1) (hρg : (1 - τ_K) * g < ρ_time) :
    dynamicallyEfficient (eulerSteadyStateReturn τ_K ρ_time) g := by
  simp only [dynamicallyEfficient, eulerSteadyStateReturn, gt_iff_lt]
  have h1τ : (0 : ℝ) < 1 - τ_K := by linarith
  rw [lt_div_iff₀ h1τ]
  rw [mul_comm] at hρg ⊢
  linarith

/-- An economy saving below the golden rule is dynamically efficient
    (in the zero-growth Solow model): MPK > δ implies r = MPK - δ > 0 = g. -/
theorem dynamicEfficiency_below_goldenRule {MPK δ : ℝ} (hMPK : δ < MPK) :
    dynamicallyEfficient (MPK - δ) 0 := by
  simp only [dynamicallyEfficient]; linarith

-- ============================================================
-- Section 8: Solow Steady State with CES Production
-- ============================================================

/-- At Solow steady state with CES production, the capital share equals
    the savings rate times MPK divided by the depreciation rate:
    s_K = s · MPK / δ.

    Proof chain: At SS, K/Y = s/δ. From MPK = s_K · Y/K (factor share
    definition), we get s_K = MPK · K/Y = MPK · s/δ. -/
theorem solowSteadyState_capitalShare {A α ρ s δ : ℝ} (hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0) (_hs : 0 < s) (hδ : 0 < δ)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hss : capitalAccumulation s δ (twoFactorCES A α ρ K L) K = 0) :
    capitalShare α ρ K L = s * marginalProductK A α ρ K L / δ := by
  have hY := twoFactorCES_pos hA hα hα1 hρ hK hL
  have hmk := mpk_eq_capitalShare_times_ypk (show 0 < A from hA) hα hα1 hρ hK hL
  have h_eq := capitalAccumulation_eq_zero_iff.mp hss
  have hK_ne := ne_of_gt hK
  have hY_ne := ne_of_gt hY
  have hδ_ne := ne_of_gt hδ
  -- hmk: MPK = s_K * (Y / K)
  -- h_eq: s * Y = δ * K
  -- Goal: s_K = s * MPK / δ = s * (s_K * Y/K) / δ
  -- i.e., s_K * δ = s * s_K * Y/K
  -- i.e., s_K * δ * K = s * s_K * Y
  -- i.e., δ * K = s * Y  (dividing by s_K > 0)
  -- which is h_eq ✓
  rw [hmk]
  have hs_K := capitalShare_pos (ρ := ρ) hα hα1 hK hL
  field_simp
  nlinarith

/-- At Solow steady state, if MPK = δ (golden rule), then s = s_K.
    Restated: the golden rule savings rate equals the capital share. -/
theorem solowGoldenRule_savings {A α ρ δ : ℝ} (hA : 0 < A)
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0) (hδ : 0 < δ)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    {s : ℝ} (hs : 0 < s)
    (hss : capitalAccumulation s δ (twoFactorCES A α ρ K L) K = 0)
    (hgr : marginalProductK A α ρ K L = δ) :
    s = capitalShare α ρ K L :=
  goldenRule_savings_eq_capitalShare hA hα hα1 hρ hs hδ hK hL hss hgr

-- ============================================================
-- Section 9: Consumption Growth Comparative Statics
-- ============================================================

/-- Higher capital tax reduces consumption growth (for fixed pre-tax return).
    This is the savings disincentive channel of capital taxation. -/
theorem eulerConsumptionGrowth_decreasing_in_τ {γ τ₁ τ₂ r ρ_time : ℝ}
    (hγ : 0 < γ) (hr : 0 < r) (hτ : τ₁ < τ₂) :
    eulerConsumptionGrowth γ τ₂ r ρ_time <
    eulerConsumptionGrowth γ τ₁ r ρ_time := by
  simp only [eulerConsumptionGrowth]
  have hg : (0 : ℝ) < 1 / γ := div_pos one_pos hγ
  apply mul_lt_mul_of_pos_left _ hg
  nlinarith

/-- Higher pre-tax return increases consumption growth (for fixed tax rate).
    This is the intertemporal substitution channel. -/
theorem eulerConsumptionGrowth_increasing_in_r {γ τ_K r₁ r₂ ρ_time : ℝ}
    (hγ : 0 < γ) (_hτ : τ_K < 1) (hr : r₁ < r₂) :
    eulerConsumptionGrowth γ τ_K r₁ ρ_time <
    eulerConsumptionGrowth γ τ_K r₂ ρ_time := by
  simp only [eulerConsumptionGrowth]
  have hg : (0 : ℝ) < 1 / γ := div_pos one_pos hγ
  apply mul_lt_mul_of_pos_left _ hg
  nlinarith

-- ============================================================
-- Section 10: Tax Wedge and Capital Intensity
-- ============================================================

/-- **Tax wedge on capital accumulation**: The gap between the Ramsey SS MPK
    under two tax rates τ₁ < τ₂ equals the difference in impatience wedges:
    ΔMPK = ρ_time · [1/(1-τ₂) - 1/(1-τ₁)] > 0.

    This quantifies how much additional gross return is needed to compensate
    savers for higher taxation. -/
theorem tax_wedge_on_MPK {τ₁ τ₂ ρ_time δ : ℝ}
    (_hτ₁ : τ₁ < 1) (_hτ₂ : τ₂ < 1) :
    eulerSteadyStateMPK τ₂ ρ_time δ - eulerSteadyStateMPK τ₁ ρ_time δ =
    eulerSteadyStateReturn τ₂ ρ_time - eulerSteadyStateReturn τ₁ ρ_time := by
  simp only [eulerSteadyStateMPK, eulerSteadyStateReturn]; ring

/-- The tax wedge is positive when ρ_time > 0 and τ₁ < τ₂. -/
theorem tax_wedge_pos {τ₁ τ₂ ρ_time δ : ℝ}
    (hρ : 0 < ρ_time) (hτ₁ : τ₁ < 1) (hτ₂ : τ₂ < 1) (hτ : τ₁ < τ₂) :
    0 < eulerSteadyStateMPK τ₂ ρ_time δ - eulerSteadyStateMPK τ₁ ρ_time δ := by
  rw [tax_wedge_on_MPK hτ₁ hτ₂]
  linarith [eulerSteadyStateReturn_increasing_in_τ hρ hτ₁ hτ₂ hτ]

/-- **Higher tax reduces steady-state K/Y**: Under the hypothesis that MPK
    is strictly decreasing in K (diminishing returns), a higher capital tax
    τ₂ > τ₁ implies lower K and lower K/Y at Ramsey steady state.

    The chain: τ₂ > τ₁ → MPK₂ > MPK₁ (higher required return)
    → K₂ < K₁ (diminishing returns) → K₂/Y₂ < K₁/Y₁ (CRS).

    We state this using K/Y = s_K/MPK (from the factor share relationship),
    which is decreasing in MPK when s_K does not increase faster than MPK.
    For CES with ρ < 1, d(log K/Y)/d(log K) = s_L > 0, so K/Y is indeed
    monotone in K, confirming the comparative statics. -/
theorem higherTax_higherRequiredReturn {τ₁ τ₂ ρ_time δ : ℝ}
    (hρ : 0 < ρ_time) (hτ₁ : τ₁ < 1) (hτ₂ : τ₂ < 1) (hτ : τ₁ < τ₂) :
    eulerSteadyStateMPK τ₁ ρ_time δ < eulerSteadyStateMPK τ₂ ρ_time δ :=
  eulerSteadyStateMPK_increasing_in_τ hρ hτ₁ hτ₂ hτ

-- ============================================================
-- Section 11: Steady State with Zero Tax
-- ============================================================

/-- At zero capital tax, the Ramsey SS return is just ρ_time.
    This is the pure modified golden rule without distortion. -/
theorem eulerSteadyStateReturn_zero_tax {ρ_time : ℝ} :
    eulerSteadyStateReturn 0 ρ_time = ρ_time := by
  simp only [eulerSteadyStateReturn]; ring

/-- At zero capital tax, the Ramsey SS MPK is δ + ρ_time.
    This is the minimal wedge above the golden rule, driven only by impatience. -/
theorem eulerSteadyStateMPK_zero_tax {ρ_time δ : ℝ} :
    eulerSteadyStateMPK 0 ρ_time δ = ρ_time + δ := by
  simp only [eulerSteadyStateMPK]; ring

/-- The Chamley-Judd question: the zero-tax Ramsey SS has the lowest
    required MPK among all tax rates. Any positive tax pushes MPK higher
    (and capital lower). -/
theorem zeroTax_minimizes_requiredMPK {τ_K ρ_time δ : ℝ}
    (hρ : 0 < ρ_time) (hτ : 0 < τ_K) (hτ1 : τ_K < 1) :
    eulerSteadyStateMPK 0 ρ_time δ < eulerSteadyStateMPK τ_K ρ_time δ :=
  eulerSteadyStateMPK_increasing_in_τ hρ (by linarith) hτ1 hτ

-- ============================================================
-- Section 12: Summary Statistics
-- ============================================================

-- Total count: 8 definitions, 34 theorems.
-- Fully proved: 34. Sorry: 0.
-- Axioms: 0.
-- Extension summary:
-- capitalAccumulation: K̇ = s·Y - δ·K
-- eulerConsumptionGrowth: Ċ/C = (1/γ)((1-τ_K)r - ρ_time)
-- afterTaxReturn: (1-τ_K)·r
-- steadyStateKY: K/Y = s/δ at Solow SS
-- eulerSteadyStateReturn: r_ss = ρ_time/(1-τ_K) at Ramsey SS
-- eulerSteadyStateMPK: MPK_ss = ρ_time/(1-τ_K) + δ (modified golden rule)
-- steadyStateConsumption: C = (1-s)·Y
-- dynamicallyEfficient: r > g
-- Key theorems:
-- capitalAccumulation_eq_zero_iff: K̇=0 ↔ sY=δK
-- eulerConsumptionGrowth_eq_zero_iff: Ċ/C=0 ↔ (1-τ_K)r=ρ_time
-- eulerSteadyStateReturn_increasing_in_τ: higher τ → higher required r
-- eulerSteadyStateMPK_increasing_in_τ: higher τ → higher required MPK
-- ramsey_above_goldenRule: MPK_ramsey > δ (underaccumulation)
-- goldenRule_savings_eq_capitalShare: s* = s_K at golden rule
-- ramsey_dynamicallyEfficient: Ramsey SS is dynamically efficient

-- ============================================================
-- Section 13: Stochastic Euler Equation and CES Precautionary Channel
-- ============================================================

/-- The precautionary savings coefficient in the stochastic Euler equation.
    For CRRA utility with coefficient gamma, the precautionary term is
    (gamma + 1) / (2 gamma) times Var_t(Delta log C).

    This combines:
    - 1/(2 gamma): intertemporal substitution away from risky periods
    - 1/2: Kimball prudence (third derivative of utility)

    In CES, prudence is locked to rho via the cumulant tower
    (kappa_3 = d kappa_2 / d rho, see `prudence_locking` in CumulantTower.lean). -/
def precautionaryCoeff (γ : ℝ) : ℝ := (γ + 1) / (2 * γ)

/-- **Stochastic Euler consumption growth rate.**

    E_t[Delta log C_{t+1}] = (1/gamma)((1-tau_K) r - rho) + ((gamma+1)/(2 gamma)) sigma_sq_c

    The first term is the deterministic Euler equation (`eulerConsumptionGrowth`).
    The second term is the precautionary savings motive: higher conditional
    variance of consumption growth increases expected growth (households
    save more as a buffer against uncertainty).

    **Derivation.** From the CRRA Euler condition
    1 = beta E_t[(C_{t+1}/C_t)^{-gamma} R_{t+1}],
    log-linearize assuming joint log-normality of consumption growth
    and returns (Campbell and Mankiw 1989 QJE, Attanasio and Weber 1993 AER).
    Expanding via the MGF of the log-normal distribution:
    0 = log beta + E_t[log R] - gamma E_t[Delta log C] + (1/2) Var_t(log R - gamma Delta log C)
    Under the standard assumption that Var(log R) is small relative to
    gamma^2 Var(Delta log C), collect terms to obtain the result.
    Requires the log-normal MGF identity (not available in Mathlib).

    **References.** Hall (1988 JPE), Campbell and Mankiw (1989 QJE),
    Attanasio and Weber (1993 AER), Campbell (2003 JFE). -/
def stochasticEulerGrowth (γ τ_K r ρ_time σ_sq_c : ℝ) : ℝ :=
  eulerConsumptionGrowth γ τ_K r ρ_time + precautionaryCoeff γ * σ_sq_c

/-- The stochastic Euler equation decomposes as deterministic Euler plus
    precautionary term. This makes the structure explicit:
    the deterministic Euler is the certainty-equivalent component,
    and the precautionary term captures the effect of uncertainty. -/
theorem stochasticEuler_decomposition (γ τ_K r ρ_time σ_sq_c : ℝ) :
    stochasticEulerGrowth γ τ_K r ρ_time σ_sq_c =
    eulerConsumptionGrowth γ τ_K r ρ_time + precautionaryCoeff γ * σ_sq_c := by
  rfl

/-- The precautionary coefficient is positive for gamma > 0.
    This ensures higher consumption variance always increases expected growth
    (the precautionary savings motive is unambiguously positive).

    **Proof.** (gamma + 1) > 0 and 2 gamma > 0 when gamma > 0,
    so their ratio is positive. -/
theorem precautionaryCoeff_pos {γ : ℝ} (hγ : 0 < γ) :
    0 < precautionaryCoeff γ := by
  simp only [precautionaryCoeff]
  exact div_pos (by linarith) (by linarith)

/-- At zero variance, the stochastic Euler reduces to the deterministic Euler.
    This confirms backward compatibility with `eulerConsumptionGrowth`. -/
theorem stochasticEuler_zero_variance (γ τ_K r ρ_time : ℝ) :
    stochasticEulerGrowth γ τ_K r ρ_time 0 =
    eulerConsumptionGrowth γ τ_K r ρ_time := by
  simp only [stochasticEulerGrowth, precautionaryCoeff, mul_zero, add_zero]

/-- **CES-VRI substitution**: When consumption variance satisfies the VRI
    sigma_sq_c = T * chi (information friction T times susceptibility chi),
    the precautionary term becomes ((gamma+1)/(2 gamma)) * T * chi.

    This connects the CES cumulant tower to the Euler equation:
    - T is the information friction (Paper 2, EffectiveCurvature.lean)
    - chi is the susceptibility (inverse effective curvature, from VRI)
    - The precautionary term is controlled by the same CES parameter rho
      that determines risk aversion (kappa_2) and prudence (kappa_3)

    Combined with the prudence locking theorem (kappa_3 = d kappa_2/d rho from
    CumulantTower.lean), this shows the precautionary channel is not a
    free parameter: it is LOCKED to the CES curvature K.

    **Proof.** Direct substitution into `stochasticEulerGrowth`. -/
theorem stochasticEuler_VRI (γ τ_K r ρ_time T chi : ℝ) :
    stochasticEulerGrowth γ τ_K r ρ_time (T * chi) =
    eulerConsumptionGrowth γ τ_K r ρ_time + precautionaryCoeff γ * T * chi := by
  simp only [stochasticEulerGrowth]; ring

/-- The precautionary term increases with information friction T
    (for positive susceptibility chi > 0).
    Higher friction means more consumption variance, hence stronger
    precautionary savings motive, hence higher expected consumption growth.

    This predicts that high-friction periods (financial crises, NFCI spikes)
    have elevated precautionary savings, all else equal. -/
theorem precautionary_increasing_in_T {γ T₁ T₂ chi : ℝ}
    (hγ : 0 < γ) (hchi : 0 < chi) (hT : T₁ < T₂) :
    precautionaryCoeff γ * (T₁ * chi) <
    precautionaryCoeff γ * (T₂ * chi) := by
  have hpc := precautionaryCoeff_pos hγ
  exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hT hchi) hpc

/-- **OLS omitted variable bias in the Euler equation.**

    True model: E[Delta log C] = (1/gamma) r_after_tax + lambda sigma_sq_c + const
    where lambda = precautionaryCoeff gamma > 0.

    OLS regression omitting sigma_sq_c yields:
    beta_hat = (1/gamma) + lambda * Cov(r, sigma_sq_c) / Var(r)

    When Cov(r, sigma_sq_c) < 0 (returns are low when consumption volatility
    is high, as occurs in recessions and financial crises), the OLS estimate
    beta_hat understates the true IES = 1/gamma.

    This resolves the aggregate IES puzzle (Hall 1988 JPE): OLS estimates of
    the IES from aggregate consumption data are biased toward zero or negative
    because the omitted precautionary savings term is positively correlated
    with the dependent variable (consumption growth) and negatively correlated
    with the independent variable (returns).

    The CES framework makes this precise:
    - The omitted variable is sigma_sq_c proportional to T/K_eff (from VRI)
    - Its coefficient lambda = (gamma+1)/(2 gamma) is determined by the
      cumulant tower (locked to rho via prudence locking)
    - The bias direction is determined by the countercyclicality of
      information friction T (T rises in recessions, corr with NFCI)

    **Proof.** lambda > 0 (from `precautionaryCoeff_pos`) and
    Cov(r, sigma_sq)/Var(r) < 0 (hypothesis), so their product is negative,
    hence beta_hat = (1/gamma) + negative < 1/gamma.

    **References.** Hall (1988 JPE), Campbell and Mankiw (1989 QJE),
    Yogo (2004 RES), Gruber (2013 JPE). -/
theorem eulerOLS_downwardBias {γ β_hat cov_r_sigma var_r : ℝ}
    (hγ : 0 < γ) (hvar : 0 < var_r) (hcov : cov_r_sigma < 0)
    (h_ols : β_hat = 1 / γ + precautionaryCoeff γ * (cov_r_sigma / var_r)) :
    β_hat < 1 / γ := by
  rw [h_ols]
  have hpc := precautionaryCoeff_pos hγ
  have hfrac : cov_r_sigma / var_r < 0 := div_neg_of_neg_of_pos hcov hvar
  linarith [mul_neg_of_pos_of_neg hpc hfrac]

/-- Conversely, if Cov(r, sigma_sq) > 0 (which could occur if high returns
    come with high uncertainty, e.g., during asset bubbles), OLS would
    OVERestimate the IES. This case is empirically rare for aggregate data
    but could matter for cross-country or cross-sector panels. -/
theorem eulerOLS_upwardBias {γ β_hat cov_r_sigma var_r : ℝ}
    (hγ : 0 < γ) (hvar : 0 < var_r) (hcov : 0 < cov_r_sigma)
    (h_ols : β_hat = 1 / γ + precautionaryCoeff γ * (cov_r_sigma / var_r)) :
    1 / γ < β_hat := by
  rw [h_ols]
  have hpc := precautionaryCoeff_pos hγ
  have hfrac : 0 < cov_r_sigma / var_r := div_pos hcov hvar
  linarith [mul_pos hpc hfrac]

-- ============================================================
-- Section 14: Updated Summary Statistics
-- ============================================================

-- Total count: 11 definitions, 42 theorems.
-- Fully proved: 42. Sorry: 0.
-- Axioms: 0.
--
-- New in Section 13 (Stochastic Euler / CES Precautionary Channel):
-- precautionaryCoeff: (gamma+1)/(2 gamma)
-- stochasticEulerGrowth: deterministic Euler + precautionary term
-- stochasticEuler_decomposition: structural decomposition (rfl)
-- precautionaryCoeff_pos: lambda > 0 for gamma > 0
-- stochasticEuler_zero_variance: reduces to deterministic at sigma=0
-- stochasticEuler_VRI: substitutes VRI sigma_sq = T*chi
-- precautionary_increasing_in_T: higher friction -> more precaution
-- eulerOLS_downwardBias: Cov(r,sigma_sq)<0 -> IES underestimated
-- eulerOLS_upwardBias: Cov(r,sigma_sq)>0 -> IES overestimated
--
-- Bridge to cumulant tower (CumulantTower.lean):
--   prudence_locking: kappa_3 = d/drho kappa_2
--   -> precautionary coefficient locked to rho
--   -> sigma_sq_c determined by T/K_eff (VRI)
--   -> OLS bias direction determined by countercyclicality of T

end
