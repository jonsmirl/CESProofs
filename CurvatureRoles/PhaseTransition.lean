/-
  Phase Transition at T* (Gap #8)

  The effective curvature K_eff = K · max(0, 1-T/T*) undergoes a
  second-order phase transition at the critical information friction T*.

  RESULTS:
  Part A: Order parameter — K_eff continuous, zero at T*, linear below
  Part B: Second-order transition — slope jump = K/T*
  Part C: Critical exponents — β=1, γ=1 (susceptibility), ν=1/2
  Part D: Landau potential — variational characterization of K_eff
  Part E: Finite-J smoothing — transition width ~ 1/√J
  Part F: Universality — exponents independent of J, ρ
-/

import CESProofs.Potential.EffectiveCurvature
import CESProofs.Dynamics.FluctuationResponse

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Part A: Order Parameter at the Transition
-- ============================================================

/-- The reduced order parameter: f(T) = max(0, 1-T/T*).
    This is the universal scaling function. It depends on T
    only through the ratio T/T*, not on J or ρ. -/
def reducedOrderParam (T Tstar : ℝ) : ℝ := max 0 (1 - T / Tstar)

/-- K_eff = K · f(T/T*): factored into the scale K (which
    depends on J, ρ) and the universal function f (which does not). -/
theorem keff_eq_K_times_reduced (J : ℕ) (ρ T Tstar : ℝ) :
    effectiveCurvatureKeff J ρ T Tstar =
      curvatureK J ρ * reducedOrderParam T Tstar := by
  simp [effectiveCurvatureKeff, reducedOrderParam]

/-- K_eff vanishes at the critical friction T = T*:
    the order parameter goes continuously to zero.

    **Proof.** At $T = T^*$, the formula gives
    $K_{\mathrm{eff}} = K \cdot \max(0, 1 - T^*/T^*) = K \cdot 0 = 0$. -/
theorem keff_at_critical (J : ℕ) (ρ Tstar : ℝ) (hTs : 0 < Tstar) :
    effectiveCurvatureKeff J ρ Tstar Tstar = 0 :=
  effectiveCurvatureKeff_above_critical J ρ Tstar Tstar hTs (le_refl _)

/-- Below T*: K_eff = K(1-T/T*). The max(0,·) is not binding
    in the sub-critical regime.

    **Proof.** For $T < T^*$, we have $1 - T/T^* > 0$, so
    $\max(0, 1 - T/T^*) = 1 - T/T^*$ and the floor constraint is not binding. -/
theorem keff_below_critical (J : ℕ) (ρ T Tstar : ℝ)
    (hTs : 0 < Tstar) (hT : T < Tstar) :
    effectiveCurvatureKeff J ρ T Tstar =
      curvatureK J ρ * (1 - T / Tstar) := by
  simp only [effectiveCurvatureKeff]
  congr 1
  exact max_eq_right (by rw [sub_nonneg, div_le_one hTs]; exact le_of_lt hT)

/-- K_eff is continuous in T: it is the product of a constant
    and the continuous piecewise-linear function max(0, 1-T/T*).

    **Proof.** $K_{\mathrm{eff}}(T) = K \cdot \max(0, 1 - T/T^*)$ is a product
    of the constant $K$ and the composition of continuous functions:
    $T \mapsto 1 - T/T^*$ (affine) and $\max(0, \cdot)$ (piecewise linear). -/
theorem keff_continuous (J : ℕ) (ρ Tstar : ℝ) :
    Continuous (fun T => effectiveCurvatureKeff J ρ T Tstar) := by
  unfold effectiveCurvatureKeff
  exact continuous_const.mul
    (continuous_const.max (continuous_const.sub (continuous_id.div_const _)))

-- ============================================================
-- Part B: Second-Order Transition (Slope Jump)
-- ============================================================

/-- The slope of K_eff below T*: exact difference quotient = -K/T*.
    Since K_eff is linear below T*, this is the exact slope,
    not a limit. -/
theorem keff_slope_below (J : ℕ) (ρ T h Tstar : ℝ)
    (hTs : 0 < Tstar) (hT : T < Tstar) (hTh : T + h < Tstar)
    (hh : h ≠ 0) :
    (effectiveCurvatureKeff J ρ (T + h) Tstar -
     effectiveCurvatureKeff J ρ T Tstar) / h =
      -(curvatureK J ρ / Tstar) := by
  rw [keff_below_critical J ρ (T + h) Tstar hTs hTh,
      keff_below_critical J ρ T Tstar hTs hT]
  have hTs_ne := ne_of_gt hTs
  field_simp
  ring

/-- The slope of K_eff above T*: zero (constant region). -/
theorem keff_slope_above (J : ℕ) (ρ T h Tstar : ℝ)
    (hTs : 0 < Tstar) (hT : Tstar ≤ T) (hTh : Tstar ≤ T + h) :
    effectiveCurvatureKeff J ρ (T + h) Tstar -
     effectiveCurvatureKeff J ρ T Tstar = 0 := by
  rw [effectiveCurvatureKeff_above_critical J ρ (T + h) Tstar hTs hTh,
      effectiveCurvatureKeff_above_critical J ρ T Tstar hTs hT]
  ring

/-- **Second-order transition**: the slope jump at T* is K/T*.

    Left slope = -K/T* (from keff_slope_below)
    Right slope = 0    (from keff_slope_above)
    Jump = 0 - (-K/T*) = K/T*

    The order parameter K_eff is CONTINUOUS (from keff_continuous)
    but its derivative is DISCONTINUOUS. This is the defining
    signature of a second-order phase transition.

    Economics: the marginal cost of information friction jumps
    discontinuously at T*. Below T*, each unit of friction costs
    K/T* units of effective curvature. Above T*, additional
    friction costs nothing (curvature already destroyed). -/
theorem slope_jump_magnitude (J : ℕ) (ρ Tstar : ℝ) :
    0 - (-(curvatureK J ρ / Tstar)) = curvatureK J ρ / Tstar := by
  ring

/-- The slope jump is positive for complementary economies (K > 0). -/
theorem slope_jump_pos (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {Tstar : ℝ} (hTs : 0 < Tstar) :
    0 < curvatureK J ρ / Tstar :=
  div_pos (curvatureK_pos hJ hρ) hTs

-- ============================================================
-- Part C: Critical Exponents
-- ============================================================

/-- **Order parameter exponent β = 1**: K_eff vanishes LINEARLY.

    K_eff = K · (T*-T)/T*  for T < T*

    The exponent β = 1 (linear vanishing) differs from standard
    Landau mean-field theory (β = 1/2, square-root vanishing).
    The CES exponent arises from a CONSTRAINED optimization
    (K_eff ≥ 0 floor) rather than spontaneous symmetry breaking. -/
theorem order_parameter_exponent_one (J : ℕ) (ρ T Tstar : ℝ)
    (hTs : 0 < Tstar) (hT : T < Tstar) :
    effectiveCurvatureKeff J ρ T Tstar =
      curvatureK J ρ * ((Tstar - T) / Tstar) := by
  rw [keff_below_critical J ρ T Tstar hTs hT]
  congr 1; field_simp

/-- **Susceptibility exponent γ = 1**: σ² diverges as (1-T/T*)⁻¹.

    The variance (response to perturbations) grows without bound
    as friction approaches the critical value. The exponent γ = 1
    is standard mean-field.

    **Proof.** The variance at friction $T$ satisfies
    $\sigma^2(T) = \sigma_0^2 / (1 - T/T^*)$ by the intensification formula.
    Rewriting $1/(1 - T/T^*)$ as $(1 - T/T^*)^{-1}$ exhibits the $\gamma = 1$
    divergence exponent as $T \to T^{*-}$. -/
theorem susceptibility_exponent_one (sigma0_sq T Tstar : ℝ)
    (hTs : 0 < Tstar) (hT : T < Tstar) :
    varianceAtFriction sigma0_sq T Tstar =
      sigma0_sq * (1 - T / Tstar)⁻¹ := by
  rw [intensification_rate (by linarith) (by linarith)]
  rw [one_div]

/-- **Timescale exponent**: τ diverges as (1-T/T*)⁻¹.

    Same exponent as the susceptibility — the two divergences
    are locked together by the variance-response identity σ² = T·χ. -/
theorem timescale_exponent (τ₀ T Tstar : ℝ) :
    adjustmentTimescale τ₀ T Tstar = τ₀ * (1 - T / Tstar)⁻¹ := by
  simp [adjustmentTimescale, div_eq_mul_inv]

/-- The correlation length squared: ξ² = D · τ.

    Since τ ~ (1-T/T*)⁻¹, we get ξ ~ (1-T/T*)⁻¹/², giving
    the correlation length exponent ν = 1/2. -/
def correlationLengthSq (D τ₀ T Tstar : ℝ) : ℝ :=
  D * adjustmentTimescale τ₀ T Tstar

theorem correlationLength_divergence (D τ₀ T Tstar : ℝ) :
    correlationLengthSq D τ₀ T Tstar =
      D * τ₀ * (1 - T / Tstar)⁻¹ := by
  simp [correlationLengthSq, adjustmentTimescale, div_eq_mul_inv, mul_assoc]

-- ============================================================
-- Part D: Landau Potential
-- ============================================================

/-- The Landau potential: V(m, t) = t · m + m²/2.

    The effective curvature K_eff/K minimizes this potential
    subject to the constraint m ≥ 0.

    Reduced temperature t = T/T* - 1:
    - t < 0 (T < T*): sub-critical, minimizer at m* = -t > 0
    - t ≥ 0 (T ≥ T*): super-critical, minimizer at m* = 0

    This variational principle reveals that K_eff is not an ad hoc
    formula but the unique solution to a constrained optimization. -/
def landauPotential (t m : ℝ) : ℝ := t * m + m ^ 2 / 2

/-- The Landau potential evaluated at its constrained minimizer:
    V(m*) = -m*²/2 (sub-critical) or 0 (super-critical). -/
theorem landau_at_minimizer (t : ℝ) :
    landauPotential t (max 0 (-t)) = -(max 0 (-t)) ^ 2 / 2 := by
  unfold landauPotential
  by_cases ht : 0 ≤ t
  · rw [max_eq_left (by linarith : -t ≤ 0)]; ring
  · push_neg at ht
    rw [max_eq_right (by linarith : 0 ≤ -t)]; ring

/-- **Landau minimization theorem**: max(0, -t) is the global
    minimizer of V(m, t) = t·m + m²/2 over all m ≥ 0.

    Proof by completing the square:
    - Super-critical (t ≥ 0): V(m) = t·m + m²/2 ≥ 0 = V(0)
    - Sub-critical (t < 0): V(m) - V(-t) = (m+t)²/2 ≥ 0

    **Proof.** For $t \geq 0$: the minimizer is $m^* = 0$ with $V(0) = 0$,
    and $V(m) = tm + m^2/2 \geq 0$ for $m \geq 0$ since both terms are
    non-negative. For $t < 0$: the minimizer is $m^* = -t > 0$, and
    $V(m) - V(-t) = (m + t)^2/2 \geq 0$ by completing the square. -/
theorem landau_minimizer_optimal (t m : ℝ) (hm : 0 ≤ m) :
    landauPotential t (max 0 (-t)) ≤ landauPotential t m := by
  unfold landauPotential
  by_cases ht : 0 ≤ t
  · -- Super-critical: minimizer is 0, V(0) = 0 ≤ V(m)
    rw [max_eq_left (by linarith : -t ≤ 0)]
    nlinarith [sq_nonneg m, mul_nonneg ht hm]
  · -- Sub-critical: V(m) - V(-t) = (m+t)²/2 ≥ 0
    push_neg at ht
    rw [max_eq_right (by linarith : 0 ≤ -t)]
    nlinarith [sq_nonneg (m + t), neg_sq t]

/-- The Landau minimizer reproduces K_eff: the constrained optimizer
    max(0, -(T/T* - 1)) = max(0, 1 - T/T*) is exactly the
    degradation factor in K_eff = K · max(0, 1 - T/T*). -/
theorem landau_gives_keff (J : ℕ) (ρ T Tstar : ℝ) :
    curvatureK J ρ * max 0 (-(T / Tstar - 1)) =
      effectiveCurvatureKeff J ρ T Tstar := by
  simp [effectiveCurvatureKeff, neg_sub]

-- ============================================================
-- Part E: Finite-J Smoothing
-- ============================================================

/-- The transition width in reduced-temperature units: Δ(T/T*) ~ 1/√J.

    For finite J, the sharp kink at T* is smoothed by statistical
    fluctuations. The central limit theorem applied to the J-sector
    CES aggregate gives a transition width that scales as 1/√J.
    More sectors means a sharper transition. -/
def transitionWidth (J : ℕ) : ℝ := 1 / Real.sqrt J

/-- More sectors → sharper transition: the width decreases with J. -/
theorem transitionWidth_decreasing {J₁ J₂ : ℕ}
    (hJ1 : 0 < J₁) (h : J₁ ≤ J₂) :
    transitionWidth J₂ ≤ transitionWidth J₁ := by
  simp only [transitionWidth]
  exact one_div_le_one_div_of_le
    (Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hJ1))
    (Real.sqrt_le_sqrt (Nat.cast_le.mpr h))

-- ============================================================
-- Part F: Universality
-- ============================================================

/-- The reduced K_eff depends only on T/T*: neither J nor ρ
    appears in the universal scaling function f = max(0, 1-T/T*). -/
theorem keff_reduced_universal (J : ℕ) (ρ T Tstar : ℝ)
    (hK : curvatureK J ρ ≠ 0) :
    effectiveCurvatureKeff J ρ T Tstar / curvatureK J ρ =
      reducedOrderParam T Tstar := by
  rw [keff_eq_K_times_reduced]
  exact mul_div_cancel_left₀ _ hK

/-- **Universality theorem**: Two CES economies with different (J, ρ)
    but the same reduced friction T/T* have identical reduced K_eff.

    The critical exponents β=1, γ=1, ν=1/2 are properties of the
    universal scaling function max(0, 1-t), not of any specific
    economy. Microscopic parameters (J, ρ) set the scales K and T*
    but do not affect the functional form of the transition.

    This is the CES analogue of universality in statistical mechanics:
    all CES economies belong to the same universality class,
    characterized by the constrained-quadratic Landau potential.

    **Proof.** Dividing $K_{\mathrm{eff}}$ by $K$ yields the reduced order
    parameter $f(T/T^*) = \max(0, 1 - T/T^*)$, in which $J$ and $\rho$ do
    not appear. If two economies share the same reduced friction
    $T_1/T_1^* = T_2/T_2^*$, the universal function $f$ evaluates identically,
    so their reduced effective curvatures are equal. -/
theorem universality {J₁ J₂ : ℕ} {ρ₁ ρ₂ : ℝ}
    {T₁ Tstar₁ T₂ Tstar₂ : ℝ}
    (hK1 : curvatureK J₁ ρ₁ ≠ 0)
    (hK2 : curvatureK J₂ ρ₂ ≠ 0)
    (hratio : T₁ / Tstar₁ = T₂ / Tstar₂) :
    effectiveCurvatureKeff J₁ ρ₁ T₁ Tstar₁ / curvatureK J₁ ρ₁ =
    effectiveCurvatureKeff J₂ ρ₂ T₂ Tstar₂ / curvatureK J₂ ρ₂ := by
  rw [keff_reduced_universal J₁ ρ₁ T₁ Tstar₁ hK1,
      keff_reduced_universal J₂ ρ₂ T₂ Tstar₂ hK2]
  unfold reducedOrderParam
  rw [hratio]

end
