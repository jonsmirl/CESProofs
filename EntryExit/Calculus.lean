/-
  Paper 1c: Formal Calculus on K(J) and V(J)

  The missing mathematical piece that closes Paper 1c's proof gaps.
  Provides HasDerivAt proofs for all key functions, enabling:
  - Full strategic complementarity: V'(J) > 0 (not just K'(J) > 0)
  - Underentry theorem: social FOC vs private FOC comparison
  - Derivative-based monotonicity of V(J)
-/

import CESProofs.EntryExit.Defs
import CESProofs.EntryExit.CurvatureInJ
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: HasDerivAt for curvatureKReal
-- ============================================================

/-- K(J,ρ) = (1-ρ)(J-1)/J has derivative (1-ρ)/J² = marginalK J ρ.
    **Proof.** rewrite K as (1-ρ) - (1-ρ)·J⁻¹ and differentiate. -/
theorem hasDerivAt_curvatureK_real {J ρ : ℝ} (hJ : J ≠ 0) :
    HasDerivAt (fun x => curvatureKReal x ρ) (marginalK J ρ) J := by
  simp only [curvatureKReal, marginalK]
  have heq : (nhds J).EventuallyEq
      (fun x => (1 - ρ) * (x - 1) / x)
      (fun x => (1 - ρ) - (1 - ρ) * x⁻¹) := by
    filter_upwards [IsOpen.mem_nhds isOpen_ne hJ] with x hx; field_simp
  rw [heq.hasDerivAt_iff]
  convert (hasDerivAt_const J (1 - ρ)).sub ((hasDerivAt_inv hJ).const_mul (1 - ρ)) using 1
  field_simp; ring

/-- K'(J) = marginalK is strictly decreasing on (0, ∞).
    Equivalent to K being strictly concave. -/
theorem marginalK_strictAntiOn {ρ : ℝ} (hρ : ρ < 1) :
    StrictAntiOn (fun J => marginalK J ρ) (Set.Ioi 0) :=
  fun _ hJ₁ _ _ hJ₁₂ => pigouvian_subsidy_decreasing (Set.mem_Ioi.mp hJ₁) hρ hJ₁₂

-- ============================================================
-- Section 2: HasDerivAt for perCapitaBenefit
-- ============================================================

/-- B(J) = J^(1/ρ-1)·c has derivative (1/ρ-1)·J^(1/ρ-2)·c.
    Uses HasDerivAt.rpow_const from Mathlib. -/
theorem hasDerivAt_perCapitaBenefit {J ρ c : ℝ} (hJ : 0 < J) :
    HasDerivAt (fun x => perCapitaBenefit x ρ c)
      ((1 / ρ - 1) * J ^ (1 / ρ - 2) * c) J := by
  simp only [perCapitaBenefit]
  have hrpow : HasDerivAt (fun x => x ^ (1 / ρ - 1 : ℝ))
      (1 * (1 / ρ - 1) * J ^ ((1 / ρ - 1) - 1)) J :=
    (hasDerivAt_id J).rpow_const (p := 1 / ρ - 1) (Or.inl (ne_of_gt hJ))
  convert hrpow.mul_const c using 1; ring_nf

/-- B(J) > 0 for J > 0 and c > 0. -/
theorem perCapitaBenefit_pos {J ρ c : ℝ} (hJ : 0 < J) (hc : 0 < c) :
    0 < perCapitaBenefit J ρ c := by
  simp only [perCapitaBenefit]
  exact mul_pos (rpow_pos_of_pos hJ _) hc

-- ============================================================
-- Section 3: The Value Function V(J) = K(J) * B(J)
-- ============================================================

/-- V(J) = K(J,ρ) * B(J,ρ,c): gross benefit of participation
    (before subtracting entry cost). -/
def valueFunction (J ρ c : ℝ) : ℝ :=
  curvatureKReal J ρ * perCapitaBenefit J ρ c

/-- V'(J): derivative by the product rule K'·B + K·B'. -/
def valueFunctionDeriv (J ρ c : ℝ) : ℝ :=
  marginalK J ρ * perCapitaBenefit J ρ c +
  curvatureKReal J ρ * ((1 / ρ - 1) * J ^ (1 / ρ - 2) * c)

/-- HasDerivAt for V(J) = K(J)*B(J) via the product rule. -/
theorem hasDerivAt_valueFunction {J ρ c : ℝ} (hJ : 0 < J) :
    HasDerivAt (fun x => valueFunction x ρ c) (valueFunctionDeriv J ρ c) J := by
  simp only [valueFunction, valueFunctionDeriv]
  exact (hasDerivAt_curvatureK_real (ne_of_gt hJ)).mul (hasDerivAt_perCapitaBenefit hJ)

-- ============================================================
-- Section 4: V'(J) > 0 for Weak Complements (ρ ∈ (0, 1))
-- ============================================================

/-- **Strategic complementarity (full).**
    For ρ ∈ (0,1) and J > 1, V'(J) > 0. Both terms of the
    product rule are positive:
    - K'(J)·B(J) > 0: marginal diversity benefit
    - K(J)·B'(J) > 0: scaling benefit (since 1/ρ > 1 means B is increasing) -/
theorem valueFunctionDeriv_pos {J ρ c : ℝ}
    (hJ : 1 < J) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    0 < valueFunctionDeriv J ρ c := by
  simp only [valueFunctionDeriv]
  have hJpos : 0 < J := by linarith
  apply add_pos
  · exact mul_pos (pigouvian_subsidy_pos hJpos hρ1) (perCapitaBenefit_pos hJpos hc)
  · apply mul_pos (curvatureKReal_pos hJ hρ1)
    apply mul_pos (mul_pos _ (rpow_pos_of_pos hJpos _)) hc
    rw [sub_pos, lt_div_iff₀ hρ0]; linarith

/-- V(J) = 0 at J = 1 (single participant, no diversity benefit). -/
theorem valueFunction_at_one {ρ c : ℝ} :
    valueFunction 1 ρ c = 0 := by
  simp [valueFunction, curvatureKReal_one]

/-- V(J) > V(J₁) whenever J₁ < J₂, both > 1, and ρ ∈ (0,1).
    Direct proof via MVT: V(J₂) - V(J₁) = V'(ξ)(J₂-J₁) > 0. -/
theorem valueFunction_increasing {J₁ J₂ ρ c : ℝ}
    (hJ₁ : 1 < J₁) (hJ₁₂ : J₁ < J₂) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    valueFunction J₁ ρ c < valueFunction J₂ ρ c := by
  have hJ₁pos : 0 < J₁ := by linarith
  have hJ₂pos : 0 < J₂ := by linarith
  -- Apply MVT: there exists ξ ∈ (J₁, J₂) with V(J₂) - V(J₁) = V'(ξ)(J₂ - J₁)
  have hdiff : ∀ x ∈ Set.Ioo J₁ J₂,
      HasDerivAt (fun J => valueFunction J ρ c) (valueFunctionDeriv x ρ c) x :=
    fun x hx => hasDerivAt_valueFunction (by linarith [hx.1])
  have hcont : ContinuousOn (fun J => valueFunction J ρ c) (Set.Icc J₁ J₂) := by
    apply ContinuousOn.mul
    · -- K(J) = (1-ρ)(J-1)/J is continuous for J ≠ 0
      simp only [curvatureKReal]
      apply ContinuousOn.div
      · exact continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
      · exact continuousOn_id
      · intro x hx; exact ne_of_gt (show (0:ℝ) < x by linarith [hx.1])
    · -- B(J) = J^p * c is continuous for J > 0
      simp only [perCapitaBenefit]
      exact (ContinuousOn.rpow continuousOn_id continuousOn_const
        (fun x hx => Or.inl (ne_of_gt (show (0:ℝ) < x by linarith [hx.1])))).mul
        continuousOn_const
  obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope
    (fun J => valueFunction J ρ c) (fun x => valueFunctionDeriv x ρ c)
    (by linarith) hcont hdiff
  -- V'(ξ) > 0 since ξ > 1
  have hξ_pos : 0 < valueFunctionDeriv ξ ρ c :=
    valueFunctionDeriv_pos (by linarith [hξ_mem.1]) hρ0 hρ1 hc
  -- hξ_eq : V'(ξ) = (V(J₂) - V(J₁)) / (J₂ - J₁), so V(J₂) - V(J₁) > 0
  rw [hξ_eq] at hξ_pos
  have hVdiff : 0 < valueFunction J₂ ρ c - valueFunction J₁ ρ c := by
    rwa [div_pos_iff_of_pos_right (by linarith : (0:ℝ) < J₂ - J₁)] at hξ_pos
  linarith

/-- V(J) > 0 for all J > 1 when ρ ∈ (0,1) and c > 0.
    **Proof.** V(1) = 0 and V is increasing on (1, ∞). -/
theorem valueFunction_pos {J ρ c : ℝ}
    (hJ : 1 < J) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    0 < valueFunction J ρ c := by
  -- Find J₀ ∈ (1, J) to apply monotonicity
  -- Actually: pick J₁ = (1+J)/2, show V(J₁) > V_at_1 = 0 and V(J) > V(J₁) > 0
  -- Simpler: use that V(J) > V at some J₀ close to 1 where V > 0
  -- Simplest: direct calculation. V(J) = K(J) * B(J), both positive for J > 1
  apply mul_pos (curvatureKReal_pos hJ hρ1) (perCapitaBenefit_pos (by linarith) hc)

-- ============================================================
-- Section 5: Per-Capita Surplus (Hump Shape)
-- ============================================================

/-- The per-capita curvature surplus:
    π_K(J) = K(J)/J = (1-ρ)(J-1)/J².
    This is the share of the curvature gain accruing to each participant. -/
def perCapitaSurplus (J : ℝ) (ρ : ℝ) : ℝ := (1 - ρ) * (J - 1) / J ^ 2

/-- Alternative form: π_K(J) = (1-ρ) * (J⁻¹ - (J^2)⁻¹). -/
theorem perCapitaSurplus_alt {J : ℝ} (hJ : J ≠ 0) (ρ : ℝ) :
    perCapitaSurplus J ρ = (1 - ρ) * (J⁻¹ - (J ^ 2)⁻¹) := by
  simp only [perCapitaSurplus]
  field_simp

/-- π_K(1) = 0: a single participant gets no curvature benefit. -/
theorem perCapitaSurplus_at_one (ρ : ℝ) :
    perCapitaSurplus 1 ρ = 0 := by
  simp [perCapitaSurplus]

/-- π_K(2) = (1-ρ)/4: the peak value. -/
theorem perCapitaSurplus_at_two (ρ : ℝ) :
    perCapitaSurplus 2 ρ = (1 - ρ) / 4 := by
  simp only [perCapitaSurplus]
  norm_num

/-- π_K(J) > 0 for J > 1 and ρ < 1. -/
theorem perCapitaSurplus_pos {J ρ : ℝ} (hJ : 1 < J) (hρ : ρ < 1) :
    0 < perCapitaSurplus J ρ := by
  simp only [perCapitaSurplus]
  apply div_pos
  · exact mul_pos (by linarith) (by linarith)
  · exact sq_pos_of_pos (by linarith)

/-- The derivative of π_K(J) = (1-ρ)(J-1)/J².
    π_K'(J) = (1-ρ)(2-J)/J³. -/
def perCapitaSurplusDeriv (J : ℝ) (ρ : ℝ) : ℝ := (1 - ρ) * (2 - J) / J ^ 3

/-- HasDerivAt proof for π_K(J).
    Strategy: rewrite π_K(J) = (1-ρ)(1/J - 1/J²) and differentiate term by term. -/
theorem hasDerivAt_perCapitaSurplus {J ρ : ℝ} (hJ : 0 < J) :
    HasDerivAt (fun x => perCapitaSurplus x ρ) (perCapitaSurplusDeriv J ρ) J := by
  have hJne : J ≠ 0 := ne_of_gt hJ
  -- Rewrite π_K as (1-ρ) * ((J-1)/J²) = (1-ρ) * (J⁻¹ - J⁻²)
  -- But J⁻² is not standard. Instead rewrite K(J) = (1-ρ) - (1-ρ)/J
  -- and K(J)/J = ((1-ρ) - (1-ρ)/J)/J = (1-ρ)/J - (1-ρ)/J²
  -- Use EventuallyEq to rewrite the function
  have heq : (nhds J).EventuallyEq
      (fun x => perCapitaSurplus x ρ)
      (fun x => (1 - ρ) * x⁻¹ - (1 - ρ) * (x⁻¹ * x⁻¹)) := by
    filter_upwards [IsOpen.mem_nhds isOpen_ne hJne] with x hx
    simp only [perCapitaSurplus]
    field_simp
  rw [heq.hasDerivAt_iff]
  -- d/dx[x⁻¹] = -x⁻²
  have hinv := hasDerivAt_inv hJne  -- d[x⁻¹] = -(J^2)⁻¹
  -- d/dx[x⁻¹ * x⁻¹] = 2 * x⁻¹ * (-(J^2)⁻¹) by product rule
  have hinv2 := hinv.mul hinv  -- d[x⁻¹ · x⁻¹]
  -- Combine
  have h1 := hinv.const_mul (1 - ρ)
  have h2 := hinv2.const_mul (1 - ρ)
  convert h1.sub h2 using 1
  simp only [perCapitaSurplusDeriv]
  field_simp
  ring

/-- π_K'(J) > 0 for 1 < J < 2: surplus is increasing before the peak. -/
theorem perCapitaSurplusDeriv_pos {J ρ : ℝ} (hJ1 : 1 < J) (hJ2 : J < 2) (hρ : ρ < 1) :
    0 < perCapitaSurplusDeriv J ρ := by
  simp only [perCapitaSurplusDeriv]
  apply div_pos
  · exact mul_pos (by linarith) (by linarith)
  · exact pow_pos (by linarith) 3

/-- π_K'(J) < 0 for J > 2: surplus is decreasing after the peak. -/
theorem perCapitaSurplusDeriv_neg {J ρ : ℝ} (hJ : 2 < J) (hρ : ρ < 1) :
    perCapitaSurplusDeriv J ρ < 0 := by
  simp only [perCapitaSurplusDeriv]
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_pos_of_neg (by linarith) (by linarith)
  · exact pow_pos (by linarith) 3

/-- π_K is increasing on (1, 2): proved via MVT. -/
theorem perCapitaSurplus_increasing_below_peak {J₁ J₂ ρ : ℝ}
    (hJ₁ : 1 < J₁) (hJ₁₂ : J₁ < J₂) (hJ₂ : J₂ ≤ 2) (hρ : ρ < 1) :
    perCapitaSurplus J₁ ρ < perCapitaSurplus J₂ ρ := by
  have hcont : ContinuousOn (fun x => perCapitaSurplus x ρ) (Set.Icc J₁ J₂) := by
    simp only [perCapitaSurplus]
    apply ContinuousOn.div
    · exact continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
    · exact (continuousOn_id.pow 2)
    · intro x hx; exact ne_of_gt (pow_pos (by linarith [hx.1]) 2)
  have hdiff : ∀ x ∈ Set.Ioo J₁ J₂,
      HasDerivAt (fun J => perCapitaSurplus J ρ) (perCapitaSurplusDeriv x ρ) x :=
    fun x hx => hasDerivAt_perCapitaSurplus (by linarith [hx.1])
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope
    (fun J => perCapitaSurplus J ρ) (fun x => perCapitaSurplusDeriv x ρ)
    (by linarith) hcont hdiff
  have hξ_pos : 0 < perCapitaSurplusDeriv ξ ρ :=
    perCapitaSurplusDeriv_pos (by linarith [hξ.1]) (by linarith [hξ.2]) hρ
  rw [hslope] at hξ_pos
  linarith [div_pos_iff_of_pos_right (show (0:ℝ) < J₂ - J₁ by linarith) |>.mp hξ_pos]

/-- π_K is decreasing on (2, ∞): proved via MVT. -/
theorem perCapitaSurplus_decreasing_above_peak {J₁ J₂ ρ : ℝ}
    (hJ₁ : 2 ≤ J₁) (hJ₁₂ : J₁ < J₂) (hρ : ρ < 1) :
    perCapitaSurplus J₂ ρ < perCapitaSurplus J₁ ρ := by
  have hcont : ContinuousOn (fun x => perCapitaSurplus x ρ) (Set.Icc J₁ J₂) := by
    simp only [perCapitaSurplus]
    apply ContinuousOn.div
    · exact continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
    · exact (continuousOn_id.pow 2)
    · intro x hx; exact ne_of_gt (pow_pos (by linarith [hx.1]) 2)
  have hdiff : ∀ x ∈ Set.Ioo J₁ J₂,
      HasDerivAt (fun J => perCapitaSurplus J ρ) (perCapitaSurplusDeriv x ρ) x :=
    fun x hx => hasDerivAt_perCapitaSurplus (by linarith [hx.1])
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope
    (fun J => perCapitaSurplus J ρ) (fun x => perCapitaSurplusDeriv x ρ)
    (by linarith) hcont hdiff
  have hξ_neg : perCapitaSurplusDeriv ξ ρ < 0 :=
    perCapitaSurplusDeriv_neg (by linarith [hξ.1]) hρ
  rw [hslope] at hξ_neg
  have hd : (0:ℝ) < J₂ - J₁ := by linarith
  have hVdiff : perCapitaSurplus J₂ ρ - perCapitaSurplus J₁ ρ < 0 := by
    by_contra h_not
    push_neg at h_not
    have : 0 ≤ (perCapitaSurplus J₂ ρ - perCapitaSurplus J₁ ρ) / (J₂ - J₁) :=
      div_nonneg h_not (le_of_lt hd)
    linarith
  linarith

/-- π_K(J) ≤ π_K(2) = (1-ρ)/4 for all J > 1: the peak bound.

    **Proof.** The per-capita surplus $\pi_K(J) = (1-\rho)(J-1)/J^2$ achieves its unique maximum at $J=2$ where $\pi_K(2) = (1-\rho)/4$. For $J < 2$, the function is increasing (positive derivative); for $J > 2$, it is decreasing (negative derivative). Both cases are handled by the monotonicity lemmas applied with $J=2$ as the reference point. -/
theorem perCapitaSurplus_le_peak {J ρ : ℝ} (hJ : 1 < J) (hρ : ρ < 1) :
    perCapitaSurplus J ρ ≤ (1 - ρ) / 4 := by
  rw [← perCapitaSurplus_at_two ρ]
  by_cases h2 : J ≤ 2
  · rcases (lt_or_eq_of_le h2) with hlt | heq
    · exact le_of_lt (perCapitaSurplus_increasing_below_peak hJ hlt le_rfl hρ)
    · rw [heq]
  · push_neg at h2
    exact le_of_lt (perCapitaSurplus_decreasing_above_peak le_rfl h2 hρ)

/-- Relating per-capita surplus to K and J:
    π_K(J) = curvatureKReal(J,ρ) / J. -/
theorem perCapitaSurplus_eq_K_div_J {J ρ : ℝ} (_hJ : J ≠ 0) :
    perCapitaSurplus J ρ = curvatureKReal J ρ / J := by
  simp only [perCapitaSurplus, curvatureKReal]
  have hJ2 : J ^ 2 = J * J := sq J
  rw [hJ2, div_div]

-- ============================================================
-- Section 6: Social Welfare and Underentry
-- ============================================================

/-- Social welfare: W(J) = J · (V(J) - κ).
    The social planner maximizes total surplus across J participants. -/
def socialWelfare (J ρ c κ : ℝ) : ℝ :=
  J * (valueFunction J ρ c - κ)

/-- The marginal external benefit J · V'(J) > 0 for ρ ∈ (0,1), J > 1.
    This is the positive externality that private entrants ignore. -/
theorem marginal_externality_pos {J ρ c : ℝ}
    (hJ : 1 < J) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    0 < J * valueFunctionDeriv J ρ c :=
  mul_pos (by linarith) (valueFunctionDeriv_pos hJ hρ0 hρ1 hc)

/-- **Underentry theorem (proved).**
    At any J where a private entrant breaks even (V(J) = κ),
    the social marginal benefit V(J) + J·V'(J) strictly exceeds κ.
    Therefore the social optimum has more entry than the private equilibrium. -/
theorem underentry_at_private_optimum {J ρ c κ : ℝ}
    (hJ : 1 < J) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c)
    (hFOC : valueFunction J ρ c = κ) :
    κ < valueFunction J ρ c + J * valueFunctionDeriv J ρ c := by
  rw [hFOC]
  linarith [marginal_externality_pos hJ hρ0 hρ1 hc]

/-- The external benefit J·V'(J) decomposes into:
    - Curvature externality: J·K'(J)·B(J) (diversity benefit to incumbents)
    - Scaling externality: J·K(J)·B'(J) (network growth benefit) -/
theorem pigouvian_subsidy_decomposition {J ρ c : ℝ} :
    J * valueFunctionDeriv J ρ c =
    J * marginalK J ρ * perCapitaBenefit J ρ c +
    J * curvatureKReal J ρ * ((1 / ρ - 1) * J ^ (1 / ρ - 2) * c) := by
  simp only [valueFunctionDeriv]; ring

-- ============================================================
-- Section 6: Pareto Ranking (Strengthened)
-- ============================================================

/-- **Pareto ranking (strengthened).**
    For J_high > J_low > 1, the value function satisfies
    V(J_high) > V(J_low) > 0. Every participant is strictly
    better off at the higher equilibrium. -/
theorem pareto_ranking_strengthened {J_high J_low ρ c : ℝ}
    (hJl : 1 < J_low) (hJh : J_low < J_high)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    valueFunction J_low ρ c < valueFunction J_high ρ c :=
  valueFunction_increasing hJl hJh hρ0 hρ1 hc

/-- The welfare gap between equilibria is at least
    [V(J_high) - V(J_low)] * J_low, since J_low participants
    each gain V(J_high) - V(J_low) > 0. -/
theorem welfare_gap_lower_bound {J_high J_low ρ c : ℝ}
    (hJl : 1 < J_low) (hJh : J_low < J_high)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hc : 0 < c) :
    0 < (valueFunction J_high ρ c - valueFunction J_low ρ c) * J_low := by
  apply mul_pos
  · linarith [pareto_ranking_strengthened hJl hJh hρ0 hρ1 hc]
  · linarith

end
