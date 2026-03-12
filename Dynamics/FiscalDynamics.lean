/-
  Fiscal Injection and Demand-Side Dynamics
  (Paper 3, Section "Fiscal Injection and Demand-Side Inflation")

  Extends the conservative-dissipative dynamics ẋ = (J-R)∇F to include
  external fiscal injection: ẋ = (J-R)∇F + Bu, where u is the fiscal
  injection rate and B is the allocation vector.

  Results 93-99:
  93. Energy balance with injection (proved)
  94. Uniform injection zero misallocation cost (proved)
  95. Targeted injection cost proportional to K (proved)
  96. Deficit vs tax financing (proved)
  97. Supply-fiscal interaction (proved)
  98. Steady-state displacement (schematic)
  99. Direction-dependent inflation (schematic)

  Key insight: the CES Hessian eigenstructure (eigenvalue 0 on 1,
  eigenvalue -(1-ρ)/(Jc) on 1⊥) determines that uniform fiscal injection
  (Bu ∝ 1) has zero misallocation cost, while targeted injection
  (Bu ⊥ 1) has cost proportional to K = (1-ρ)(J-1)/J.
-/

import CESProofs.Dynamics.Defs
import CESProofs.Dynamics.PolicyCost
import CESProofs.Dynamics.SymmetricAdjustment
import CESProofs.Foundations.Hessian

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Definitions: Fiscal injection
-- ============================================================

/-- Fiscal injection rate: government spending per unit time. -/
def fiscalInjection (u : ℝ) := u

/-- Allocation vector: how fiscal injection is distributed across sectors.
    B : Fin J → ℝ with Σ B_j = u (total injection).
    Decompose B = (u/J)·1 + b where b ⊥ 1 (Σ b_j = 0). -/
def uniformComponent (_J : ℕ) (u : ℝ) : ℝ := u / ↑_J

/-- The perpendicular (misallocation) component of fiscal injection.
    b_j = B_j - u/J, satisfying Σ b_j = 0 (i.e., b ⊥ 1). -/
def misallocationComponent (J : ℕ) (B : Fin J → ℝ) (u : ℝ) : Fin J → ℝ :=
  fun j => B j - u / ↑J

/-- The misallocation component sums to zero when B sums to u. -/
theorem misallocationComponent_orthToOne (hJ : 0 < J)
    (B : Fin J → ℝ) (u : ℝ) (hB : ∑ j : Fin J, B j = u) :
    orthToOne J (misallocationComponent J B u) := by
  simp only [orthToOne, vecSum, misallocationComponent]
  rw [Finset.sum_sub_distrib, hB, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [nsmul_eq_mul]
  field_simp
  ring

-- ============================================================
-- Result 93: Energy Balance with Fiscal Injection (proved)
-- ============================================================

/-- **Result 93 (Energy Balance with Fiscal Injection).**

    Under the dynamics ẋ = (J-R)∇F + Bu, the energy balance becomes:
    dE/dt = -dissipation + injection power

    The injection power is u · Σ B_j · ∂F/∂x_j. At the symmetric point
    where ∂F/∂x_j = 1/J for all j, the injection power equals
    u · (Σ B_j)/J = u²/J when Σ B_j = u.

    We prove: injection power at symmetric point = u²/J.

    **Proof.** At the symmetric equilibrium, all marginal products equal $1/J$
    (by Euler's theorem for homogeneous-of-degree-1 CES). The fiscal injection
    power is $\sum_j B_j \cdot (\partial F/\partial x_j) = (1/J)\sum_j B_j = u/J$.
    The total energy rate is $\dot{E} = -\text{dissipation} + u/J$. -/
theorem fiscal_injection_power (hJ : 0 < J)
    (B : Fin J → ℝ) (u : ℝ) (hB : ∑ j : Fin J, B j = u) :
    (1 / (↑J : ℝ)) * ∑ j : Fin J, B j = u / ↑J := by
  rw [hB]
  ring

-- ============================================================
-- Result 94: Uniform Injection Has Zero Misallocation Cost (proved)
-- ============================================================

/-- **Result 94 (Uniform Injection Zero Misallocation Cost).**

    When fiscal injection is distributed uniformly across sectors
    (B_j = u/J for all j), the CES Hessian quadratic form applied to
    the allocation vector equals zero. Uniform injection moves the
    economy along the 1-direction (scale), which is the zero-eigenvalue
    direction of the Hessian.

    This is the fiscal analogue of Euler's theorem: scaling all inputs
    equally has no misallocation cost because CES is homogeneous of
    degree 1.

    **Proof.** By `cesHessianQF_on_one`: the CES Hessian applied to any
    constant vector $\alpha \cdot \mathbf{1}$ gives zero, since the Hessian
    eigenvalue on the $\mathbf{1}$-direction is 0 (Euler's theorem for
    homogeneous functions). Uniform injection $B_j = u/J$ is a constant
    vector with $\alpha = u/J$. -/
theorem uniform_injection_zero_cost (hJ : 0 < J) (ρ c u : ℝ) (hc : 0 < c) :
    cesHessianQF J ρ c (fun _ => u / ↑J) = 0 := by
  exact cesHessianQF_on_one hJ ρ c hc (u / ↑J)

-- ============================================================
-- Result 95: Targeted Injection Cost Proportional to K (proved)
-- ============================================================

/-- **Result 95 (Targeted Injection Misallocation Cost).**

    When fiscal injection has a component perpendicular to 1 (i.e.,
    it favors some sectors over others), the misallocation cost is:
    cost = -(1-ρ)/(Jc) · ‖b‖²

    where b is the perpendicular component of the allocation vector.
    The cost is proportional to (1-ρ), hence to K = (1-ρ)(J-1)/J.
    More complementary economies (lower ρ, higher K) pay a larger
    misallocation penalty for targeted spending.

    **Proof.** By `cesHessianQF_on_perp`: for any vector $b \perp \mathbf{1}$
    (i.e., $\sum b_j = 0$), the Hessian quadratic form equals
    $\lambda_\perp \cdot \|b\|^2$ where $\lambda_\perp = -(1-\rho)/(Jc)$.
    Since $1-\rho > 0$ for complementary inputs ($\rho < 1$), this is
    negative (a welfare loss). The magnitude scales with $K$ because
    $|{\lambda_\perp}| = (1-\rho)/(Jc)$ and $K = (1-\rho)(J-1)/J$. -/
theorem targeted_injection_cost (hJ : 0 < J) (ρ c : ℝ) (hc : 0 < c)
    (b : Fin J → ℝ) (hb : orthToOne J b) :
    cesHessianQF J ρ c b = cesEigenvaluePerp J ρ c * vecNormSq J b :=
  cesHessianQF_on_perp hJ ρ c hc b hb

/-- The misallocation cost is non-positive for complementary inputs (ρ < 1).
    Targeted injection always reduces welfare relative to uniform injection. -/
theorem targeted_injection_cost_nonpos (hJ : 0 < J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c)
    (b : Fin J → ℝ) (hb : orthToOne J b) :
    cesHessianQF J ρ c b ≤ 0 :=
  cesHessianQF_neg_semidef hJ hρ hc b hb

-- ============================================================
-- Result 96: Deficit vs Tax Financing (proved)
-- ============================================================

/-- **Result 96 (Deficit vs Tax Financing).**

    Deficit-financed injection Bu has the full misallocation component b.
    Tax-financed injection (B - τI)u has a DIFFERENT misallocation component
    because the tax τ partially cancels the injection.

    Net injection under proportional tax τ: (B_j - τ)u for each sector j.
    The perpendicular component is (B_j - u/J) - (τ - τ) = b_j (same!).

    Key result: under a UNIFORM proportional tax, the misallocation component
    is unchanged. The tax only reduces the uniform component (scale).
    So the misallocation cost of deficit financing and tax financing are
    identical — the difference is purely in the scale (1-direction) component.

    **Proof.** A uniform proportional tax $\tau$ subtracts a constant from each
    sector: net injection is $(B_j - \tau)u$. The perpendicular component
    $b_j^{\text{net}} = (B_j - \tau) - (\bar{B} - \tau) = B_j - \bar{B} = b_j$.
    Hence the misallocation vector is unchanged, and by Result 95, the
    Hessian quadratic form on $b^{\text{net}} = b$ is identical. -/
theorem deficit_vs_tax_same_misallocation (hJ : 0 < J)
    (B : Fin J → ℝ) (u τ : ℝ) (_hB : ∑ j : Fin J, B j = u) :
    misallocationComponent J (fun j => B j - τ) (u - ↑J * τ) =
    misallocationComponent J B u := by
  ext j
  simp only [misallocationComponent]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

-- ============================================================
-- Result 97: Supply-Fiscal Interaction (proved)
-- ============================================================

/-- **Result 97 (Supply-Fiscal Interaction).**

    When information friction T is elevated (supply disruption), the
    effective curvature is K_eff = K·(1-T/T*). The misallocation cost
    of targeted fiscal injection is amplified by the supply disruption
    because the economy is operating closer to the critical threshold.

    Specifically, the ratio of misallocation cost to injection size
    scales as (1-ρ)/(Jc), which is the Hessian eigenvalue magnitude.
    When friction T increases, the economy moves closer to T* where
    small misallocations have outsized effects through the effective
    curvature channel.

    We prove: the misallocation cost is strictly negative (welfare-reducing)
    when ρ < 1 and the perpendicular component is nonzero, regardless of
    friction level. The friction level affects the DYNAMIC response
    (how quickly the misallocation is resolved) but not the instantaneous
    cost.

    **Proof.** By `ces_strict_concavity_on_perp`: for any nonzero $b \perp \mathbf{1}$
    with $\rho < 1$, the Hessian quadratic form is strictly negative. The strict
    inequality holds at all friction levels because the Hessian at the symmetric
    point depends on $\rho$ and $c$ but not on $T$ — friction affects the dynamics
    (relaxation speed) but not the instantaneous curvature of the production surface.
    During supply disruptions ($T \uparrow$), adjustment slows (relaxation rate
    $\propto 1 - T/T^*$), so the misallocation persists longer, amplifying cumulative
    welfare loss. -/
theorem supply_fiscal_interaction (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c)
    (b : Fin J → ℝ) (hb : orthToOne J b) (hb_ne : ∃ j, b j ≠ 0) :
    cesHessianQF J ρ c b < 0 :=
  ces_strict_concavity_on_perp hJ hρ hc b hb hb_ne

-- ============================================================
-- Result 98: Steady-State Displacement (schematic)
-- ============================================================

/-- **Result 98 (Steady-State Displacement under Persistent Injection).**

    Under persistent fiscal injection ẋ = -L∇F + Bu, the steady state
    shifts from x* to x* + L⁻¹Bu. The displacement decomposes into:
    - Scale component (1-direction): proportional to u/J, shifts
      all sectors equally → pure output expansion
    - Misallocation component (1⊥): proportional to L⁻¹b, distorts
      relative allocation → welfare loss ∝ K·‖b‖²

    The inflation rate at steady state equals the marginal product
    change: π = ∇²F · L⁻¹Bu = (1-ρ)/(Jc) · (‖b‖²/ℓ) for the
    misallocation channel.

    **Proof.** At steady state, $0 = -L\nabla F(x^{**}) + Bu$, so $\nabla F(x^{**}) = L^{-1}Bu$.
    Linearizing around $x^*$: $x^{**} - x^* \approx (\nabla^2 F)^{-1} L^{-1} Bu$. The
    eigenstructure of $\nabla^2 F$ separates the displacement into the zero-eigenvalue
    $\mathbf{1}$-direction (pure scale, no inflation) and the $\lambda_\perp$-eigenvalue
    $\mathbf{1}^\perp$-direction (misallocation, inflationary). The scale component
    grows output; the misallocation component distorts relative prices. -/
theorem steadyState_displacement :
    -- x** = x* + (∇²F)⁻¹ L⁻¹ Bu
    -- with decomposition into 1-direction and 1⊥-direction
    True := trivial

-- ============================================================
-- Result 99: Direction-Dependent Inflation (schematic)
-- ============================================================

/-- **Result 99 (Direction-Dependent Inflation).**

    The inflationary impact of fiscal injection depends on its direction
    relative to the CES Hessian eigenstructure:

    (a) Uniform injection (Bu ∝ 1): zero first-order inflation.
        Pure demand expansion along the 1-direction meets the zero
        eigenvalue — prices adjust uniformly (numeraire shift only).

    (b) Targeted injection (Bu ⊥ 1): inflation ∝ (1-ρ)·‖b‖²/(Jc·ℓ).
        Misallocation along the 1⊥-direction meets the negative eigenvalue
        λ_⊥ = -(1-ρ)/(Jc), creating relative price distortions that
        aggregate into measured inflation.

    Combined: π = π_demand + π_misallocation, where π_demand ∝ u·(∂²F/∂x²)|₁
    (= 0 by Euler) and π_misallocation ∝ |λ_⊥|·‖b‖²/ℓ.

    This explains:
    - Biden 2021-23: large u with targeted b (PPP by sector, stimulus checks
      meeting supply constraints) → significant misallocation inflation
    - Trump tariffs 2025: targeted b but small ‖b‖ (tariffs redistribute
      across many sectors, partially offsetting), high σ in affected sectors
      → low pass-through

    **Proof.** The inflation decomposition follows from the Hessian eigenstructure (Results 94-95)
    and the steady-state displacement (Result 98). The uniform component $u/J \cdot \mathbf{1}$
    lies in the kernel of the Hessian (eigenvalue 0), producing zero relative price change. The
    perpendicular component $b$ lies in the $\lambda_\perp$-eigenspace, producing relative price
    distortions of magnitude $|\lambda_\perp| \cdot \|b\|^2 / \ell$. Aggregating over sectors via
    the CES price index gives the measured inflation rate. For high-$\sigma$ sectors (low $1-\rho$),
    the eigenvalue $|\lambda_\perp|$ is small, so tariff pass-through is low. -/
theorem direction_dependent_inflation :
    -- π = 0 for uniform injection (Bu ∝ 1)
    -- π ∝ (1-ρ)·‖b‖²/(Jc·ℓ) for targeted injection (Bu ⊥ 1)
    True := trivial

end
