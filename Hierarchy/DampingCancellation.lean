/-
  Proposition 6, Theorem 9, Corollaries 1-2 and 4:
  Damping Cancellation and the Upstream Reform Principle
  (Paper 4, Section 12)

  The headline result: increasing depreciation (regulation) at level n
  speeds convergence but lowers equilibrium output, and these effects
  exactly cancel in the welfare loss. Welfare improvement requires
  upstream reform (reducing sigma at level n-1 or increasing beta at level n).
-/

import CESProofs.Hierarchy.Defs
import CESProofs.Hierarchy.WelfareDecomposition

open Real Finset BigOperators

noncomputable section

variable {N : ℕ}

-- ============================================================
-- Proposition 6(i): Convergence Speed Increasing in sigma_n
-- ============================================================

/-- **Proposition 6(i) (Convergence Speed)** -- Section 12 of Paper 4.

    Convergence speed = sigma_n / eps_n is strictly increasing in sigma_n.
    Higher depreciation means faster adjustment toward equilibrium. -/
theorem convergenceSpeed_increasing_sigma {sigma1 sigma2 eps : ℝ}
    (heps : 0 < eps) (h12 : sigma1 < sigma2) :
    sigma1 / eps < sigma2 / eps :=
  div_lt_div_of_pos_right h12 heps

-- ============================================================
-- Proposition 6(ii): Equilibrium Output Decreasing in sigma_n
-- ============================================================

/-- **Proposition 6(ii) (Equilibrium Output)** -- Section 12 of Paper 4.

    Equilibrium output Fbar_n = phi(Fbar_{n-1}) / sigma_n is strictly
    decreasing in sigma_n. Higher depreciation means lower output. -/
theorem equilibriumOutput_decreasing_sigma {sigma1 sigma2 phi_val : ℝ}
    (hphi : 0 < phi_val) (hs1 : 0 < sigma1) (_hs2 : 0 < sigma2)
    (h12 : sigma1 < sigma2) :
    phi_val / sigma2 < phi_val / sigma1 :=
  div_lt_div_of_pos_left hphi hs1 h12

-- ============================================================
-- Proposition 6(iii): Welfare Loss Independent of sigma_n
-- ============================================================

-- **Proposition 6(iii) (Damping Cancellation)** -- Section 12 of Paper 4.
--
-- The key algebraic identity: c * (phi / sigma) * sigma = c * phi.
-- The sigma in Fbar = phi/sigma cancels with the sigma weight.
-- Welfare loss depends only on upstream parameters (sigma_{n-1}, beta_n).

/-- The damping cancellation identity: sigma cancels in the product
    c * Fbar * sigma where Fbar = phi / sigma. -/
theorem damping_cancellation_algebraic {phi_prev sigma_n c_n : ℝ}
    (hsigma : sigma_n ≠ 0) :
    c_n * (phi_prev / sigma_n) * sigma_n = c_n * phi_prev := by
  field_simp

/-- The welfare contribution is independent of own-level sigma.
    If the upstream input phi is the same, changing sigma does not
    change the welfare contribution. -/
theorem welfare_independent_of_own_sigma {phi_prev sigma1 sigma2 c delta : ℝ}
    (hs1 : sigma1 ≠ 0) (hs2 : sigma2 ≠ 0) :
    c * (phi_prev / sigma1) * sigma1 * delta ^ 2 =
    c * (phi_prev / sigma2) * sigma2 * delta ^ 2 := by
  have h1 : c * (phi_prev / sigma1) * sigma1 = c * phi_prev := by field_simp
  have h2 : c * (phi_prev / sigma2) * sigma2 = c * phi_prev := by field_simp
  rw [h1, h2]

-- ============================================================
-- Theorem 9: Upstream Reform Principle
-- ============================================================

-- **Theorem 9 (Upstream Reform Principle)** -- Section 12 of Paper 4.
--
-- To improve welfare at level n, reform upstream:
-- (a) Increase beta_n (improve gain elasticity) to reduce welfare loss
-- (b) Decrease sigma_{n-1} (reduce upstream depreciation) to reduce welfare loss
--
-- These are the only parameters that affect welfare after damping cancellation.

/-- Welfare loss is decreasing in gain elasticity (for nonzero deviation).

    **Proof.** The welfare contribution $V_n = \sigma_{n-1}\delta^2/\beta_n$ is inversely proportional to $\beta_n$ (with the numerator $\sigma_{n-1}\delta^2 > 0$ fixed). Since $\beta_1 < \beta_2$ and $f(x) = c/x$ is decreasing for $c > 0$ and $x > 0$, we get $V(\beta_2) < V(\beta_1)$. -/
theorem upstream_reform_beta {sigma_prev delta beta1 beta2 : ℝ}
    (hs : 0 < sigma_prev) (hdelta : delta ≠ 0)
    (hb1 : 0 < beta1) (_hb2 : 0 < beta2) (h12 : beta1 < beta2) :
    welfareContribution sigma_prev delta beta2 <
    welfareContribution sigma_prev delta beta1 := by
  simp only [welfareContribution]
  apply div_lt_div_of_pos_left _ hb1 h12
  exact mul_pos hs (sq_pos_of_ne_zero hdelta)

/-- Welfare loss is increasing in upstream depreciation (for nonzero deviation). -/
theorem upstream_reform_sigma_prev {sigma_prev1 sigma_prev2 delta beta : ℝ}
    (hdelta : delta ≠ 0) (hb : 0 < beta) (h12 : sigma_prev1 < sigma_prev2) :
    welfareContribution sigma_prev1 delta beta <
    welfareContribution sigma_prev2 delta beta := by
  simp only [welfareContribution]
  apply div_lt_div_of_pos_right _ hb
  exact mul_lt_mul_of_pos_right h12 (sq_pos_of_ne_zero hdelta)

-- ============================================================
-- Corollary 1: Zero Welfare Effect of Fastest-Layer Regulation
-- ============================================================

/-- **Corollary 1** -- Section 12 of Paper 4.

    The fastest layer can be regulated without welfare cost.
    Financial regulation has zero net welfare effect. -/
theorem fastest_layer_regulation {phi_prev sigma_fast1 sigma_fast2 c : ℝ}
    (hs1 : sigma_fast1 ≠ 0) (hs2 : sigma_fast2 ≠ 0) :
    c * (phi_prev / sigma_fast1) * sigma_fast1 =
    c * (phi_prev / sigma_fast2) * sigma_fast2 := by
  have h1 : c * (phi_prev / sigma_fast1) * sigma_fast1 = c * phi_prev := by field_simp
  have h2 : c * (phi_prev / sigma_fast2) * sigma_fast2 = c * phi_prev := by field_simp
  rw [h1, h2]

-- ============================================================
-- Corollary 2: Welfare Ordering
-- ============================================================

/-- **Corollary 2 (Welfare Ordering)** -- Section 12 of Paper 4.

    If gain elasticity increases with level (beta_1 < beta_2 < ... < beta_N),
    then welfare weights decrease: W_11 > W_22 > ... > W_NN.
    The slowest level has the largest welfare weight. -/
theorem welfare_ordering {W1 W2 P sigma beta1 beta2 : ℝ}
    (hP : 0 < P) (hs : 0 < sigma) (hb1 : 0 < beta1) (_hb2 : 0 < beta2)
    (hbeta : beta1 < beta2)
    (hW1 : W1 = P / (sigma * beta1))
    (hW2 : W2 = P / (sigma * beta2)) :
    W2 < W1 := by
  rw [hW1, hW2]
  exact div_lt_div_of_pos_left hP (mul_pos hs hb1) (mul_lt_mul_of_pos_left hbeta hs)

-- ============================================================
-- Corollary 4: Rigidity Ordering
-- ============================================================

/-- **Corollary 4 (Rigidity Ordering)** -- Section 12 of Paper 4.

    Level 1 is both the slowest to adjust AND the most welfare-consequential.
    If eps_1 > eps_2 and W_1 > W_2 (both positive), then eps_1 * W_1 > eps_2 * W_2. -/
theorem rigidity_ordering {eps1 eps2 W1 W2 : ℝ}
    (heps : eps2 < eps1) (hW : W2 < W1)
    (_heps2 : 0 < eps2) (hW2 : 0 < W2) :
    eps2 * W2 < eps1 * W1 :=
  calc eps2 * W2 < eps1 * W2 := mul_lt_mul_of_pos_right heps hW2
    _ ≤ eps1 * W1 := mul_le_mul_of_nonneg_left (le_of_lt hW) (by linarith)

-- ============================================================
-- Regulatory Cascade: Two-Stage Transmission Preserves Long-Run Zero
-- ============================================================

-- **Remark (Regulatory Cascade)** -- Paper 4, Remark (regulatory cascade).
--
-- Institutional regulations (activity restrictions, supervisory power)
-- pass through a two-stage announcement→implementation cascade:
--   Stage 1: ż = -μ(z - s),  Stage 2: ε ẋ ≈ -λ(x - z_eq)
-- The IRF for unit impulse s(0)=1 is:
--   β(h) = (λ/(λ-μ)) · [exp(-μh) - exp(-λh)]
-- Key property: β(h) → 0 as h → ∞, for any μ,λ > 0.
-- Damping cancellation survives: long-run effect is zero regardless of transient shape.

/-- **Cascade long-run zero** (Paper 4, Remark: Regulatory Transmission Cascade).

    The biexponential IRF of the two-stage regulatory cascade converges to zero.
    For any announcement speed μ > 0 and adjustment speed λ > 0, the long-run
    effect is zero: the cascade changes the transient path but not the long-run outcome.

    This ensures the damping cancellation theorem's key welfare implication holds
    for both direct stock regulations (first-order IRF, Model A) and institutional
    regulations (hump-shaped IRF, Model B/C). -/
theorem cascade_long_run_zero {lam mu : ℝ} (hlam : 0 < lam) (hmu : 0 < mu) :
    Filter.Tendsto (fun h : ℝ => Real.exp (-mu * h) - Real.exp (-lam * h))
                   Filter.atTop (nhds 0) := by
  have key : ∀ c : ℝ, 0 < c →
      Filter.Tendsto (fun h : ℝ => Real.exp (-c * h)) Filter.atTop (nhds 0) := by
    intro c hc
    have h1 := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id)
    convert h1 using 1
    funext h; simp [neg_mul, id]
  have hsub := (key mu hmu).sub (key lam hlam)
  simp only [sub_self] at hsub
  exact hsub

/-- **Hump long-run zero** — the hump-shaped IRF beta(h) = a*h*exp(-lam*h)
    (limit case of cascade when mu tends to lam) also converges to zero.

    This is the equal-speed limit of the biexponential cascade, confirming
    that Model B (hump) also satisfies the damping cancellation prediction
    of zero long-run effect. -/
theorem hump_long_run_zero {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    Filter.Tendsto (fun h : ℝ => a * h * Real.exp (-lam * h))
                   Filter.atTop (nhds 0) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · -- Normalize: exp(-lam*h) = exp(-(lam*h)) for compatibility with composition
    have hrw : (fun h : ℝ => a * h * Real.exp (-lam * h)) =
               (fun h => a * h * Real.exp (-(lam * h))) := by
      funext h; congr 1; ring
    rw [hrw]
    -- Build: lam*h * exp(-(lam*h)) → 0 via h ↦ lam*h substitution
    have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (Filter.Tendsto.const_mul_atTop hlam Filter.tendsto_id)
    have h2 : Filter.Tendsto (fun h : ℝ => lam * h * Real.exp (-(lam * h)))
        Filter.atTop (nhds 0) := by
      convert h1 using 1; funext h; simp [Function.comp, id]
    -- Scale: a * h * exp(-(lam*h)) = (a/lam) * (lam * h * exp(-(lam*h)))
    have h3 := h2.const_mul (a / lam)
    simp only [mul_zero] at h3
    convert h3 using 1
    funext h
    field_simp [hlam.ne']

end
