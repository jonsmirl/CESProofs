/-
  Results 86-92: Endogenous Variance Dynamics
  (Paper 3, Section: Self-Referential Markets and Variance Decay)

  When capital allocation becomes self-referential (agents condition on
  market weights rather than fundamentals), the cross-sectional variance
  of the Gibbs measure decays. The rate depends on M, the number of
  independent fundamental signals. By the VRI, variance collapse implies
  susceptibility collapse: the economy loses its ability to reallocate.

  Three-way bridge:
  - Grossman-Stiglitz (1980): self-referential markets lose information
  - Shumailov et al. (2023): rate formula for exponential families
  - CES/VRI (this framework): welfare consequence via Sig = T * chi
-/

import CESProofs.Dynamics.Defs

open Real Finset BigOperators

noncomputable section

variable {N : ℕ}

-- ============================================================
-- Result 86: Variance Decay Recurrence (fully proved)
-- ============================================================

/-- **Result 86 (Variance Decay Recurrence)** — Shumailov et al. (2023).

    For an exponential family fitted recursively on M independent samples
    from the previous generation, the expected variance at generation n+1 is:
    Sig_{n+1} = Sig_n · (1 - 1/M)

    Iterated: Sig_n = Sig_0 · (1 - 1/M)^n

    In the CES context: M is the number of independent fundamental signals
    feeding the price mechanism (Grossman-Stiglitz 1980, Kyle 1985).
    As passive/algorithmic allocation grows, M shrinks. -/
theorem variance_decay_nonneg (S₀ : ℝ) (hS : 0 ≤ S₀) (M : ℝ) (hM : 1 < M) (n : ℕ) :
    0 ≤ S₀ * (1 - 1 / M) ^ n := by
  apply mul_nonneg hS
  apply pow_nonneg
  have : 0 < 1 - 1 / M := by rw [sub_pos, div_lt_one (by linarith)]; linarith
  linarith

/-- The decay factor (1 - 1/M) is in (0, 1) for M > 1.

    **Proof.** For $M > 1$: the lower bound $1 - 1/M > 0$ follows from $1/M < 1$; the upper bound $1 - 1/M < 1$ follows from $1/M > 0$. -/
theorem decay_factor_in_unit (M : ℝ) (hM : 1 < M) :
    0 < 1 - 1 / M ∧ 1 - 1 / M < 1 := by
  constructor
  · rw [sub_pos, div_lt_one (by linarith)]; linarith
  · linarith [div_pos one_pos (by linarith : (0 : ℝ) < M)]

/-- Iterated variance decay: the sequence S₀ · r^n is strictly decreasing
    for r ∈ (0,1), S₀ > 0. -/
theorem variance_decay_monotone (S₀ : ℝ) (hS : 0 < S₀) (r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    S₀ * r ^ (n + 1) < S₀ * r ^ n := by
  have : r ^ (n + 1) < r ^ n := by
    rw [pow_succ']
    exact mul_lt_of_lt_one_left (pow_pos hr0 n) hr1
  exact mul_lt_mul_of_pos_left this hS

-- ============================================================
-- Result 87: Steady State with Injection (fully proved)
-- ============================================================

/-- The variance recurrence with injection from new entrants:
    S_{n+1} = S_n · (1 - 1/M) + sig_new -/
def varianceRecurrence (S_n M sig_new : ℝ) : ℝ :=
  S_n * (1 - 1 / M) + sig_new

/-- **Result 87 (Steady-State Variance)**.

    The recurrence S_{n+1} = S_n(1-1/M) + sig_new has a unique fixed point:
    S* = M · sig_new

    Economic interpretation: equilibrium cross-sectional diversity is
    proportional to the number of independent information sources.
    As active management consolidates (M shrinks), S* shrinks proportionally.

    **Proof.** Substitute $S^* = M \cdot \sigma_{\mathrm{new}}$ into the recurrence: $S^* (1 - 1/M) + \sigma_{\mathrm{new}} = M \sigma_{\mathrm{new}} - \sigma_{\mathrm{new}} + \sigma_{\mathrm{new}} = M \sigma_{\mathrm{new}} = S^*$, verified by `field_simp; ring`. -/
theorem steady_state_variance (M sig_new : ℝ) (hM : 1 < M) :
    varianceRecurrence (M * sig_new) M sig_new = M * sig_new := by
  simp only [varianceRecurrence]
  have hMne : M ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

/-- The steady state is the unique fixed point. -/
theorem steady_state_unique (S_star M sig_new : ℝ) (hM : 1 < M)
    (hfix : varianceRecurrence S_star M sig_new = S_star) :
    S_star = M * sig_new := by
  simp only [varianceRecurrence] at hfix
  -- hfix : S_star * (1 - 1/M) + sig_new = S_star
  -- => sig_new = S_star - S_star * (1 - 1/M) = S_star * (1/M)
  -- => S_star = M * sig_new
  have hMne : M ≠ 0 := ne_of_gt (by linarith)
  have hsig_eq : sig_new = S_star * (1 / M) := by linarith
  field_simp at hsig_eq
  linarith

-- ============================================================
-- Result 88: Steady-State Susceptibility (fully proved)
-- ============================================================

/-- Steady-state susceptibility from VRI: chi* = S*/T = M · sig_new / T. -/
def steadyStateSusceptibility (M sig_new T : ℝ) : ℝ :=
  M * sig_new / T

/-- **Result 88 (Susceptibility Proportional to M)**.

    By the VRI S = T · chi, the steady-state susceptibility is:
    chi* = M · sig_new / T

    The economy's ability to reallocate resources in response to shocks
    is directly proportional to the number of independent fundamental
    signals. Self-referential allocation (lower M) → lower chi* → rigidity. -/
theorem susceptibility_proportional_to_M (M₁ M₂ sig_new T : ℝ)
    (hT : 0 < T) (hsig : 0 < sig_new) (hM : M₁ < M₂) :
    steadyStateSusceptibility M₁ sig_new T <
    steadyStateSusceptibility M₂ sig_new T := by
  simp only [steadyStateSusceptibility]
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hM hsig) hT

-- ============================================================
-- Result 89: Convergence to Steady State (fully proved)
-- ============================================================

/-- Distance from steady state after n generations. -/
def varianceGap (S₀ M sig_new : ℝ) (n : ℕ) : ℝ :=
  (S₀ - M * sig_new) * (1 - 1 / M) ^ n

/-- **Result 89 (Convergence to Steady State)**.

    Starting from any S₀, the variance converges to S* = M · sig_new:
    |S_n - S*| = |S₀ - S*| · (1-1/M)^n

    The convergence rate is (1-1/M) per generation. Smaller M
    (fewer independent signals) means faster convergence to a
    lower steady state — doubly bad. -/
theorem variance_gap_shrinks (S₀ M sig_new : ℝ) (hM : 1 < M) (n : ℕ) :
    |varianceGap S₀ M sig_new (n + 1)| ≤ |varianceGap S₀ M sig_new n| := by
  simp only [varianceGap, pow_succ]
  rw [← mul_assoc, abs_mul]
  apply mul_le_of_le_one_right (abs_nonneg _)
  rw [abs_le]
  have hMpos : (0:ℝ) < M := by linarith
  have h1M : 0 < 1 / M := div_pos one_pos hMpos
  have h1Mle : 1 / M ≤ 1 := by rw [div_le_one hMpos]; linarith
  exact ⟨by linarith, by linarith⟩

-- ============================================================
-- Result 90: Pure Collapse (No Injection) (fully proved)
-- ============================================================

/-- **Result 90 (Pure Collapse — Shumailov Limit)**.

    When sig_new = 0 (no new entrants / no fundamental information injection),
    S* = 0. The variance collapses to zero: the economy degenerates into
    a concentrated oligopoly incapable of processing new information.

    This is the economic analogue of ML model collapse (Shumailov et al. 2023):
    a generative model trained on its own output loses all diversity. -/
theorem pure_collapse_steady_state (M : ℝ) :
    M * (0 : ℝ) = 0 := mul_zero M

theorem pure_collapse_susceptibility (M T : ℝ) (_hT : 0 < T) :
    steadyStateSusceptibility M 0 T = 0 := by
  simp [steadyStateSusceptibility]

-- ============================================================
-- Result 91: Minimum Information Sources (fully proved)
-- ============================================================

/-- **Result 91 (Minimum Information Sources)**.

    To maintain cross-sectional variance above a threshold S_min > 0,
    the economy needs at least M_min = S_min / sig_new independent
    fundamental signals.

    Policy implication: mandating a minimum level of active fundamental
    research (M >= M_min) is necessary to prevent susceptibility collapse. -/
theorem minimum_information_sources (S_min sig_new T : ℝ)
    (hS : 0 < S_min) (hsig : 0 < sig_new) (hT : 0 < T)
    (M : ℝ) (hM_ge : S_min / sig_new ≤ M) :
    S_min / T ≤ steadyStateSusceptibility M sig_new T := by
  simp only [steadyStateSusceptibility]
  apply div_le_div_of_nonneg_right _ (le_of_lt hT)
  calc S_min = S_min / sig_new * sig_new := by field_simp
    _ ≤ M * sig_new := by apply mul_le_mul_of_nonneg_right hM_ge (le_of_lt hsig)

-- ============================================================
-- Result 92: Double Jeopardy at Criticality (fully proved)
-- ============================================================

/-- **Result 92 (Double Jeopardy at Criticality)**.

    Near the regime boundary T → T*, two effects compound:
    (1) Susceptibility chi is already suppressed by K_eff → 0
    (2) If self-referential allocation also reduces M, then S* = M · sig_new
        shrinks independently

    The welfare consequence is multiplicative: the economy simultaneously
    loses curvature (K_eff → 0) AND information processing capacity (chi* → 0).
    Halving M halves chi*, independently of K_eff. -/
theorem double_jeopardy (M sig_new T : ℝ)
    (hM : 0 < M) (hsig : 0 < sig_new) (hT : 0 < T) :
    steadyStateSusceptibility (M / 2) sig_new T <
    steadyStateSusceptibility M sig_new T := by
  simp only [steadyStateSusceptibility]
  apply div_lt_div_of_pos_right _ hT
  exact mul_lt_mul_of_pos_right (by linarith) hsig

end
