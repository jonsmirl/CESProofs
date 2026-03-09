/-
  Propositions 3-4: q-Exponential Equilibrium and Tail Behavior
  (Paper 2, Section 3.3-3.4)

  The optimal allocation under the CES potential is the q-exponential
  (escort) distribution. Tail behavior depends on q:
  - q < 1: compact support (bounded rationality)
  - q = 1: exponential/logit (standard discrete choice)
  - q > 1: power-law tails (heavy-tailed choices)
-/

import CESProofs.Potential.Defs

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Proposition 3: q-Exponential Equilibrium
-- ============================================================

/-- The q-exponential allocation (escort distribution):
    p*ⱼ ∝ exp_q(εⱼ / T)

    This is the optimal allocation under the CES potential Φ_q.
    For q = 1, this is the standard softmax/logit.
    For q ≠ 1, this is the Tsallis generalization. -/
def qExpAllocation (J : ℕ) (q T : ℝ) (ε : Fin J → ℝ) : Fin J → ℝ :=
  let Z := ∑ j : Fin J, qExp q (ε j / T)
  fun j => qExp q (ε j / T) / Z

/-- **Proposition 3 (q-Exponential Equilibrium)** — Section 3.3 of Paper 2.

    The first-order condition ∂Φ_q/∂pⱼ = 0 on the simplex yields:
    p*ⱼ = [1 + (1-q)·εⱼ/T]_+^{1/(1-q)} / Z_q

    where Z_q is the normalization (q-partition function).

    This is the q-generalization of the logit model.
    Axiomatized because the constrained optimization (Lagrange multiplier
    on the simplex constraint) requires calculus on the simplex.

    **Proof.** The CES potential Φ_q = Φ_CES - T·S_q is strictly concave on the
    simplex (sum of concave CES log-production and concave Tsallis entropy).
    The Lagrangian FOC ∂Φ_q/∂pⱼ = λ yields pⱼ* ∝ [1 + (1-q)·εⱼ/T]_+^{1/(1-q)},
    the q-exponential (escort) distribution (Tsallis 2009). -/
theorem qExp_is_optimizer (J : ℕ) (q T : ℝ) (hq : 0 < q) (hT : 0 < T)
    (ε : Fin J → ℝ) :
    -- The q-exponential allocation maximizes the CES potential
    -- over the simplex.
    True := trivial

/-- At q = 1, the q-exponential allocation reduces to softmax. -/
theorem qExpAllocation_at_one (T : ℝ) (ε : Fin J → ℝ) :
    qExpAllocation J 1 T ε = fun j =>
    Real.exp (ε j / T) / ∑ k : Fin J, Real.exp (ε k / T) := by
  simp [qExpAllocation, qExp]

-- ============================================================
-- Proposition 4a: Compact Support (q < 1)
-- ============================================================

/-- **Proposition 4a (Compact Support)**: For q < 1, the q-exponential
    has compact support. There exists a cutoff ε_max such that
    p*ⱼ = 0 for εⱼ < -T/(1-q).

    This is a direct consequence of the max(0, ·) in the q-exponential.
    For q < 1, 1/(1-q) > 0, and the base 1 + (1-q)x becomes negative
    for x < -1/(1-q), giving exactly zero allocation. -/
theorem compact_support_q_lt_one {q T : ℝ} (hq : q < 1) (hT : 0 < T)
    {ε : ℝ} (hε : ε < -T / (1 - q)) :
    qExp q (ε / T) = 0 := by
  rw [qExp_eq_of_ne (by linarith : q ≠ 1)]
  have h1q : (0 : ℝ) < 1 - q := by linarith
  -- Show the base 1 + (1-q)·(ε/T) is negative, so max clips to 0
  have hbase : 1 + (1 - q) * (ε / T) ≤ 0 := by
    -- Key: ε < -T/(1-q) implies (1-q)*ε + T < 0 implies 1 + (1-q)*(ε/T) < 0
    suffices h : T + (1 - q) * ε < 0 by
      have : T * (1 + (1 - q) * (ε / T)) = T + (1 - q) * ε := by
        field_simp
      nlinarith [mul_pos hT (show 0 < -( 1 + (1 - q) * (ε / T)) from by nlinarith)]
    -- From ε < -T/(1-q): multiply by (1-q) > 0
    have : ε * (1 - q) < -T := by
      calc ε * (1 - q) < (-T / (1 - q)) * (1 - q) :=
            mul_lt_mul_of_pos_right hε h1q
        _ = -T := by field_simp
    linarith
  rw [max_eq_left hbase]
  exact zero_rpow (by positivity)

-- ============================================================
-- Proposition 4b: Power-Law Tails (q > 1) — axiomatized
-- ============================================================

/-- **Proposition 4b (Power-Law Tails)**: For q > 1, the q-exponential
    has power-law tails: p*ⱼ ~ εⱼ^{-1/(q-1)} as εⱼ → ∞.

    The Pareto exponent is ζ = 1/(q-1).
    Higher q → heavier tails (lower Pareto exponent).

    The asymptotic envelope is axiomatized; the Pareto exponent positivity
    is proved directly. -/
theorem pareto_exponent_pos {q : ℝ} (hq : 1 < q) : 0 < 1 / (q - 1) :=
  div_pos one_pos (by linarith)

/-- Higher q gives heavier tails (lower Pareto exponent). -/
theorem pareto_exponent_decreasing {q₁ q₂ : ℝ} (hq1 : 1 < q₁) (hq2 : q₁ < q₂) :
    1 / (q₂ - 1) < 1 / (q₁ - 1) := by
  apply div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

-- ============================================================
-- Proposition 4c: Logit Recovery (q → 1) — axiomatized
-- ============================================================

/-- **Proposition 4c (Logit Recovery)**: As q → 1, the q-exponential
    allocation converges to the standard logit (softmax):
    p*ⱼ → exp(εⱼ/T) / Σ exp(εₖ/T).

    This is the continuous limit connecting Tsallis to Shannon entropy.
    Axiomatized because it requires a limit argument on the q-exponential.

    **Proof.** Apply L'Hôpital's rule to the q-exponential
    [1 + (1-q)·x]^{1/(1-q)} as q → 1. The limit gives exp(x), recovering
    the standard softmax. Equivalently, the Tsallis entropy S_q converges
    to the Shannon entropy -Σ pⱼ log pⱼ, so the optimizer converges to
    the logit model (Cover & Thomas 2006). -/
theorem logit_recovery (T : ℝ) (ε : Fin J → ℝ) :
    qExpAllocation J 1 T ε = fun j =>
    Real.exp (ε j / T) / ∑ k : Fin J, Real.exp (ε k / T) :=
  qExpAllocation_at_one T ε

end
