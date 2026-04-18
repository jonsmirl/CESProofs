/-
  LogZExperiment/Layer0.lean — Layer 0: The Master Generator.

  The bottom of the tradition-neutral top-down architecture.
  One definition, and the basic structural properties that are
  shared across Aczél and Chentsov readings.

  **Layer status**: NEUTRAL.

  **Contents**:
  - The master generator `logZ`.
  - Reduction to existing `escortPartitionZ`.
  - Basic positivity.
  - Structural properties shared by both traditions:
    (a) permutation invariance (Aczél A2 / Chentsov coord invariance).
    (b) scalar homogeneity in x (Aczél A1 / Chentsov scaling relation).
-/

import CESProofs.Foundations.InformationGeometry

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

namespace LogZExperiment

-- ============================================================
-- Definition: the master generator
-- ============================================================

/-- **The master generator (tradition-neutral)**.
    `logZ x ρ := log (∑ j, x_j^ρ)`.

    Under Aczél-reading, `x : Fin J → ℝ` is a positive production
    input vector and `ρ` is the CES elasticity parameter; `logZ`
    is then (up to additive `log J` and a `ρ` scale) the
    log-CES-aggregator.

    Under Chentsov-reading, `x` is the coordinate on an exponential
    family's statistical manifold and `ρ` parameterizes the family;
    `logZ` is the cumulant-generating function and `exp(logZ)` is
    the partition function `Z`.

    Both readings are specializations of this single definition. -/
def logZ (x : Fin J → ℝ) (ρ : ℝ) : ℝ :=
  Real.log (∑ j : Fin J, (x j) ^ ρ)

-- ============================================================
-- Reduction to existing CESProofs infrastructure
-- ============================================================

/-- `logZ` equals the log of the existing `escortPartitionZ`.
    This is a definitional unfolding showing the existing CESProofs
    code IS log-Z calculus under Aczél-reading names. -/
theorem logZ_eq_log_escortPartition (x : Fin J → ℝ) (ρ : ℝ) :
    logZ x ρ = Real.log (escortPartitionZ x ρ) := rfl

/-- The argument of the `log` in `logZ` is strictly positive on
    the positive orthant (both readings' base-case domain). -/
theorem logZ_argPos [NeZero J] {x : Fin J → ℝ} (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    0 < escortPartitionZ x ρ :=
  escortPartitionZ_pos x hx ρ

-- ============================================================
-- Structural properties (tradition-neutral)
-- ============================================================

/-- **Permutation invariance** of `logZ`.

    Relabeling the inputs by any permutation leaves `logZ` unchanged.
    Under Aczél-reading, this is axiom A2 (symmetry across inputs).
    Under Chentsov-reading, this is a form of coordinate invariance.
    Both traditions view this as a structural regularity, not a
    distinguishing feature — it sits at Layer 0 because it's
    shared. -/
theorem logZ_permutation_invariant (σ : Equiv.Perm (Fin J))
    (x : Fin J → ℝ) (ρ : ℝ) :
    logZ (fun j => x (σ j)) ρ = logZ x ρ := by
  unfold logZ
  congr 1
  exact Equiv.sum_comp σ (fun j => (x j) ^ ρ)

/-- **Scalar homogeneity in x** of `logZ`.

    Rescaling all inputs by a positive scalar `λ` shifts `logZ`
    additively by `ρ · log λ`:

        logZ (λ · x) ρ = ρ · log λ + logZ x ρ.

    Under Aczél-reading, this is axiom A1 (homogeneity of degree
    `ρ` in the partition sum, equivalently degree 1 in the CES
    aggregator). Under Chentsov-reading, it is the scaling
    covariance of the log-partition function. Again tradition-
    neutral; shared structure, different interpretations. -/
theorem logZ_homogeneity [NeZero J] {x : Fin J → ℝ} (hx : ∀ j, 0 < x j)
    {lam : ℝ} (hlam : 0 < lam) (ρ : ℝ) :
    logZ (fun j => lam * x j) ρ = ρ * Real.log lam + logZ x ρ := by
  unfold logZ
  have h_mul_rpow : ∀ j : Fin J, (lam * x j) ^ ρ = lam ^ ρ * (x j) ^ ρ := by
    intro j
    exact Real.mul_rpow (le_of_lt hlam) (le_of_lt (hx j))
  have h_sum_eq :
      ∑ j : Fin J, (lam * x j) ^ ρ =
      lam ^ ρ * ∑ j : Fin J, (x j) ^ ρ := by
    simp_rw [h_mul_rpow]
    exact (Finset.mul_sum _ _ _).symm
  rw [h_sum_eq]
  have hlam_pow_pos : 0 < lam ^ ρ := Real.rpow_pos_of_pos hlam ρ
  have hsum_pos : 0 < ∑ j : Fin J, (x j) ^ ρ := escortPartitionZ_pos x hx ρ
  rw [Real.log_mul (ne_of_gt hlam_pow_pos) (ne_of_gt hsum_pos)]
  rw [Real.log_rpow hlam]

end LogZExperiment

end
