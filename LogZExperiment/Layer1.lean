/-
  LogZExperiment/Layer1.lean — Layer 1: The Six Derivatives.

  From log Z alone, six derived objects emerge — each named
  differently by Aczél (production/economics) and Chentsov
  (statistics) traditions but representing the same mathematical
  content.

  **Layer status**: NEUTRAL.

  **The six derivatives**:
  1. **Escort** — 1st x-derivative, normalized. Aczél: factor
     share. Chentsov: escort probability / exponential-family
     probability distribution.
  2. **Fisher information (ρ-direction)** — 2nd ρ-derivative.
     Aczél: estimation curvature. Chentsov: Fisher information
     for the ρ-parameter.
  3. **Curvature (x-direction)** — negative 2nd x-derivative on
     `1⊥`. Aczél: economic curvature. Chentsov: natural-parameter
     Fisher information.
  4. **Bridge ratio** — cross-partial scaling constant.
     `b(ρ) = (1-ρ)/ρ²`. Both traditions use the same scalar.
  5. **Legendre dual** — Fenchel conjugate in x. Aczél: cost
     function (production duality). Chentsov: entropy / free
     energy.
  6. **Bregman divergence** — logZ-induced. Aczél: welfare loss.
     Chentsov: KL divergence between exponential-family members.

  This file gives each a tradition-neutral definition and links
  it to the existing CESProofs name where applicable.
-/

import CESProofs.LogZExperiment.Layer0
import CESProofs.Foundations.CumulantTower

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

namespace LogZExperiment

-- ============================================================
-- Derivative 1: Escort (first x-derivative, normalized)
-- ============================================================

/-- **Escort**: the first x-derivative of `logZ`, normalized.

    Formula: `escort x ρ j = x_j^ρ / ∑_k x_k^ρ`.

    Under Aczél-reading, this is the CES factor share (cost share).
    Under Chentsov-reading, this is the escort probability / the
    exponential-family probability distribution at parameter `ρ`. -/
def escort (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) : ℝ :=
  escortProbability x ρ j

/-- `escort` equals the existing `escortProbability`. -/
theorem escort_eq_escortProbability (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) :
    escort x ρ j = escortProbability x ρ j := rfl

/-- Explicit formula for `escort`. -/
theorem escort_formula (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) :
    escort x ρ j = (x j) ^ ρ / escortPartitionZ x ρ := rfl

-- ============================================================
-- Derivative 2: Fisher information (ρ-direction)
-- ============================================================

/-- **Fisher information (ρ-direction)**: the second ρ-derivative
    of `logZ`, equivalently the escort-variance of `log x`:

        I_ρ(x, ρ) = ∂² logZ / ∂ρ² = Var_escort[log x].

    Under Aczél-reading, this is the estimation curvature of the
    CES family at `ρ`. Under Chentsov-reading, this is the Fisher
    information of the `ρ`-parameter exponential family — the
    unique (Chentsov 1972) invariant Riemannian metric on the
    statistical manifold. -/
def fisherInfoRho (x : Fin J → ℝ) (ρ : ℝ) : ℝ :=
  escortCumulant2 x ρ

theorem fisherInfoRho_eq_cumulant2 (x : Fin J → ℝ) (ρ : ℝ) :
    fisherInfoRho x ρ = escortCumulant2 x ρ := rfl

-- ============================================================
-- Derivative 3: Curvature (x-direction, on 1⊥)
-- ============================================================

/-- **Curvature (x-direction) on 1⊥**: negative Hessian eigenvalue
    of `logZ` on the constant-sum subspace, at the uniform
    allocation `x = c · 1`.

    Under Aczél-reading: economic curvature of the log-CES
    aggregator. Under Chentsov-reading: natural-parameter Fisher
    information of the exponential family in its `x`-parameter
    direction. -/
def curvatureX (J : ℕ) (ρ c : ℝ) : ℝ :=
  -hessLogFEigenvalue J ρ c

theorem curvatureX_eq_neg_hessLogF (J : ℕ) (ρ c : ℝ) :
    curvatureX J ρ c = -hessLogFEigenvalue J ρ c := rfl

-- ============================================================
-- Derivative 4: Bridge ratio (cross-partial scaling)
-- ============================================================

/-- **Bridge ratio**: the cross-partial scaling constant connecting
    the x-direction and ρ-direction second derivatives of `logZ`.

    Formula: `b(ρ) = (1 - ρ) / ρ²`.

    Same scalar in both traditions — the bridge theorem asserts
    this universal ratio. -/
def bridge (ρ : ℝ) : ℝ := bridgeRatio ρ

theorem bridge_eq_bridgeRatio (ρ : ℝ) : bridge ρ = bridgeRatio ρ := rfl

theorem bridge_formula (ρ : ℝ) : bridge ρ = (1 - ρ) / ρ ^ 2 := rfl

-- ============================================================
-- Derivative 5: Legendre dual (Fenchel conjugate in x)
-- ============================================================

/-- **Legendre dual** of `logZ` in the `x`-direction.

    `legendreDual p ρ := sup_x { ⟨p, x⟩ - logZ x ρ }` (where the
    sup is taken over positive `x`).

    Under Aczél-reading, this is the **cost function** dual to the
    production function (with input prices `p`). Under Chentsov-
    reading, this is the **negative entropy / free energy**
    functional of the exponential family (with natural parameter
    `p`).

    Production duality and thermodynamic duality are the same
    Legendre transform applied to `logZ`. -/
def legendreDual (p : Fin J → ℝ) (ρ : ℝ) : ℝ :=
  sSup {z : ℝ | ∃ x : Fin J → ℝ, (∀ j, 0 < x j) ∧
                 z = (∑ j, p j * x j) - logZ x ρ}

-- ============================================================
-- Derivative 6: Bregman divergence (logZ-induced)
-- ============================================================

/-- **Bregman divergence** induced by `logZ`.

    `bregmanDivergence logZ x y ρ = logZ x ρ - logZ y ρ
                                     - ⟨∇_x logZ(y, ρ), x - y⟩`.

    Under Aczél-reading, this is the **welfare loss** from
    deviation `x` to reference allocation `y` (measured via
    log-CES potential). Under Chentsov-reading, this is the
    **Kullback-Leibler divergence** between exponential-family
    distributions parameterized by `x` and `y`.

    Welfare loss and KL divergence are the same Bregman divergence
    of `logZ`. We give the scalar 1D form here via `bregmanDiv`
    from `InformationGeometry.lean`; the vector form is the
    per-coordinate sum. -/
def bregmanDivergence1D (φ_at_x φ_at_y φ'_at_y x y : ℝ) : ℝ :=
  bregmanDiv φ_at_x φ_at_y φ'_at_y x y

theorem bregmanDivergence1D_eq_bregmanDiv (φ_at_x φ_at_y φ'_at_y x y : ℝ) :
    bregmanDivergence1D φ_at_x φ_at_y φ'_at_y x y =
    bregmanDiv φ_at_x φ_at_y φ'_at_y x y := rfl

end LogZExperiment

end
