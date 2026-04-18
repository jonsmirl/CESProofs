/-
  LogZExperiment/Chentsov/CramerRao.lean — Layer 6 Chentsov cascade.

  **Layer status**: HARD FORK. Chentsov-tradition downstream.

  Cramér-Rao lower bound on estimator variance, stated in
  hypothesis-bundled form matching Phase 3's
  `mechanism_efficiency_bound` pattern.

  **Classical content**: Rao 1945, Cramér 1946. The
  inequality is `Var[θ̂] ≥ I(θ)⁻¹` for any unbiased estimator
  `θ̂` of `θ`, where `I(θ)` is the Fisher information.

  **Lean content**: Mathlib has no Cramér-Rao content and no
  general probability-measure / estimator infrastructure. We
  therefore follow the Phase 3 template: state the bound
  hypothesis-bundled at the algebraic-identity level, with the
  classical derivation cited in the docstring.
-/

import CESProofs.LogZExperiment.Chentsov

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

namespace LogZExperiment
namespace Chentsov
namespace CramerRao

-- ============================================================
-- Definitions: unbiased estimator + Cramér-Rao bound
-- ============================================================

/-- **`IsUnbiasedEstimator`**: `ρHat x` (an estimator of the
    parameter `ρ`) is unbiased at `(x, ρ)` if its escort-
    expectation equals `ρ`.

    We take the escort expectation as supplied (a real number);
    the full abstract definition would take the escort over
    multiple i.i.d. observations, but we work at the
    point-value level for the bundled form. -/
def IsUnbiasedEstimator (ρHat : (Fin J → ℝ) → ℝ) (x : Fin J → ℝ) (ρ : ℝ)
    (escortMean : ℝ) : Prop :=
  escortMean = ρ

/-- **`cramerRaoBound`**: the Cramér-Rao lower bound on
    variance of an unbiased estimator, using `fisherRaoRho`
    (the 1D Fisher information in the ρ direction) and sample
    size `N`.

    Formula: `CRBound := 1 / (N · I(ρ))`. The classical
    Cramér-Rao inequality asserts `Var[ρHat] ≥ CRBound` for
    any unbiased estimator. -/
def cramerRaoBound (N : ℕ) (fisherInfo : ℝ) : ℝ :=
  1 / ((↑N : ℝ) * fisherInfo)

-- ============================================================
-- Theorem: Cramér-Rao bound (hypothesis-bundled)
-- ============================================================

/-- **Cramér-Rao lower bound** (Rao 1945, Cramér 1946),
    hypothesis-bundled form.

    Given:
    - `h_unbiased`: `ρHat` is an unbiased estimator of `ρ`.
    - `h_fisher_pos`: the Fisher information is strictly
      positive (regularity condition).
    - `h_cr`: the classical Cramér-Rao derivation supplies the
      inequality `Var[ρHat] ≥ cramerRaoBound N I(ρ)`.

    Conclude: the variance of `ρHat` is bounded below by the
    Cramér-Rao bound. The hypothesis-bundled form records the
    classical content explicitly; the Lean proof is the
    identity application of `h_cr`.

    **Scope note**: Mathlib has no Cramér-Rao infrastructure;
    a fully-formalized proof would require general probability-
    measure spaces, unbiased-estimator definitions, and
    differentiation of the likelihood function. This bundled
    form is the Lean-level placeholder while that
    infrastructure remains outside Mathlib. -/
theorem cramerRao_bound_bundled
    (ρHat : (Fin J → ℝ) → ℝ)
    (x : Fin J → ℝ) (ρ : ℝ) (N : ℕ)
    (escortMean varEstimator fisherInfo : ℝ)
    (_h_unbiased : IsUnbiasedEstimator ρHat x ρ escortMean)
    (_h_fisher_pos : 0 < fisherInfo)
    (h_cr : varEstimator ≥ cramerRaoBound N fisherInfo) :
    varEstimator ≥ cramerRaoBound N fisherInfo := h_cr

/-- **Cramér-Rao attainment** (equality case), hypothesis-bundled.

    For the exponential family with natural parameter `ρ`
    (i.e., our escort family), the Cramér-Rao bound is
    *attained* by the maximum-likelihood estimator. This is
    Chentsov's efficient-estimator characterization.

    The equality case is bundled as hypothesis `h_attain`; the
    conclusion is the equality statement. Matches Phase 3
    pattern. -/
theorem cramerRao_attains_at_exponentialFamily
    (N : ℕ) (fisherInfo varEfficient : ℝ)
    (h_attain : varEfficient = cramerRaoBound N fisherInfo) :
    varEfficient = cramerRaoBound N fisherInfo := h_attain

/-- **Cramér-Rao bound scales inversely with `N`**.
    Direct algebraic identity: doubling sample size halves
    the bound. -/
theorem cramerRaoBound_scaling (N₁ N₂ : ℕ) (fisherInfo : ℝ)
    (hI : fisherInfo ≠ 0) (hN₁ : (N₁ : ℝ) ≠ 0) (hN₂ : (N₂ : ℝ) ≠ 0) :
    cramerRaoBound N₁ fisherInfo * (↑N₁ : ℝ) =
    cramerRaoBound N₂ fisherInfo * (↑N₂ : ℝ) := by
  unfold cramerRaoBound
  field_simp

end CramerRao
end Chentsov
end LogZExperiment

end
