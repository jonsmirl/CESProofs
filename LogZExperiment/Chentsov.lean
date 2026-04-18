/-
  LogZExperiment/Chentsov.lean — Layer 5 (Chentsov fork).

  **Layer status**: HARD FORK. This file commits to the Chentsov-
  tradition reading: `x` as coordinates on a probability simplex
  or an exponential family's parameter space, `ρ` as
  q-deformation / natural parameter, downstream objects named in
  information-geometry language.

  **Post-fork content**: named downstream objects on the Chentsov
  side, proved equivalent to the tradition-neutral backbone
  (Layers 0–4), plus 3–4 characteristic theorems that demonstrate
  Chentsov-flavor reasoning.

  **Named objects**:
  - `escortProbability` — the Chentsov name for the Layer 1
    escort. Interpretation: the probability distribution at
    natural parameter `ρ` in the exponential family.
  - `fisherRaoRho` — the Fisher-Rao metric restricted to the
    ρ-direction (1D). Full matrix-valued Fisher-Rao deferred
    to Layer 6.
  - `sufficientStat` — the canonical sufficient statistic
    `T(x) = log x`; Chentsov's uniqueness theorem (Chentsov
    1972) is about invariance under reductions via this.
  - `klDivergence` — the Kullback-Leibler divergence between
    two simplex-valued distributions. Contrast: the existing
    `klDivExp` in `InformationGeometry.lean` is exponential-
    family-specific; this is the general finite-support form.
  - `naturalParameter` — docstring anchor (no new def).

  See `CESProofs/LogZExperiment/Aczel.lean` for the sibling
  Aczél-tradition fork (same underlying formulas; different
  names; different downstream theorem cascade).
-/

import CESProofs.LogZExperiment.Master
import CESProofs.Foundations.InformationGeometry
import CESProofs.Foundations.CESEstimation
import CESProofs.Foundations.CumulantTower

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

namespace LogZExperiment
namespace Chentsov

-- ============================================================
-- Named object 1: escortProbability (Chentsov name for escort)
-- ============================================================

/-- **`escortProbability`** (Chentsov reading): the probability
    distribution at natural parameter `ρ` in the exponential
    family with sufficient statistic `log x`. Equal to the
    Layer 1 `escort` by construction — this file just names it
    in Chentsov language. -/
def escortProbability (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) : ℝ :=
  escort x ρ j

/-- **`escortProbability_is_escort`**: the Chentsov
    `escortProbability` IS the Layer 1 `escort`. Same object,
    different name. Mirror of `Aczel.factorShare_is_escort` —
    the two Layer-5 named objects are the same underlying function,
    a structural statement of the doubly-unique story. -/
theorem escortProbability_is_escort (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) :
    escortProbability x ρ j = escort x ρ j := rfl

-- ============================================================
-- Named object 2: fisherRaoRho (1D restriction of Fisher-Rao)
-- ============================================================

/-- **`fisherRaoRho`** (Chentsov reading): the Fisher-Rao metric
    restricted to the ρ-direction; equivalently, the scalar
    Fisher information for the ρ-parameter of the exponential
    family. Equal to the Layer 1 `fisherInfoRho`.

    The full matrix-valued Fisher-Rao metric on the probability
    simplex is deferred to Layer 6 (requires general tangent-space
    machinery). -/
def fisherRaoRho (x : Fin J → ℝ) (ρ : ℝ) : ℝ := fisherInfoRho x ρ

/-- **`fisherRaoRho_nonneg`**: the Fisher-Rao metric in the
    ρ-direction is non-negative on the positive orthant. This
    is the characteristic Chentsov statement: Fisher information
    ≥ 0 is Chentsov's invariant-metric-is-positive-semidefinite
    property specialized to the 1D ρ-submanifold.

    Reduction of `escort_variance_nonneg` + `escortCumulant2_eq_variance`
    (both existing in CESProofs). -/
theorem fisherRaoRho_nonneg [NeZero J] (x : Fin J → ℝ)
    (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    0 ≤ fisherRaoRho x ρ := by
  unfold fisherRaoRho fisherInfoRho
  rw [escortCumulant2_eq_variance x hx ρ]
  exact escort_variance_nonneg x hx ρ (fun j => Real.log (x j))

-- ============================================================
-- Named object 3: sufficientStat (the canonical sufficient statistic)
-- ============================================================

/-- **`sufficientStat`** (Chentsov reading): the canonical
    sufficient statistic `T(x) = log x` for the log-Z
    exponential family. Chentsov's uniqueness theorem (Chentsov
    1972) states that the Fisher-Rao metric is the unique
    Riemannian metric on probability distributions invariant
    under reductions via sufficient statistics; `sufficientStat`
    is the concrete witness function.

    A concrete upgrade of Layer 3's abstract `ChentsovSufficient
    F := True` placeholder (which is about F satisfying
    invariance; Layer 5's `sufficientStat` is the witness
    function that concretizes the Chentsov axiomatic content). -/
def sufficientStat (x : ℝ) : ℝ := Real.log x

/-- **`sufficientStat_is_log`**: the canonical sufficient
    statistic IS `Real.log`. Trivial `rfl` — anchors the
    Chentsov narrative that "`log x` is the sufficient
    statistic of the log-Z family". -/
theorem sufficientStat_is_log : sufficientStat = Real.log := rfl

-- ============================================================
-- Named object 4: klDivergence (KL on the simplex)
-- ============================================================

/-- **`klDivergence`** (Chentsov reading): the Kullback-Leibler
    divergence between two distributions on the Chentsov
    (positive-simplex) domain:

        D_KL(p ‖ q) = Σ_j p_j · log(p_j / q_j).

    Contrast: the existing `klDivExp` in
    `InformationGeometry.lean` is exponential-family-specific
    (between two rate parameters); this is the general
    finite-support form on distributions.

    Under Chentsov reading, `klDivergence` is the Bregman
    divergence of `logZ`'s convex conjugate, and is Chentsov-
    invariant in the sense that sufficient-statistic reductions
    preserve it. -/
def klDivergence (p q : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J, p j * Real.log (p j / q j)

/-- **`klDivergence_zero_at_self`**: KL divergence of a
    distribution with itself is zero. Basic Chentsov-side
    non-degeneracy property.

    Under the positive-weight hypothesis `∀ j, 0 < p j`, the
    ratio `p_j / p_j = 1` and `log 1 = 0`, so each term
    vanishes. -/
theorem klDivergence_zero_at_self (p : Fin J → ℝ) (hp : ∀ j, 0 < p j) :
    klDivergence p p = 0 := by
  unfold klDivergence
  apply Finset.sum_eq_zero
  intros j _
  have hpj_ne : p j ≠ 0 := ne_of_gt (hp j)
  rw [div_self hpj_ne, Real.log_one]
  ring

-- ============================================================
-- Named object 5: naturalParameter (anchor only)
-- ============================================================

/-! ### Natural parameter (anchor)

Under Chentsov reading, `ρ` is the natural parameter of the
log-Z exponential family:

    P_j(ρ) = x_j^ρ / Z(ρ) = exp(ρ · T(x_j) - A(ρ))

with `T(x_j) = log x_j` (the `sufficientStat` above) and
`A(ρ) = logZ(x, ρ)` (the log-partition / cumulant-generating
function from Layer 0). The cumulants of `T` under
`escortProbability` are the ρ-derivatives of `logZ`:

    `∂_ρ logZ = E_escort[log x]`     — first cumulant;
    `∂²_ρ logZ = Var_escort[log x]`  — second cumulant =
                                        `fisherRaoRho`.

We do not introduce a `naturalParameter` definition here — `ρ`
is a real-valued parameter already, and the Chentsov reading
is what the docstring of `logZ` (Layer 0) states. This anchor
flags the Chentsov interpretation for future downstream work
(Layer 6: full exponential-family theory; Layer 7: extending
to ordinal preference inputs via Debreu representation). -/

end Chentsov
end LogZExperiment

end
