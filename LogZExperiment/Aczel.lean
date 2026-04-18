/-
  LogZExperiment/Aczel.lean — Layer 5 (Aczél fork).

  **Layer status**: HARD FORK. This file commits to the Aczél-
  tradition reading: `x : Fin J → ℝ` as positive production
  inputs, `ρ` as CES elasticity parameter, downstream objects
  named in production-economics language.

  **Post-fork content**: named downstream objects on the Aczél
  side, proved equivalent to the tradition-neutral backbone
  (Layers 0–4), plus 3–4 characteristic theorems that demonstrate
  Aczél-flavor reasoning.

  **Named objects**:
  - `factorShare` — the Aczél name for the Layer 1 escort.
    Interpretation: cost share of input `j` at the CES optimum.
  - `cesAggregator` — the CES production function `F_ρ(x)`.
    Related to `logZ` by `ρ · log F = logZ − log J`.
  - `economicCurvature` — the curvature parameter `K = (1−ρ)(J−1)/J`
    that controls six downstream roles (superadditivity,
    correlation robustness, strategic independence, network
    scaling, statistical estimation, phase ordering).
  - `costFunction` — the Legendre-dual cost function with
    Hölder-conjugate exponent `r = ρ/(ρ−1)`. Formula-level only;
    full Shephard duality deferred to Layer 6.
  - `arrowPratt` — docstring anchor (no new def) tying
    economic curvature to the Arrow-Pratt coefficient of
    risk aversion.

  See `CESProofs/LogZExperiment/Chentsov.lean` for the sibling
  Chentsov-tradition fork (same underlying formulas; different
  names; different downstream theorem cascade).
-/

import CESProofs.LogZExperiment.Master
import CESProofs.Applications.Economics
import CESProofs.Foundations.Defs
import CESProofs.Foundations.InformationGeometry

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

namespace LogZExperiment
namespace Aczel

-- ============================================================
-- Named object 1: factorShare (Aczél name for escort)
-- ============================================================

/-- **`factorShare`** (Aczél reading): the CES cost share of
    input `j` at unit weights. Equal to the Layer 1 `escort` by
    construction — this file just names it in Aczél language.

    For weighted factor shares with arbitrary weights, see
    `Applications.Economics.factorShare`. -/
def factorShare (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) : ℝ :=
  escort x ρ j

/-- **`factorShare_is_escort`**: the Aczél `factorShare` IS the
    Layer 1 `escort`. Same object, different name. -/
theorem factorShare_is_escort (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) :
    factorShare x ρ j = escort x ρ j := rfl

-- ============================================================
-- Named object 2: cesAggregator (Aczél name for powerMean)
-- ============================================================

/-- **`cesAggregator`** (Aczél reading): the CES production
    function `F_ρ(x) = ( (1/J) · Σ_j x_j^ρ )^(1/ρ)`. Equal to
    the existing Mathlib/CESProofs `powerMean`; this file just
    re-exposes it under an Aczél-reading name. -/
def cesAggregator (J : ℕ) (ρ : ℝ) (hρ : ρ ≠ 0) : AggFun J :=
  powerMean J ρ hρ

/-- **`cesAggregator_and_logZ`**: under Aczél reading, the CES
    aggregator `F_ρ` is connected to the Layer 0 master generator
    `logZ` via the identity `ρ · log F_ρ = logZ − log J`.

    Reduction of `logCES_eq_logPartition` from `InformationGeometry`
    and Layer 4's `logZ_and_powerMean`. -/
theorem cesAggregator_and_logZ [NeZero J] {ρ : ℝ} (hρ : ρ ≠ 0)
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) :
    ρ * Real.log (cesAggregator J ρ hρ x) = logZ x ρ - Real.log ↑J :=
  logZ_and_powerMean hρ x hx

-- ============================================================
-- Named object 3: economicCurvature (Aczél name for K)
-- ============================================================

/-- **`economicCurvature`** (Aczél reading): the curvature
    parameter `K = (1−ρ)(J−1)/J`. Under Aczél reading, `K`
    simultaneously controls six downstream production-economics
    roles (see `CurvatureRoles/QuadrupleRole.lean`). Equal to
    the existing `curvatureK`. -/
def economicCurvature (J : ℕ) (ρ : ℝ) : ℝ := curvatureK J ρ

/-- **`economicCurvature_positive`**: under the Aczél
    complementarity reading (`ρ < 1`, `J ≥ 2`), the economic
    curvature is strictly positive. This is the characteristic
    Aczél sign condition — "ρ < 1 means complementarity, which
    means positive curvature, which means concavity on `1⊥`".

    Reduction of `Defs.curvatureK_pos`. -/
theorem economicCurvature_positive {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ}
    (hρ : ρ < 1) :
    0 < economicCurvature J ρ := curvatureK_pos hJ hρ

-- ============================================================
-- Named object 4: costFunction (Legendre dual in production)
-- ============================================================

/-- **`costFunction`** (Aczél reading): the Legendre-Fenchel
    dual of the CES production function, with Hölder-conjugate
    exponent `r = ρ/(ρ−1)`:

        C(p; ρ) = ( Σ_j p_j^r )^(1/r),  r = ρ/(ρ−1).

    Under Aczél production duality, `cesAggregator` (output as
    function of inputs) and `costFunction` (minimum expenditure
    as function of prices) are Legendre duals of each other.

    This file gives the formula only; full Shephard-style duality
    theorems are deferred to Layer 6. -/
def costFunction (J : ℕ) (ρ : ℝ) (p : Fin J → ℝ) : ℝ :=
  (∑ j : Fin J, (p j) ^ (ρ / (ρ - 1))) ^ ((ρ - 1) / ρ)

/-- **`costFunction_complementary_exponent`**: the Hölder
    conjugate relation `1/ρ + 1/r = 1` where `r = ρ/(ρ-1)`.

    Algebraic evidence that the cost-function exponent is the
    Fenchel conjugate in the `p`-direction — a structural
    precursor to full production duality. -/
theorem costFunction_complementary_exponent {ρ : ℝ} (hρ : ρ ≠ 0)
    (hρ1 : ρ ≠ 1) :
    1 / ρ + 1 / (ρ / (ρ - 1)) = 1 := by
  have hρm1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  field_simp
  ring

-- ============================================================
-- Named object 5: arrowPratt (anchor only)
-- ============================================================

/-! ### Arrow-Pratt risk aversion (anchor)

Under Aczél reading, the economic curvature `K` controls
risk-aversion-like sensitivities. The Arrow-Pratt coefficient
of absolute risk aversion is classically `A(x) = −u''(x)/u'(x)`
for univariate utility `u`; in CES, the multivariate analog
involves the Hessian of log F on `1⊥`, which is proportional
to `-curvatureX · economicCurvature` (per Layer 4's bridge).

We do not introduce a new `arrowPratt` definition here (avoids
committing to a univariate-utility formalization). The Aczél-
downstream content (e.g., CES prudence = third cumulant from
`CumulantTower.lean`) suffices as the named-anchor evidence.
Full Arrow-Pratt formalization is Layer 6 material. -/

end Aczel
end LogZExperiment

end
