/-
  LogZExperiment/Aczel/ArrowPratt.lean — Layer 6 Aczél cascade.

  **Layer status**: HARD FORK. Aczél-tradition downstream.

  Arrow-Pratt risk-aversion content. Two definitions:

  1. `arrowPratt` — univariate absolute risk aversion
     `A(x) := -u''(x) / u'(x)` for utility `u : ℝ → ℝ`.
  2. `arrowPrattCES` — multivariate CES risk-aversion
     coefficient, defined via Layer 5's `economicCurvature`
     and linking to the normalized eigenvalue on `1⊥`.

  Plus two characteristic theorems demonstrating the
  Arrow-Pratt Aczél flavor.

  **Design note**: univariate Arrow-Pratt formalization
  requires `u''` and `u'` as actual derivative values. We use
  the value-level formulation — `arrowPratt u x` takes `u`'s
  first and second derivatives at `x` as supplied values,
  avoiding a Mathlib-derivative dependency. The hypothesis-
  bundled form matches the Phase 3 pattern.
-/

import CESProofs.LogZExperiment.Aczel

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

namespace LogZExperiment
namespace Aczel
namespace ArrowPratt

-- ============================================================
-- Univariate Arrow-Pratt coefficient
-- ============================================================

/-- **`arrowPratt`** (univariate): the Arrow-Pratt coefficient
    of absolute risk aversion `A(x) := -u''(x) / u'(x)`.

    Takes the derivative values `uPrime := u'(x)` and
    `uDoublePrime := u''(x)` as explicit arguments; this
    value-level formulation avoids a direct Mathlib-derivative
    dependency. The classical definition of `arrowPratt` at a
    specific utility `u` and point `x` is obtained by
    substituting the actual derivatives. -/
def arrowPratt (uPrime uDoublePrime : ℝ) : ℝ :=
  -uDoublePrime / uPrime

/-- **Log-utility Arrow-Pratt coefficient**.

    For `u(x) = log x` with `x > 0`, we have `u'(x) = 1/x` and
    `u''(x) = -1/x²`. Therefore
    `arrowPratt u'(x) u''(x) = -(-1/x²) / (1/x) = 1/x`.

    Classical reference point — log utility is the canonical
    constant-relative-risk-aversion utility with CRRA = 1. -/
theorem arrowPratt_logUtility_eq_inverse
    {x : ℝ} (hx : x ≠ 0) (hx2 : x^2 ≠ 0) :
    arrowPratt (1 / x) (-1 / x^2) = 1 / x := by
  unfold arrowPratt
  field_simp

-- ============================================================
-- CES Arrow-Pratt (multivariate)
-- ============================================================

/-- **`arrowPrattCES`** (multivariate CES): the scale-normalized
    risk-aversion coefficient of the CES aggregator at the
    symmetric allocation, tied to Layer 5's `economicCurvature`.

    Formula: `arrowPrattCES J ρ c := economicCurvature J ρ / c`,
    the curvature per unit allocation scale. Under Aczél reading,
    this captures the "how averse is the CES firm to input
    fluctuations" interpretation of curvature. -/
def arrowPrattCES (J : ℕ) (ρ c : ℝ) : ℝ :=
  economicCurvature J ρ / c

/-- **`arrowPrattCES_positive`** under Aczél complementarity
    (`ρ < 1`, `J ≥ 2`, `c > 0`), the CES Arrow-Pratt coefficient
    is strictly positive. -/
theorem arrowPrattCES_positive {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) :
    0 < arrowPrattCES J ρ c := by
  unfold arrowPrattCES
  exact div_pos (economicCurvature_positive hJ hρ) hc

/-- **`arrowPrattCES_eq_economicCurvature_over_c`**: definitional
    unfolding. Captures the Aczél-reading claim "CES risk-
    aversion equals the economic curvature per scale". -/
theorem arrowPrattCES_eq_economicCurvature_over_c (J : ℕ) (ρ c : ℝ) :
    arrowPrattCES J ρ c = economicCurvature J ρ / c := rfl

end ArrowPratt
end Aczel
end LogZExperiment

end
