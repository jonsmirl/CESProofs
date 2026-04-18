/-
  AggFamily: Arity-indexed family of aggregators (Phase D6)
  =========================================================

  An `AggFamily` bundles an aggregator `F n : AggFun n` at each arity `n ∈ ℕ`
  together with full symmetry, continuity, strict monotonicity, and
  homogeneity at every arity.

  **Scope of D6 closure (honest framing).** This structure is intentionally
  minimal. It does NOT include a cross-arity scale-consistency field,
  because the natural general-block-grouping form of scale consistency
  is INCONSISTENT with standard uniform families (e.g., the uniform
  arithmetic mean `F n (x) := (∑ x) / n` fails it: for `p = (1, 3)`,
  `F_4((5,1,1,1)) = 2` but `F_2(F_1(5), F_3(1,1,1)) = 3`). The regular
  `m*k` form holds for standard families but is too weak to derive the
  general-`p` case of `HasSymExtension` without additional work.

  Instead, D6 takes the following pragmatic route: given a family, define
  the "fiber-weighted" aggregator `weightedOfFiber p` which is `family.F N`
  applied to a fiber-expansion of its input (`N := ∑ p j`). The
  `HasSymExtension (family.weightedOfFiber p) p` instance is then
  constructive — `eq_fill` holds by definition of `weightedOfFiber`.

  The axiomatic content relocates but does not vanish: classical claims
  like "every weighted-symmetric `F` is of the form `family.weightedOfFiber
  p` for some family" remain axiomatic (`lit_aczel` / `lit_kolmogorov_nagumo`
  + the implicit family-existence assumption).

  What D6 does provide:
    * A concrete family-based construction that produces `HasSymExtension`
      instances without invoking `lit_symmetric_extension` at the call site.
    * A clean path for future work to axiomatize the family-existence at a
      higher structural level (e.g., for power-mean families with ρ ≠ 1 on
      restricted domains).

  See `~/thesis/research/demographics/phase_d6_prompt.md` for the original
  D6 specification and `generalized_aczel_status.md` for the obstacle
  analysis that led to this pragmatic formulation.
-/

import CESProofs.Foundations.Defs
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.SuccPred
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section

open Real Finset BigOperators

/-- **Arity-indexed aggregator family** (Phase D6).

    Bundles one aggregator per arity with uniform regularity properties.
    Does NOT include scale-consistency (see file docstring). -/
structure AggFamily where
  /-- The aggregator at each arity. -/
  F : (n : ℕ) → AggFun n
  /-- Continuity at every arity. -/
  continuous : ∀ n, Continuous (F n)
  /-- Full permutation symmetry at every arity. -/
  symmetric : ∀ n, IsSymmetric n (F n)
  /-- Strict monotonicity at every arity. -/
  strict_monotone : ∀ n, IsStrictlyIncreasing n (F n)
  /-- Homogeneity of degree one at every arity. -/
  homogeneous : ∀ n, IsHomogDegOne n (F n)

end
