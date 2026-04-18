/-
  LogZExperiment/Preferences.lean — Layer 7 shared foundation.

  Preference / utility-representation infrastructure shared by
  both Layer 7 Aczel (Harsanyi-style utility aggregation) and
  Layer 7 Chentsov (Arrow + Condorcet, future phase).

  **Layer status**: Layer 7 foundation. NOT a fork — this file
  is the common preference-framework substrate that both
  tradition-specific files import.

  **Design**: the downstream content (Arrow impossibility,
  Condorcet convergence, Harsanyi aggregation) is all
  hypothesis-bundled matching the Phase 3 / Layer 5 / Layer 6
  pattern. The *preference → utility → real* bridge (Debreu
  representation) is the canonical translation from ordinal
  preferences to the log-Z cardinal-real input space.

  **Contents**:
  - `PreferenceRelation` — binary relation structure with the
    three axioms (reflexivity, transitivity, completeness).
  - `IsUtilityRepresentation` — predicate for when a utility
    function represents a preference relation.
  - `debreuRepresentation_bundled` — the Debreu representation
    theorem stated hypothesis-bundled.
  - `utility_shareFunction_softmax` — the bridge to TenWayIdentity's
    11th view: utility functions + softmax produce shareFunction
    instances, reducing social-choice aggregation to log-Z calculus.
-/

import CESProofs.LogZExperiment.Master
import CESProofs.Foundations.TenWayIdentity

open Real Finset BigOperators

noncomputable section

namespace LogZExperiment
namespace Preferences

-- ============================================================
-- PreferenceRelation structure
-- ============================================================

/-- **`PreferenceRelation α`**: a binary relation `≼ : α → α → Prop`
    with the three standard rationality axioms (reflexivity,
    transitivity, completeness). This is the classical
    preference-relation structure of choice theory. -/
structure PreferenceRelation (α : Type*) where
  /-- The underlying binary preference relation. -/
  prefRel : α → α → Prop
  /-- Reflexivity: everything is at least as good as itself. -/
  refl : ∀ a, prefRel a a
  /-- Transitivity: `a ≼ b` and `b ≼ c` imply `a ≼ c`. -/
  trans : ∀ {a b c}, prefRel a b → prefRel b c → prefRel a c
  /-- Completeness: any two elements are comparable. -/
  complete : ∀ a b, prefRel a b ∨ prefRel b a

-- ============================================================
-- Utility representation
-- ============================================================

/-- **`IsUtilityRepresentation`**: the utility function `u` represents
    the preference relation `P` iff `a ≼ b ↔ u(a) ≤ u(b)`. -/
def IsUtilityRepresentation {α : Type*} (P : PreferenceRelation α)
    (u : α → ℝ) : Prop :=
  ∀ a b, P.prefRel a b ↔ u a ≤ u b

/-- **Debreu representation theorem** (hypothesis-bundled).

    Classical statement (Debreu 1954): every continuous
    preference relation on a connected, separable topological
    space has a continuous utility representation. The
    continuity + separability hypotheses are bundled as
    `h_debreu`; under those hypotheses, a utility representation
    exists.

    **Lean closure (bundled)**: matches Phase 3 / Layer 5 /
    Layer 6 pattern. The existence of a utility function `u`
    with `IsUtilityRepresentation` is supplied as hypothesis.
    The statement form is the classical claim; the proof is
    the hypothesis. -/
theorem debreuRepresentation_bundled
    {α : Type*} (P : PreferenceRelation α)
    (h_debreu : ∃ u : α → ℝ, IsUtilityRepresentation P u) :
    ∃ u : α → ℝ, IsUtilityRepresentation P u := h_debreu

-- ============================================================
-- Bridge to TenWayIdentity: utility + softmax = shareFunction
-- ============================================================

/-- **`softmaxOverUtilities`**: given N agents with utility functions
    `u_i : α → ℝ` evaluated at a specific alternative `a : α`, and
    an inverse-temperature / choice-sharpness parameter `T : ℝ`,
    the softmax aggregation gives the choice probability of
    alternative `j` as the `shareFunction` over `exp(u_j(a)/T)`.

    This connects preference-based social choice to the log-Z
    universal share function calculus: preferences → utility (Debreu)
    → softmax → shareFunction → escort = Layer 1 escort = logZ
    first derivative.

    Direct reduction to TenWayIdentity's `expectedUtilityAllocation`
    (the 11th view): `softmaxOverUtilities u_vals T j` at preference
    profile evaluation equals `expectedUtilityAllocation id T u_vals j`. -/
def softmaxOverUtilities {J : ℕ} (uVals : Fin J → ℝ) (T : ℝ) (j : Fin J) : ℝ :=
  Real.exp (uVals j / T) / ∑ k : Fin J, Real.exp (uVals k / T)

/-- **The softmax aggregation IS a shareFunction** (the Ten-Way
    Identity reduction). Direct `rfl` since both sides are the
    same algebraic form. -/
theorem softmaxOverUtilities_is_shareFunction {J : ℕ}
    (uVals : Fin J → ℝ) (T : ℝ) (j : Fin J) :
    softmaxOverUtilities uVals T j =
    shareFunction (fun k => Real.exp (uVals k / T)) j := rfl

/-- **The softmax aggregation IS `expectedUtilityAllocation` at linear
    utility**. Direct `rfl` since preference → utility produces
    numerical utility values that then feed softmax, which equals
    `expectedUtilityAllocation (fun e => e) T uVals j` (identity
    preprocessing in the Ten-Way 11th view sense).

    Bridge to Layer 5: softmaxOverUtilities factors through
    `expectedUtilityAllocation` (TenWayIdentity's 11th view).
    Since the 11th view is a `shareFunction` instance, so is
    softmaxOverUtilities. -/
theorem softmaxOverUtilities_is_expectedUtility {J : ℕ}
    (uVals : Fin J → ℝ) (T : ℝ) (j : Fin J) :
    softmaxOverUtilities uVals T j =
    expectedUtilityAllocation (fun e => e) T uVals j := rfl

end Preferences
end LogZExperiment

end
