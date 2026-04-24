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
  - `softmaxOverUtilities` — softmax aggregation over utility
    values at temperature T.
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
-- Softmax aggregation over utilities
-- ============================================================

/-- Softmax aggregation: given utility values `uVals` and temperature
    `T`, the choice probability of alternative `j` is
    `exp(uVals j / T) / Σ_k exp(uVals k / T)`. -/
def softmaxOverUtilities {J : ℕ} (uVals : Fin J → ℝ) (T : ℝ) (j : Fin J) : ℝ :=
  Real.exp (uVals j / T) / ∑ k : Fin J, Real.exp (uVals k / T)

end Preferences
end LogZExperiment

end
