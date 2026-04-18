/-
  LogZExperiment/Layer2.lean — Layer 2: Domain Regularity.

  The first minor fork between Aczél and Chentsov readings:
  the natural domain of `x`.

  **Layer status**: MINOR FORK (parameterized; both readings
  handled by a domain predicate).

  - **Aczél domain**: positive orthant `{x : ∀ j, 0 < x j}`.
    Production inputs are real, positive, with no normalization
    constraint.
  - **Chentsov (statistical) domain**: positive simplex
    `{x : (∀ j, 0 < x j) ∧ ∑ x = 1}`. Probability distributions
    are positive and sum to 1.

  The two domains are related by *normalization*: any Aczél-domain
  element normalizes to a Chentsov-domain element via
  `aczelToChentsov x := x / Σ x`, and every Chentsov-domain
  element is trivially an Aczél-domain element.

  Because both domains are subsets of the positive orthant, and
  `logZ` is well-defined on the whole positive orthant, Layer 2's
  "fork" is really a choice of which sub-domain to restrict to.
  The mathematics is unchanged; only the interpretation differs.
-/

import CESProofs.LogZExperiment.Layer0

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

namespace LogZExperiment

-- ============================================================
-- Domain predicates
-- ============================================================

/-- **Aczél-reading domain**: strictly positive inputs.
    This is the natural domain for production economics
    (inputs are strictly positive quantities). -/
def IsAczelDomain (x : Fin J → ℝ) : Prop := ∀ j, 0 < x j

/-- **Chentsov (statistical) reading domain**: strictly positive
    and summing to 1 (the open simplex).
    This is the natural domain for probability distributions. -/
def IsChentsovDomain (x : Fin J → ℝ) : Prop :=
  (∀ j, 0 < x j) ∧ (∑ j : Fin J, x j = 1)

-- ============================================================
-- Domain relations
-- ============================================================

/-- **Chentsov ⊆ Aczél**: every probability distribution with
    strictly-positive components is in the Aczél domain.
    (Dropping the normalization constraint is forgetful.) -/
theorem chentsov_sub_aczel {x : Fin J → ℝ} (h : IsChentsovDomain x) :
    IsAczelDomain x := h.1

-- ============================================================
-- Normalization: Aczél → Chentsov
-- ============================================================

/-- **Normalization map Aczél → Chentsov**: rescale a positive
    vector to sum to 1. This is the natural "forgetful to
    interpretable" map in the reverse direction. -/
def aczelToChentsov (x : Fin J → ℝ) (j : Fin J) : ℝ :=
  x j / ∑ k : Fin J, x k

/-- Normalization is idempotent on the Chentsov domain. -/
theorem aczelToChentsov_id_on_chentsov {x : Fin J → ℝ}
    (h : IsChentsovDomain x) (j : Fin J) :
    aczelToChentsov x j = x j := by
  unfold aczelToChentsov
  rw [h.2]; ring

/-- Normalization lands in the positive orthant. -/
theorem aczelToChentsov_pos [NeZero J] {x : Fin J → ℝ} (hx : ∀ j, 0 < x j)
    (j : Fin J) :
    0 < aczelToChentsov x j := by
  unfold aczelToChentsov
  have hsum : 0 < ∑ k : Fin J, x k :=
    Finset.sum_pos (fun k _ => hx k) Finset.univ_nonempty
  exact div_pos (hx j) hsum

/-- Normalization sums to 1 (lands on the simplex). -/
theorem aczelToChentsov_sum_one [NeZero J] {x : Fin J → ℝ}
    (hx : ∀ j, 0 < x j) :
    ∑ j : Fin J, aczelToChentsov x j = 1 := by
  unfold aczelToChentsov
  rw [← Finset.sum_div]
  have hsum : 0 < ∑ k : Fin J, x k :=
    Finset.sum_pos (fun k _ => hx k) Finset.univ_nonempty
  exact div_self (ne_of_gt hsum)

/-- **Normalization lands on the Chentsov domain**: the forgetful
    Aczél → Chentsov direction. -/
theorem aczelToChentsov_mem_chentsov [NeZero J] {x : Fin J → ℝ}
    (hx : IsAczelDomain x) :
    IsChentsovDomain (aczelToChentsov x) :=
  ⟨fun j => aczelToChentsov_pos hx j, aczelToChentsov_sum_one hx⟩

-- ============================================================
-- logZ on the Chentsov domain
-- ============================================================

/-- `logZ` is well-defined on the Chentsov domain (positive
    inputs satisfying the simplex constraint). -/
theorem logZ_wellDefined_on_chentsov [NeZero J] {x : Fin J → ℝ}
    (h : IsChentsovDomain x) (ρ : ℝ) :
    0 < escortPartitionZ x ρ :=
  logZ_argPos h.1 ρ

end LogZExperiment

end
