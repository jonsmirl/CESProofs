/-
  CESProofs/Foundations/TenWayIdentity.lean

  Historical filename retained to avoid breaking imports. This file
  previously claimed a "ten-way unification" across economics,
  statistics, information theory, game theory, ML, and physics — the
  claim being that a shared algebraic form `w_j / Σ_k w_k` across
  these fields constituted structural unity. That framing was the
  labels-as-encoding error: the shared form arises independently in
  each field as the maximum-entropy distribution under linear moment
  constraints, not because the fields share a deeper unity.

  What remains: `shareFunction` as a mathematical primitive
  (normalized weights), its universal property lemmas, and a small
  number of auxiliary definitions (`powerMeanWeight`, `luceChoice`,
  `expectedUtilityAllocation`) used by downstream files.

  The ten `*_is_shareFunction` rfl-relabeling theorems, the
  `ten_views_one_object` capstone, the eleventh-view Expected Utility
  narrative, and the `logUtility_locking` claim are deleted.
-/

import CESProofs.Foundations.InformationGeometry
import CESProofs.CurvatureRoles.GameTheory
import CESProofs.Applications.Economics
import CESProofs.Potential.QEquilibrium
import CESProofs.Dynamics.GibbsMeasure

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- The shareFunction primitive
-- ============================================================

/-- Normalized share of a weight vector: `w_j / Σ_k w_k`. -/
def shareFunction (w : Fin J → ℝ) (j : Fin J) : ℝ :=
  w j / ∑ k : Fin J, w k

-- ============================================================
-- Universal properties
-- ============================================================

/-- Shares sum to 1 when the total weight is nonzero. -/
theorem shareFunction_sum_one {w : Fin J → ℝ}
    (hw : (∑ k : Fin J, w k) ≠ 0) :
    ∑ j : Fin J, shareFunction w j = 1 := by
  simp only [shareFunction, ← Finset.sum_div]
  exact div_self hw

/-- Each share is non-negative when all weights are non-negative. -/
theorem shareFunction_nonneg {w : Fin J → ℝ}
    (hw : ∀ j, 0 ≤ w j) (j : Fin J) :
    0 ≤ shareFunction w j :=
  div_nonneg (hw j) (Finset.sum_nonneg fun k _ => hw k)

/-- IIA: the ratio of any two shares depends only on the ratio of
    their weights. -/
theorem shareFunction_iia [NeZero J] {w : Fin J → ℝ}
    (hw : ∀ j, 0 < w j) (j k : Fin J) :
    shareFunction w j / shareFunction w k = w j / w k := by
  simp only [shareFunction]
  have hsum : (0 : ℝ) < ∑ i, w i :=
    Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  field_simp [ne_of_gt hsum, ne_of_gt (hw k)]

/-- Scale invariance: multiplying all weights by a nonzero constant
    does not change shares. -/
theorem shareFunction_scale_invariant {w : Fin J → ℝ}
    {c : ℝ} (hc : c ≠ 0) (j : Fin J) :
    shareFunction (fun k => c * w k) j = shareFunction w j := by
  simp only [shareFunction, ← Finset.mul_sum]
  exact mul_div_mul_left (w j) (∑ k, w k) hc

/-- Each share is at most 1 when weights are nonneg and the total is positive. -/
theorem shareFunction_le_one {w : Fin J → ℝ}
    (hw : ∀ j, 0 ≤ w j)
    (hpos : 0 < ∑ k : Fin J, w k) (j : Fin J) :
    shareFunction w j ≤ 1 := by
  have hsum := shareFunction_sum_one (ne_of_gt hpos)
  calc shareFunction w j
      ≤ ∑ k : Fin J, shareFunction w k :=
        Finset.single_le_sum (fun k _ => shareFunction_nonneg hw k) (Finset.mem_univ j)
    _ = 1 := hsum

-- ============================================================
-- Coordinate, symmetry, and maximum lemmas
-- ============================================================

/-- The share function depends on weights only through the pre-image
    under any preprocessing φ. -/
theorem shareFunction_coordinate_invariance
    (φ : ℝ → ℝ) (y : Fin J → ℝ) (j : Fin J) :
    shareFunction (fun k => φ (y k)) j =
    φ (y j) / ∑ k : Fin J, φ (y k) :=
  rfl

/-- When all weights are equal to a nonzero constant, every share is 1/J. -/
theorem shareFunction_uniform_at_symmetry {J : ℕ} (hJ : 0 < J)
    {c : ℝ} (hc : c ≠ 0) (j : Fin J) :
    shareFunction (fun _ : Fin J => c) j = 1 / ↑J := by
  simp only [shareFunction, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- The maximum-weight component has the largest share. -/
theorem shareFunction_maximum_dominates [NeZero J]
    {w : Fin J → ℝ} (hw : ∀ j, 0 < w j)
    {j₀ : Fin J} (hmax : ∀ k, w k ≤ w j₀) :
    ∀ j, shareFunction w j ≤ shareFunction w j₀ := by
  intro j
  simp only [shareFunction]
  apply div_le_div_of_nonneg_right (hmax j)
  exact (Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty).le

-- ============================================================
-- Auxiliary definitions used by downstream files
-- ============================================================

/-- Contribution of input j to the power mean `(Σ x_j^ρ / J)^{1/ρ}`. -/
def powerMeanWeight (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) : ℝ :=
  (x j) ^ ρ / ∑ k : Fin J, (x k) ^ ρ

/-- Luce choice probability (Luce 1959): `P_j = v_j / Σ v_k`. -/
def luceChoice (v : Fin J → ℝ) (j : Fin J) : ℝ :=
  v j / ∑ k : Fin J, v k

/-- Expected-utility allocation: utility preprocessing φ composed
    with softmax at temperature T. Used by LogZExperiment/Preferences.lean. -/
def expectedUtilityAllocation (φ : ℝ → ℝ) (T : ℝ)
    (ε : Fin J → ℝ) (j : Fin J) : ℝ :=
  Real.exp (φ (ε j) / T) / ∑ k : Fin J, Real.exp (φ (ε k) / T)

end
