/-
  Phase 3b Sanity Check — Concrete `HasSymExtension` Instances
  =============================================================

  Purpose: validate the Phase 3b `HasSymExtension`-based API by constructing
  a concrete instance and applying `weighted_aczel_rational` and
  `generalized_aczel_network` to it. This surfaces any ergonomic issues
  with the refactored API before committing to a D6 refactor on top of it.

  Chosen instance: weighted arithmetic mean `F(x) := ∑ j, (p j / N) * x j`
  (where `N = ∑ p j`), whose fully-symmetric extension is the uniform
  arithmetic mean `Ftilde(y) := (1/N) * ∑ ij, y ij` on the Σ-type
  `(j : Fin J) × Fin (p j)`. This corresponds to ρ = 1 in the power-mean
  family, where `Real.rpow` degenerates to plain multiplication and
  strict monotonicity holds on all of ℝ (unlike ρ ≠ 1 which requires
  nonnegativity conventions).

  Findings:
    * The `HasSymExtension` structure is constructable for a concrete F
      using fairly standard Lean tactics (ring, Finset.sum_*, continuity
      bundles).
    * `weighted_aczel_rational` and `generalized_aczel_network` accept
      the concrete instance cleanly.
    * Minor ergonomic wart: the `levelCount (fun j => W i j)` signature
      at the network theorem requires the caller to either match their
      G-definition to `levelCount W` or bridge via an equality of
      functions. Picking `G i := weightedArithMean (levelCount (W i ·))`
      is the smoothest match.
-/

import CESProofs.Foundations.WeightedAczelReduction
import CESProofs.Foundations.NetworkAczel

noncomputable section

open Real Finset BigOperators

namespace Phase3bExamples

-- ============================================================
-- Section 1: Weighted arithmetic mean and its uniform extension
-- ============================================================

/-- Weighted arithmetic mean with rational weights `p j / N` (N = ∑ p j). -/
def weightedArithMean {J : ℕ} (p : Fin J → ℕ) : AggFun J :=
  fun x => ∑ j, ((p j : ℝ) / (↑(∑ k, p k) : ℝ)) * x j

/-- Uniform arithmetic mean on the Σ-type — the natural Ftilde for
    `weightedArithMean p`. -/
def uniformArithMean {J : ℕ} (p : Fin J → ℕ) :
    ((j : Fin J) × Fin (p j) → ℝ) → ℝ :=
  fun y => (1 / (↑(∑ j, p j) : ℝ)) * ∑ ij, y ij

-- ============================================================
-- Section 2: The `HasSymExtension` instance
-- ============================================================

/-- Concrete `HasSymExtension` for the weighted arithmetic mean. -/
def hasSymExt_arith {J : ℕ} (p : Fin J → ℕ) (hp : 0 < (∑ j, p j : ℕ)) :
    HasSymExtension (weightedArithMean p) p where
  Ftilde := uniformArithMean p
  sym := by
    intro σ y
    change (1 / (↑(∑ j, p j) : ℝ)) * (∑ ij, (y ∘ σ) ij) =
           (1 / (↑(∑ j, p j) : ℝ)) * (∑ ij, y ij)
    congr 1
    exact Equiv.sum_comp σ y
  hom := by
    intro c _hc y
    change (1 / (↑(∑ j, p j) : ℝ)) * (∑ ij, c * y ij) =
           c * ((1 / (↑(∑ j, p j) : ℝ)) * (∑ ij, y ij))
    rw [← Finset.mul_sum]
    ring
  cont := by
    change Continuous (fun y : (j : Fin J) × Fin (p j) → ℝ =>
      (1 / (↑(∑ j, p j) : ℝ)) * (∑ ij, y ij))
    exact Continuous.mul continuous_const
      (continuous_finset_sum _ (fun ij _ => continuous_apply ij))
  incr := by
    intro y z hle hlt
    obtain ⟨ij₀, hk⟩ := hlt
    change (1 / (↑(∑ j, p j) : ℝ)) * (∑ ij, y ij) <
           (1 / (↑(∑ j, p j) : ℝ)) * (∑ ij, z ij)
    apply mul_lt_mul_of_pos_left
    · apply Finset.sum_lt_sum
      · intro ij _; exact hle ij
      · exact ⟨ij₀, Finset.mem_univ _, hk⟩
    · have hnpos : (0 : ℝ) < (↑(∑ j, p j) : ℝ) := by exact_mod_cast hp
      exact one_div_pos.mpr hnpos
  eq_fill := by
    intro x
    change (1 / (↑(∑ j, p j) : ℝ)) *
           (∑ ij : (j : Fin J) × Fin (p j), x ij.1) =
           ∑ j, ((p j : ℝ) / (↑(∑ k, p k) : ℝ)) * x j
    rw [sum_replicate_sigma p x, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring

-- ============================================================
-- Section 3: Apply `weighted_aczel_rational` to the instance
-- ============================================================

/-- **API check**: `weighted_aczel_rational` accepts the concrete instance
    and produces the expected existential. -/
theorem weightedArithMean_isPowerMean {J : ℕ} (p : Fin J → ℕ)
    (hp : 0 < (∑ j, p j : ℕ)) :
    ∃ (ρ : ℝ) (_hρ : ρ ≠ 0) (a : Fin J → ℝ),
      (∀ (j k : Fin J), p j = p k → a j = a k) ∧
      (∀ (x : Fin J → ℝ), weightedArithMean p x =
        (∑ j, a j * (x j) ^ ρ) ^ (1 / ρ)) :=
  weighted_aczel_rational (weightedArithMean p) p (hasSymExt_arith p hp)

-- ============================================================
-- Section 4: Concrete network example (2×2 uniform)
-- ============================================================

/-- Uniform 2×2 network: W_{ij} = 1 for all i, j. -/
def W2 : NetworkMatrix 2 := fun _ _ => 1

/-- Each component G_i: weighted arithmetic mean with weights
    `levelCount (W2 i ·)`. Choosing G's weights to match `levelCount W`
    avoids a function-equality rewrite at the HasSymExtension step. -/
def G2 : NetworkAggFun 2 :=
  fun i => weightedArithMean (levelCount (fun j => W2 i j))

/-- **API check**: `generalized_aczel_network` applies cleanly to the
    concrete 2×2 uniform network. -/
theorem G2_isNetworkCES : IsNetworkCES G2 W2 := by
  apply generalized_aczel_network (by norm_num : (2 : ℕ) ≤ 2) G2 W2
    (by trivial : IsConnectedNetwork W2)
    (by intro _ _ _ _ _; rfl : NetA3_ScaleConsistent G2)
  intro i
  -- Goal: HasSymExtension (G2 i) (levelCount (fun j => W2 i j))
  -- G2 i = weightedArithMean (levelCount (fun j => W2 i j)) by def.
  -- So we can apply `hasSymExt_arith` directly; need only 0 < ∑ p.
  have hp : 0 < (∑ j, levelCount (fun j => W2 i j) j : ℕ) := by
    apply Finset.sum_pos
    · intro j _; exact levelCount_pos _ _
    · exact Finset.univ_nonempty
  exact hasSymExt_arith (levelCount (fun j => W2 i j)) hp

end Phase3bExamples

end
