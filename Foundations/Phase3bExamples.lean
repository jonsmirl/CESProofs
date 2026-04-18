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
-- Section 4: D6 — concrete `AggFamily` instance
-- ============================================================

/-- Uniform arithmetic mean at each arity:
    `F n (x) = (1/n) * ∑ i, x i` for `n ≥ 1`; `F 0 := fun _ => 0` as arbitrary
    unused filler (the `n = 0` case is never touched by downstream
    `AggFamily` usage). -/
def arithMean : (n : ℕ) → AggFun n
  | 0 => fun _ => 0
  | n + 1 => fun x => (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, x i

/-- **Concrete `AggFamily`**: the uniform arithmetic-mean family.

    Verifies end-to-end that `AggFamily.hasSymExtension` produces a
    constructive `HasSymExtension` instance for `family.weightedOfFiber p`
    (a fiber-weighted arithmetic mean). -/
def arithmeticMeanFamily : AggFamily where
  F := arithMean
  continuous := by
    intro n
    cases n with
    | zero => exact continuous_const
    | succ n =>
      refine Continuous.mul continuous_const ?_
      exact continuous_finset_sum _ (fun i _ => continuous_apply i)
  symmetric := by
    intro n x σ
    cases n with
    | zero => rfl
    | succ n =>
      change (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, x (σ i) =
             (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, x i
      congr 1
      exact Equiv.sum_comp σ x
  strict_monotone := by
    intro n x y hle hlt
    obtain ⟨i₀, hi₀⟩ := hlt
    cases n with
    | zero => exact Fin.elim0 i₀
    | succ n =>
      change (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, x i <
             (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, y i
      apply mul_lt_mul_of_pos_left
      · exact Finset.sum_lt_sum (fun i _ => hle i) ⟨i₀, Finset.mem_univ _, hi₀⟩
      · have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
        exact one_div_pos.mpr this
  homogeneous := by
    intro n x c hc
    cases n with
    | zero => simp [arithMean]
    | succ n =>
      change (1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, c * x i =
             c * ((1 / ((n + 1 : ℕ) : ℝ)) * ∑ i, x i)
      rw [← Finset.mul_sum]
      ring

/-- **D6 end-to-end check**: the arithmetic-mean family produces a
    `HasSymExtension` for its fiber-weighted aggregator, constructively.

    The resulting `Ftilde` is the uniform arithmetic mean at arity
    `∑ p j`, transported to the Σ-type. All fields of `HasSymExtension`
    hold by D6's derivation; no custom axioms. -/
example {J : ℕ} (p : Fin J → ℕ) :
    HasSymExtension (arithmeticMeanFamily.weightedOfFiber p) p :=
  arithmeticMeanFamily.hasSymExtension p

-- ============================================================
-- Section 5: Concrete network example (2×2 uniform) via D6 path
-- ============================================================

/-- Uniform 2×2 network: W_{ij} = 1 for all i, j. -/
def W2 : NetworkMatrix 2 := fun _ _ => 1

/-- Each component G_i: the arithmetic-mean family's fiber-weighted
    aggregator at multiplicity profile `levelCount (W2 i ·)`. This goes
    through the **D6 `AggFamily` pipeline** (as opposed to the Phase 3b
    direct construction via `weightedArithMean`).

    Extensionally equal to `weightedArithMean (levelCount ...)` — both
    compute `∑ j, (p j / N) * x j` — but constructed via
    `arithmeticMeanFamily.weightedOfFiber` so that the
    `HasSymExtension` proof arrives from `AggFamily.hasSymExtension`
    (zero custom axioms). -/
def G2 : NetworkAggFun 2 :=
  fun i => arithmeticMeanFamily.weightedOfFiber (levelCount (fun j => W2 i j))

/-- **API check (D6 consolidation)**: `generalized_aczel_network` applies
    cleanly to the concrete 2×2 uniform network when each `G i` is sourced
    from `arithmeticMeanFamily.weightedOfFiber`. The `HasSymExtension`
    hypothesis is discharged by `arithmeticMeanFamily.hasSymExtension`,
    demonstrating the full D6 pipeline end-to-end. -/
theorem G2_isNetworkCES : IsNetworkCES G2 W2 := by
  apply generalized_aczel_network (by norm_num : (2 : ℕ) ≤ 2) G2 W2
    (by trivial : IsConnectedNetwork W2)
    (by intro _ _ _ _ _; rfl : NetA3_ScaleConsistent G2)
  intro i
  -- Goal: HasSymExtension (G2 i) (levelCount (fun j => W2 i j))
  -- By definition of G2, this is
  --   HasSymExtension (arithmeticMeanFamily.weightedOfFiber (levelCount ...))
  --                   (levelCount ...)
  -- which is exactly what arithmeticMeanFamily.hasSymExtension provides.
  exact arithmeticMeanFamily.hasSymExtension (levelCount (fun j => W2 i j))

end Phase3bExamples

end
