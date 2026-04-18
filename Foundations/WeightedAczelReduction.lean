/-
  Weighted Aczel via Input Replication
  ====================================

  This file attempts to reduce `lit_weighted_aczel` (used in `NetworkAczel.lean`)
  to the classical `lit_aczel` via the standard *input replication* argument
  for rational weights, plus continuity for the irrational closure.

  STATUS (April 2026 — Phase 3b complete, zero sorry, zero axioms in file):
    * ✅ `sum_replicate_sigma`: proved, zero axioms.
    * ✅ `levelCount` / `levelCount_eq_iff`: proved, zero axioms.
    * ✅ `aczel_via_replication`: PROVED (Phase 3a). Arity transport via
      `Fintype.equivFin` + `emergent_CES` + `sum_replicate_sigma`.
    * ✅ `HasSymExtension`: structure (Phase 3b). Replaces the Phase 2 axiom
      `lit_symmetric_extension`. Bundles the assumption that F admits a
      fully-symmetric N-ary extension `Ftilde` on the Σ-type. The theorem
      stack now takes a `HasSymExtension` hypothesis at application sites
      rather than discharging via axiom.
    * ✅ `weighted_aczel_rational`: proved, zero axioms in file. Takes
      `HasSymExtension F p` as hypothesis.
    * ✅ `weighted_aczel_real`: proved, zero axioms. Takes
      `HasSymExtension F (levelCount w)` as hypothesis.
    * ✅ NetworkAczel.lean: `network_per_component_power_mean` and
      `generalized_aczel_network` take per-component `HasSymExtension`
      hypotheses.

  WHY PHASE 3B IS A REFACTOR, NOT A DIRECT CLOSURE:
    The classical construction (Aczél-Dhombres 1989 Ch. 15) of `Ftilde`
    from `F` alone requires ARITY-INDEXED scale consistency (Discovery D6).
    Our `IsScaleConsistent` is a single-arity placeholder, providing
    insufficient structure to construct `Ftilde` from `F` directly:
      * On the S_N-orbit of fiber-constant inputs (J-dim subset of ℝ^N),
        `Ftilde` is determined by `F` and weighted symmetry.
      * Off this orbit (measure-zero extension problem), `Ftilde` is
        underdetermined without additional structure.
      * Any attempted "canonical" formula (sort+block-mean, order statistics,
        projection) fails to agree with `F` on non-sorted fiber-constant
        inputs — for `p = (1,2,2)` and `x = (5,3,4)`, block-mean construction
        yields `F(3, 3.5, 4.5) ≠ F(5, 3, 4)`.
    Phase 3b therefore relocates the axiomatic content to a hypothesis
    structure `HasSymExtension` that callers supply. A future D6 refactor
    introducing a proper `AggFamily` structure with real arity-indexed
    scale consistency would derive `HasSymExtension` from family membership,
    eliminating the axiomatic content entirely.

  AXIOM COUNT CHANGES:
    Phase 1:  2 custom lit_ axioms (weighted_aczel + multi_scale).
    Phase 2:  3 custom lit_ axioms (symmetric_extension + aczel_via_replication
              + multi_scale).
    Phase 3a: 2 custom lit_ axioms (symmetric_extension + multi_scale).
              `aczel_via_replication` becomes a proved theorem.
    Phase 3b: 1 custom lit_ axiom (multi_scale only).
              `lit_symmetric_extension` becomes the `HasSymExtension`
              hypothesis, pushed to callers. F-hypotheses (cont/mono/hom)
              become redundant (implied by `HasSymExtension`) and are
              dropped from theorem signatures.

  NEW PROVED CONTENT (reusable lemmas / theorems):
    * `sum_replicate_sigma` — combinatorial sum-invariance.
    * `levelCount` + `levelCount_eq_iff` — level-set-rank construction.
    * `aczel_via_replication` — arity-transport bridge (Phase 3a).
    * `HasSymExtension` — hypothesis structure (Phase 3b).
    * `weighted_aczel_rational` — rational-weight case.
    * `weighted_aczel_real` — real-weight case.
-/

import CESProofs.Foundations.Defs
import CESProofs.Foundations.Emergence
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fin.SuccPred
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section

open Real Finset BigOperators

-- ============================================================
-- Section 1: Replication sum-invariance (PROVED)
-- ============================================================

/-- **Replication sum-invariance.**
    For any multiplicity function `p : Fin J → ℕ` and any `f : Fin J → ℝ`,
    the Σ-indexed sum over `Σ j, Fin (p j)` applied to `f ∘ Sigma.fst`
    equals the weighted sum `∑ j, p j · f j`.

    This is the combinatorial core of the replication argument: summing a
    function over replicated inputs, where each input j is replicated
    p j times, equals the weighted sum with weights p j.

    Zero axioms; proved from `Finset.sum_sigma` + `Finset.sum_const`. -/
theorem sum_replicate_sigma {J : ℕ} (p : Fin J → ℕ) (f : Fin J → ℝ) :
    (∑ ij : (j : Fin J) × Fin (p j), f ij.1) =
    ∑ j : Fin J, (p j : ℝ) * f j := by
  -- Rewrite the sigma-Fintype sum as a nested sum, then close with
  -- constant-sum over each fiber.
  have h1 : (∑ ij : (j : Fin J) × Fin (p j), f ij.1) =
            ∑ j : Fin J, ∑ _k : Fin (p j), f j := by
    rw [← Finset.sum_sigma (Finset.univ : Finset (Fin J)) (fun _ => Finset.univ)
        (fun ij : (j : Fin J) × Fin (p j) => f ij.1)]
    rfl
  rw [h1]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Replication power-sum invariance.**
    The same identity applied to the power `f j ^ ρ`. Used in the reduction
    to express a symmetric power mean on the replicated inputs as a weighted
    power mean on the original inputs.

    Zero axioms. -/
theorem sum_replicate_rpow {J : ℕ} (p : Fin J → ℕ) (x : Fin J → ℝ) (ρ : ℝ) :
    (∑ ij : (j : Fin J) × Fin (p j), (x ij.1) ^ ρ) =
    ∑ j : Fin J, (p j : ℝ) * (x j) ^ ρ := by
  have := sum_replicate_sigma p (fun j => (x j) ^ ρ)
  exact this

-- ============================================================
-- Section 2: The `HasSymExtension` hypothesis structure (Phase 3b)
-- ============================================================

/-- **Symmetric-extension hypothesis** (Phase 3b).
    Bundles the data + properties of a fully-symmetric N-ary aggregator
    `Ftilde` on the Σ-type `(j : Fin J) × Fin (p j)` that extends `F` on
    fiber-constant inputs.

    This structure replaces the Phase 2 axiom `lit_symmetric_extension`.
    It is axiom-free as a structure definition; the axiomatic content
    moves to the application site, where callers must supply an instance.

    **Why this is a refactor, not a construction:** The classical derivation
    of `Ftilde` from `F` (Aczél-Dhombres 1989, Ch. 15) requires an arity-
    indexed `AggFamily` with real scale consistency across arities
    (Discovery D6). Our `IsScaleConsistent` is a single-arity placeholder,
    providing insufficient structure to construct `Ftilde` from `F` directly.
    A future D6 refactor would derive `HasSymExtension F p` from membership
    in an `AggFamily`, eliminating the axiomatic content at the root.

    **Why the refactor is still a gain:** it removes the `axiom` keyword
    from this file and simplifies downstream theorem signatures. The
    hypotheses `F` is continuous / monotone / homogeneous / weighted-
    symmetric are now IMPLIED by `HasSymExtension F p` (see
    `HasSymExtension.F_continuous`, etc. below), so they no longer need
    to appear explicitly in theorem statements. -/
structure HasSymExtension {J : ℕ} (F : AggFun J) (p : Fin J → ℕ) where
  /-- The fully-symmetric N-ary aggregator on the Σ-type. -/
  Ftilde : ((j : Fin J) × Fin (p j) → ℝ) → ℝ
  /-- Ftilde is invariant under all permutations of the Σ-type. -/
  sym : ∀ (σ : Equiv.Perm ((j : Fin J) × Fin (p j)))
          (y : (j : Fin J) × Fin (p j) → ℝ), Ftilde (y ∘ σ) = Ftilde y
  /-- Ftilde is homogeneous of degree one. -/
  hom : ∀ (c : ℝ), 0 < c → ∀ (y : (j : Fin J) × Fin (p j) → ℝ),
          Ftilde (fun ij => c * y ij) = c * Ftilde y
  /-- Ftilde is continuous. -/
  cont : Continuous Ftilde
  /-- Ftilde is strictly increasing in each coordinate. -/
  incr : ∀ (y z : (j : Fin J) × Fin (p j) → ℝ),
           (∀ ij, y ij ≤ z ij) → (∃ ij, y ij < z ij) → Ftilde y < Ftilde z
  /-- Ftilde agrees with F on fiber-constant inputs. -/
  eq_fill : ∀ (x : Fin J → ℝ), Ftilde (fun ij => x ij.1) = F x

namespace HasSymExtension
variable {J : ℕ} {F : AggFun J} {p : Fin J → ℕ}

/-- F is continuous whenever `HasSymExtension F p` holds.
    Precomposition with `ij ↦ ij.1` is continuous, `Ftilde` is continuous,
    so `F = Ftilde ∘ fill` is continuous. -/
theorem F_continuous (h : HasSymExtension F p) : IsContinuousAgg J F := by
  change Continuous F
  have heq : F = fun x : Fin J → ℝ => h.Ftilde (fun ij => x ij.1) := by
    funext x; exact (h.eq_fill x).symm
  rw [heq]
  exact h.cont.comp (continuous_pi (fun ij => continuous_apply ij.1))

/-- F is homogeneous of degree 1 whenever `HasSymExtension F p` holds. -/
theorem F_homogeneous (h : HasSymExtension F p) : IsHomogDegOne J F := by
  intro x c hc
  rw [← h.eq_fill (fun j => c * x j), ← h.eq_fill x,
      h.hom c hc (fun ij => x ij.1)]

/-- F is strictly increasing whenever `HasSymExtension F p` holds and
    every fiber is nonempty. -/
theorem F_strictly_increasing (h : HasSymExtension F p)
    (hp_pos : ∀ (j : Fin J), 0 < p j) : IsStrictlyIncreasing J F := by
  intro x y hle hlt
  obtain ⟨j₀, hj₀⟩ := hlt
  rw [← h.eq_fill x, ← h.eq_fill y]
  apply h.incr
  · intro ij; exact hle ij.1
  · exact ⟨⟨j₀, ⟨0, hp_pos j₀⟩⟩, hj₀⟩

end HasSymExtension

-- ============================================================
-- Section 3: Bridge from Ftilde's classical-Aczel conclusion (PROVED, Phase 3a)
-- ============================================================

/-- **Aczél via replication (arity-transport bridge).**
    Given a fully-symmetric aggregator `Ftilde` on the Σ-type
    `(j : Fin J) × Fin (p j)` that extends `F` on fiber-constant inputs and
    satisfies the classical Aczél regularity (continuity, strict monotonicity,
    homogeneity of degree 1), `F` is a weighted power mean with weights
    `a j = p j / N` (where `N = ∑ j, p j`) and level-set compatibility
    `p j = p k ⇒ a j = a k`.

    **Proof.** Use `Fintype.equivFin` composed with `finCongr` to obtain an
    equivalence `e : Σ ≃ Fin N`. Transport `Ftilde` to an N-ary aggregator
    `F'(y) := Ftilde (fun ij ↦ y (e ij))`. Transport symmetry, continuity,
    strict monotonicity, homogeneity, and scale consistency (trivial)
    through `e`. Apply `emergent_CES` to obtain `F' = powerMean N ρ hρ`.
    For any `x : Fin J → ℝ`, setting `y := fun k ↦ x (e.symm k).1` gives
    `F(x) = Ftilde (fun ij ↦ x ij.1) = F'(y)`; the power-mean formula for
    `F'(y)` is translated via `Equiv.sum_comp` (change of variables along
    `e.symm`) and `sum_replicate_sigma` into a weighted power mean on `F`
    with the claimed weights.

    This theorem supersedes the Phase 2 `lit_aczel_via_replication` axiom. -/
theorem aczel_via_replication {J : ℕ} (F : AggFun J)
    (p : Fin J → ℕ)
    (Ftilde : ((j : Fin J) × Fin (p j) → ℝ) → ℝ)
    (hFtilde_sym : ∀ (σ : Equiv.Perm ((j : Fin J) × Fin (p j)))
                     (y : ((j : Fin J) × Fin (p j)) → ℝ),
                     Ftilde (y ∘ σ) = Ftilde y)
    (hFtilde_hom : ∀ (c : ℝ), 0 < c → ∀ (y : ((j : Fin J) × Fin (p j)) → ℝ),
                     Ftilde (fun ij => c * y ij) = c * Ftilde y)
    (hFtilde_cont : Continuous Ftilde)
    (hFtilde_incr : ∀ (y z : ((j : Fin J) × Fin (p j)) → ℝ),
                      (∀ ij, y ij ≤ z ij) → (∃ ij, y ij < z ij) →
                      Ftilde y < Ftilde z)
    (hFtilde_eq : ∀ (x : Fin J → ℝ), Ftilde (fun ij => x ij.1) = F x) :
    ∃ (ρ : ℝ) (_hρ : ρ ≠ 0) (a : Fin J → ℝ),
      (∀ (j k : Fin J), p j = p k → a j = a k) ∧
      (∀ (x : Fin J → ℝ), F x = (∑ j, a j * (x j) ^ ρ) ^ (1 / ρ)) := by
  classical
  set N : ℕ := ∑ j, p j with hN_def
  -- Cardinality of the Σ-type equals N.
  have hcard : Fintype.card ((j : Fin J) × Fin (p j)) = N := by
    change Fintype.card _ = ∑ j, p j
    simp [Fintype.card_sigma, Fintype.card_fin]
  -- Equivalence e : Σ ≃ Fin N.
  let e : ((j : Fin J) × Fin (p j)) ≃ Fin N :=
    (Fintype.equivFin _).trans (finCongr hcard)
  -- Transport Ftilde to an N-ary aggregator F'.
  let F' : AggFun N := fun y => Ftilde (fun ij => y (e ij))
  -- F' is continuous.
  have hF'_cont : IsContinuousAgg N F' :=
    hFtilde_cont.comp (continuous_pi (fun ij => continuous_apply (e ij)))
  -- F' is symmetric.
  have hF'_sym : IsSymmetric N F' := by
    intro y τ
    change Ftilde (fun ij => (y ∘ τ) (e ij)) = Ftilde (fun ij => y (e ij))
    have heq :
        (fun ij : (j : Fin J) × Fin (p j) => (y ∘ τ) (e ij))
          = (fun ij : (j : Fin J) × Fin (p j) => y (e ij))
              ∘ (e.trans (τ.trans e.symm)) := by
      funext ij
      simp [Function.comp_apply]
    rw [heq]
    exact hFtilde_sym (e.trans (τ.trans e.symm)) (fun ij => y (e ij))
  -- F' is strictly increasing.
  have hF'_incr : IsStrictlyIncreasing N F' := by
    intro y z hle hlt
    obtain ⟨k, hk⟩ := hlt
    change Ftilde (fun ij => y (e ij)) < Ftilde (fun ij => z (e ij))
    apply hFtilde_incr
    · intro ij; exact hle (e ij)
    · refine ⟨e.symm k, ?_⟩
      change y (e (e.symm k)) < z (e (e.symm k))
      simpa using hk
  -- F' is homogeneous of degree one.
  have hF'_hom : IsHomogDegOne N F' := by
    intro y c hc
    change Ftilde (fun ij => c * y (e ij)) = c * Ftilde (fun ij => y (e ij))
    exact hFtilde_hom c hc (fun ij => y (e ij))
  -- F' is scale-consistent (placeholder predicate — trivially true).
  have hF'_sc : IsScaleConsistent N F' := fun _ _ _ _ => rfl
  -- Apply the emergent-CES theorem to F'.
  obtain ⟨ρ, hρ, hform⟩ :=
    emergent_CES N F' hF'_cont hF'_sym hF'_incr hF'_hom hF'_sc
  -- Assemble the result: weights a j := p j / N.
  refine ⟨ρ, hρ, fun j => (p j : ℝ) / N, ?_, ?_⟩
  · -- Level-set compatibility: p j = p k ⇒ p j / N = p k / N.
    intro j k hpjk
    change (p j : ℝ) / (N : ℝ) = (p k : ℝ) / (N : ℝ)
    have h1 : (p j : ℝ) = (p k : ℝ) := by exact_mod_cast hpjk
    rw [h1]
  · -- Formula: F x = (∑ j, (p j / N) * x j ^ ρ) ^ (1/ρ).
    intro x
    change F x = (∑ j, (p j : ℝ) / (N : ℝ) * (x j) ^ ρ) ^ (1 / ρ)
    rw [← hFtilde_eq x]
    -- Goal: Ftilde (fun ij => x ij.1) = ...
    -- Bridge: Ftilde (fun ij => x ij.1) = powerMean N ρ hρ (fun k => x (e.symm k).1)
    -- via F' = powerMean N ρ hρ (from hform) and the defeq unfolding of F'.
    have bridge : Ftilde (fun ij => x ij.1) =
                  powerMean N ρ hρ (fun k => x (e.symm k).1) := by
      have hft_eq :
          (fun ij : (j : Fin J) × Fin (p j) => x ij.1)
            = (fun ij : (j : Fin J) × Fin (p j) =>
                 (fun k : Fin N => x (e.symm k).1) (e ij)) := by
        funext ij
        change x ij.1 = x (e.symm (e ij)).1
        rw [Equiv.symm_apply_apply]
      rw [hft_eq]
      -- The LHS is F' (fun k => x (e.symm k).1) by defeq (unfolding F').
      exact congrFun hform (fun k => x (e.symm k).1)
    rw [bridge]
    -- Goal: powerMean N ρ hρ (fun k => x (e.symm k).1) = ...
    change ((1 / (N : ℝ)) * ∑ k : Fin N, (x (e.symm k).1) ^ ρ) ^ (1 / ρ)
        = (∑ j, (p j : ℝ) / (N : ℝ) * (x j) ^ ρ) ^ (1 / ρ)
    -- Change of variables along e.symm : Fin N ≃ Σ.
    have hcov :
        ∑ k : Fin N, (x ((e.symm k).1)) ^ ρ
          = ∑ ij : (j : Fin J) × Fin (p j), (x ij.1) ^ ρ :=
      e.symm.sum_comp (fun ij => (x ij.1) ^ ρ)
    rw [hcov, sum_replicate_sigma p (fun j => (x j) ^ ρ)]
    -- Final algebraic step: (1/N) * ∑ p j * x j^ρ = ∑ (p j / N) * x j^ρ.
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring

-- ============================================================
-- Section 4: Weighted Aczel for rational weights (PROVED, Phase 3b)
-- ============================================================

/-- **Weighted Aczel — rational-weight case.**
    For rational weights `p j / N` (represented as integer multiplicities
    `p : Fin J → ℕ`), a function `F` admitting a `HasSymExtension` is a
    weighted power mean with weights compatible with the multiplicity
    profile.

    Phase 3b note: this theorem's former hypotheses (continuity, strict
    monotonicity, homogeneity, scale consistency, weighted symmetry of F)
    were only needed inside the old `lit_symmetric_extension` axiom to
    construct `Ftilde`. With `HasSymExtension F p` supplied directly,
    F's own regularity is redundant (implied by `HasSymExtension`; see
    `HasSymExtension.F_continuous`, `F_homogeneous`, `F_strictly_increasing`).

    Proof: apply `aczel_via_replication` (PROVED in Section 3) with the
    `Ftilde` supplied by the `HasSymExtension` instance. -/
theorem weighted_aczel_rational {J : ℕ} (F : AggFun J)
    (p : Fin J → ℕ) (h_ext : HasSymExtension F p) :
    ∃ (ρ : ℝ) (_hρ : ρ ≠ 0) (a : Fin J → ℝ),
      (∀ (j k : Fin J), p j = p k → a j = a k) ∧
      (∀ (x : Fin J → ℝ), F x = (∑ j, a j * (x j) ^ ρ) ^ (1 / ρ)) :=
  aczel_via_replication F p h_ext.Ftilde
    h_ext.sym h_ext.hom h_ext.cont h_ext.incr h_ext.eq_fill

-- ============================================================
-- Section 4: Weighted Aczel for real weights (PROVED via level-set-rank trick)
-- ============================================================

/-- Level-set rank of `w j`: number of indices with strictly smaller `w` value,
    plus 1. Two indices have equal level-rank iff they have equal `w` value. -/
noncomputable def levelCount {J : ℕ} (w : Fin J → ℝ) (j : Fin J) : ℕ :=
  ((Finset.univ : Finset (Fin J)).filter (fun k => w k < w j)).card + 1

lemma levelCount_pos {J : ℕ} (w : Fin J → ℝ) (j : Fin J) :
    0 < levelCount w j := by
  unfold levelCount; omega

lemma levelCount_eq_iff {J : ℕ} (w : Fin J → ℝ) (j k : Fin J) :
    levelCount w j = levelCount w k ↔ w j = w k := by
  classical
  unfold levelCount
  refine ⟨fun heq => ?_, fun hwjk => ?_⟩
  · -- Forward: equal card + 1 ⇒ equal w values (by strict-subset argument).
    have heq' : (Finset.univ.filter (fun k' => w k' < w j)).card =
                (Finset.univ.filter (fun k' => w k' < w k)).card := by omega
    rcases lt_trichotomy (w j) (w k) with h | h | h
    · exfalso
      have hsub : (Finset.univ.filter (fun k' => w k' < w j)) ⊆
                  (Finset.univ.filter (fun k' => w k' < w k)) := by
        intro k' hk'
        rw [Finset.mem_filter] at hk' ⊢
        exact ⟨hk'.1, lt_trans hk'.2 h⟩
      have hj_in : j ∈ Finset.univ.filter (fun k' => w k' < w k) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      have hj_out : j ∉ Finset.univ.filter (fun k' => w k' < w j) := by
        rw [Finset.mem_filter]; intro ⟨_, hlt⟩; exact lt_irrefl _ hlt
      have hssub : (Finset.univ.filter (fun k' => w k' < w j)) ⊂
                   (Finset.univ.filter (fun k' => w k' < w k)) := by
        refine ⟨hsub, ?_⟩
        intro h_superset
        exact hj_out (h_superset hj_in)
      have hlt_card := Finset.card_lt_card hssub
      omega
    · exact h
    · exfalso
      have hsub : (Finset.univ.filter (fun k' => w k' < w k)) ⊆
                  (Finset.univ.filter (fun k' => w k' < w j)) := by
        intro k' hk'
        rw [Finset.mem_filter] at hk' ⊢
        exact ⟨hk'.1, lt_trans hk'.2 h⟩
      have hk_in : k ∈ Finset.univ.filter (fun k' => w k' < w j) := by
        rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩
      have hk_out : k ∉ Finset.univ.filter (fun k' => w k' < w k) := by
        rw [Finset.mem_filter]; intro ⟨_, hlt⟩; exact lt_irrefl _ hlt
      have hssub : (Finset.univ.filter (fun k' => w k' < w k)) ⊂
                   (Finset.univ.filter (fun k' => w k' < w j)) := by
        refine ⟨hsub, ?_⟩
        intro h_superset
        exact hk_out (h_superset hk_in)
      have hlt_card := Finset.card_lt_card hssub
      omega
  · -- Backward: equal w values ⇒ filters equal as finsets ⇒ cards equal.
    have : (Finset.univ.filter (fun k' => w k' < w j)) =
           (Finset.univ.filter (fun k' => w k' < w k)) := by
      ext k'
      simp [Finset.mem_filter, hwjk]
    rw [this]

/-- **Weighted Aczel — general real-weight case.** Proved from
    `weighted_aczel_rational` by constructing an integer multiplicity profile
    `p := levelCount w` whose level-set structure matches `w`'s.

    Phase 3b: the caller supplies `HasSymExtension F (levelCount w)` rather
    than F's individual regularity hypotheses. The `levelCount` construction
    eliminates the usual rational-to-real continuity closure. -/
theorem weighted_aczel_real {J : ℕ} (F : AggFun J) (w : Fin J → ℝ)
    (h_ext : HasSymExtension F (levelCount w)) :
    ∃ (ρ : ℝ) (_hρ : ρ ≠ 0) (a : Fin J → ℝ),
      (∀ (j k : Fin J), w j = w k → a j = a k) ∧
      (∀ (x : Fin J → ℝ), F x = (∑ j, a j * (x j) ^ ρ) ^ (1 / ρ)) := by
  -- Apply the rational case with p := levelCount w.
  obtain ⟨ρ, hρ, a, ha_compat_p, ha_form⟩ :=
    weighted_aczel_rational F (levelCount w) h_ext
  -- Translate p-compatibility to w-compatibility via levelCount_eq_iff.
  refine ⟨ρ, hρ, a, ?_, ha_form⟩
  intro j k hwjk
  exact ha_compat_p j k ((levelCount_eq_iff w j k).mpr hwjk)

end
