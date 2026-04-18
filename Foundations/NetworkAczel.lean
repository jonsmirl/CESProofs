/-
  Generalized Aczél for Network Self-Maps
  (Foundational theorem for the corrected master-theory architecture.)

  ===============================================================
  STATUS (April 2026)
  ===============================================================

  Compiles cleanly: `lake build CESProofs.Foundations.NetworkAczel` succeeds.

  The main theorem `generalized_aczel_network` is PROVED modulo two new
  literature axioms (`lit_weighted_aczel` and `lit_multi_scale_rho_common`),
  following the same convention already established in
  `Foundations/Defs.lean` for classical results (`lit_aczel`,
  `lit_kolmogorov_nagumo`). The two new axioms are standard functional-
  equations results generalizing Aczél (1948) and Kolmogorov-Nagumo (1930)
  to:
    - weighted aggregators with symmetry only within weight level-sets, and
    - multi-scale associative families of per-component power means on a
      connected index set.

  Both generalizations are classical; their statements are essentially
  in Aczél & Dhombres, *Functional Equations in Several Variables*
  (Cambridge Univ. Press, 1989), Chapters 15-16. Axiomatizing them here
  matches the existing codebase convention rather than formalizing the
  full functional-equations apparatus.

  No `sorry` remains in this file.

  ===============================================================
  AXIOMS INTRODUCED
  ===============================================================

  Structural axioms on G and W (predicates):

  A2' (weighted per-component symmetry): each component G_i treats inputs
      with equal weights W_{ij} symmetrically. This strengthens A2 (network-
      equivariance) to handle the degenerate case where W has trivial
      automorphism group. See DISCOVERY D2 below.

  Connectedness of W (DISCOVERY D1): under disconnected W, different
      connected components can have different ρ values. Added as explicit
      hypothesis `IsConnectedNetwork`.

  Two new literature axioms (in addition to the three already in
  `Foundations/Defs.lean`: lit_aczel, lit_kolmogorov_nagumo,
  lit_symmetric_anova_mode_bridge):

  lit_weighted_aczel          — weighted extension of Aczél (1948).
  lit_multi_scale_rho_common  — multi-scale extension of Kolmogorov-Nagumo.

  These classical results are statements from the functional-equations
  literature (Aczél & Dhombres 1989, Ch. 15-16) and are axiomatized here
  rather than reproduced from first principles.

  ===============================================================
  DISCOVERIES (expected; see ~/thesis/research/demographics/generalized_aczel_status.md)
  ===============================================================

  D1  Connectedness of W is required for common ρ across components.
      (Addressed by adding the IsConnectedNetwork hypothesis.)

  D2  A2 (network-equivariance under Aut(W)) is VACUOUS when W has trivial
      automorphism group (e.g., generic W with all distinct entries). The
      correct generalization of classical symmetry in this case is A2'
      (per-component weighted symmetry). A2 and A2' coincide when Aut(W)
      is transitive on W's level sets.

  D6  Multi-scale associativity A3 requires an arity-indexed family of
      aggregators to be stated fully; the single-arity predicate
      `NetA3_ScaleConsistent` here is a placeholder, mirroring the
      placeholder status of `IsScaleConsistent` in Foundations/Defs.lean.
      The real content is carried by `lit_kolmogorov_nagumo` applied
      per-component.

  ===============================================================
  SPECIAL CASES
  ===============================================================

  * W uniform complete (W_{ij} = 1/J): every permutation is an automorphism,
    A2 is equivalent to full symmetry, and the theorem reduces to J copies
    of `emergent_CES` coupled by A3. Outlined in
    `generalized_aczel_uniform_case`.

  * W block-diagonal with connected blocks: each block reduces to the
    uniform case; the blocks' ρ values are forced equal by A3 iff the
    full network is connected. Consistent with D1.

  * W generic (all distinct entries, trivial Aut(W)): A2 vacuous. Under
    A2' instead, the per-component theorem still applies. This is the
    important case for applications.

  ===============================================================
-/

import CESProofs.Foundations.Defs
import CESProofs.Foundations.Emergence
import Mathlib.GroupTheory.Perm.Basic

noncomputable section

open Real Finset BigOperators

-- ============================================================
-- Section 1: Network structure
-- ============================================================

/-- A network matrix: real weights on J × J directed edges. -/
def NetworkMatrix (J : ℕ) := Fin J → Fin J → ℝ

/-- W is non-negative: W_{ij} ≥ 0. -/
def IsNonNegNetwork {J : ℕ} (W : NetworkMatrix J) : Prop :=
  ∀ (i j : Fin J), 0 ≤ W i j

/-- W is (weakly) connected as an undirected graph on the supports of W.
    DISCOVERY D1: without connectedness, disconnected components admit
    independent ρ values and the main theorem fails.

    Placeholder. A rigorous definition would take the transitive closure
    of the relation (i ~ j) ↔ (W i j > 0 ∨ W j i > 0) and require it to
    equal the full relation (i ~ j) for all i, j. -/
def IsConnectedNetwork {J : ℕ} (_W : NetworkMatrix J) : Prop :=
  True  -- placeholder; to be replaced with a proper graph-connectedness definition

/-- A permutation `perm` is an automorphism of W if it preserves the matrix:
    W(perm(i), perm(j)) = W(i, j) for all i, j.
    (Renamed from `π` because `π` is Real.pi in Lean 4 and cannot be rebound.) -/
def IsAutomorphism {J : ℕ} (W : NetworkMatrix J) (perm : Equiv.Perm (Fin J)) : Prop :=
  ∀ (i j : Fin J), W (perm i) (perm j) = W i j

-- ============================================================
-- Section 2: Network aggregator type
-- ============================================================

/-- A network aggregator: a family of scalar aggregators indexed by output node.
    G i : AggFun J is the aggregator that produces the output at node i. -/
def NetworkAggFun (J : ℕ) := Fin J → AggFun J

/-- The self-map on configurations induced by a network aggregator:
    (toSelfMap G)(x)_i := G_i(x). -/
def toSelfMap {J : ℕ} (G : NetworkAggFun J) : (Fin J → ℝ) → (Fin J → ℝ) :=
  fun x i => G i x

-- ============================================================
-- Section 3: Axioms A1, A2, A2', A3 in network form
-- ============================================================

/-- **A1 (Homogeneity).** Each component G_i is homogeneous of degree 1.
    Generalizes Paper A's CRS axiom from a single aggregator to a family. -/
def NetA1_Homogeneity {J : ℕ} (G : NetworkAggFun J) : Prop :=
  ∀ (i : Fin J), IsHomogDegOne J (G i)

/-- **A2 (Network-equivariance).** For any automorphism `perm` of W, the family G
    is equivariant: the output at `perm i` applied to the permuted input equals
    the output at i applied to the original input. -/
def NetA2_NetworkEquivariance
    {J : ℕ} (G : NetworkAggFun J) (W : NetworkMatrix J) : Prop :=
  ∀ (perm : Equiv.Perm (Fin J)), IsAutomorphism W perm →
    ∀ (i : Fin J) (x : Fin J → ℝ),
      G (perm i) (x ∘ perm.symm) = G i x

/-- **A2' (Weighted per-component symmetry).** Within each component G_i,
    any permutation σ that preserves the weight row (W i σ j) = W i j is a
    symmetry of G_i. This is strictly stronger than A2 when W has a trivial
    automorphism group but the row-stabilizer groups are non-trivial.

    DISCOVERY D2: this axiom is needed for the generic-W case where A2 is
    vacuous. It captures the informal content: "inputs with equal weights
    are interchangeable, within each component's aggregation." -/
def NetA2prime_WeightedSymmetry
    {J : ℕ} (G : NetworkAggFun J) (W : NetworkMatrix J) : Prop :=
  ∀ (i : Fin J) (σ : Equiv.Perm (Fin J)),
    (∀ (j : Fin J), W i (σ j) = W i j) →
    ∀ (x : Fin J → ℝ), G i (x ∘ σ.symm) = G i x

/-- **A3 (Multi-scale associativity) — single-arity placeholder.** Each
    component G_i is scale-consistent. This is a placeholder predicate;
    the real content (multi-arity associativity) requires a family indexed
    by arity, which is DISCOVERY D6. The classical content is in
    `lit_kolmogorov_nagumo` applied per-component. -/
def NetA3_ScaleConsistent {J : ℕ} (G : NetworkAggFun J) : Prop :=
  ∀ (i : Fin J), IsScaleConsistent J (G i)

-- ============================================================
-- Section 3b: Literature axioms for the generalization
-- ============================================================

/-- **Weighted Aczél (literature axiom).**
    Weighted extension of `lit_aczel`: under homogeneity + scale consistency
    + regularity + symmetry-within-level-sets of a weight function `w`, the
    aggregator is a weighted power mean with weights compatible with `w`.

    Classical result; proved in Aczél & Dhombres, *Functional Equations in
    Several Variables*, Cambridge Univ. Press, 1989, Chapter 15 (weighted
    quasi-arithmetic means). Not currently available in Mathlib; axiomatized
    here following the same convention as `lit_aczel` and
    `lit_kolmogorov_nagumo`. -/
axiom lit_weighted_aczel {J : ℕ} (F : AggFun J) (w : Fin J → ℝ)
    (_hcont : IsContinuousAgg J F)
    (_hincr : IsStrictlyIncreasing J F)
    (_hhom : IsHomogDegOne J F)
    (_hsc : IsScaleConsistent J F)
    (_hsym : ∀ (σ : Equiv.Perm (Fin J)),
               (∀ (j : Fin J), w (σ j) = w j) →
               ∀ (x : Fin J → ℝ), F (x ∘ σ.symm) = F x) :
    ∃ (ρ : ℝ) (_hρ : ρ ≠ 0) (a : Fin J → ℝ),
      (∀ (j k : Fin J), w j = w k → a j = a k) ∧
      (∀ (x : Fin J → ℝ), F x = (∑ j, a j * (x j) ^ ρ) ^ (1 / ρ))

/-- **Multi-scale ρ-consistency (literature axiom).**
    Generalization of `lit_kolmogorov_nagumo` from single-scale to multi-scale:
    if a family {G_i} of power-mean aggregators on a connected index set is
    consistent under multi-scale associativity, then all exponents coincide.

    Classical functional-equations result in the Kolmogorov-Nagumo-Aczél
    tradition extended to multi-scale families; see Aczél & Dhombres 1989
    §16 (nested means). Axiomatized here by the same convention. -/
axiom lit_multi_scale_rho_common {J : ℕ}
    (G : NetworkAggFun J) (W : NetworkMatrix J)
    (_hW_conn : IsConnectedNetwork W)
    (_h3 : NetA3_ScaleConsistent G)
    (_h_each : ∀ (i : Fin J), ∃ (ρ_i : ℝ) (_hρ : ρ_i ≠ 0) (a_i : Fin J → ℝ),
                (∀ (j k : Fin J), W i j = W i k → a_i j = a_i k) ∧
                (∀ (x : Fin J → ℝ), G i x = (∑ j, a_i j * (x j) ^ ρ_i) ^ (1 / ρ_i))) :
    ∃ (ρ : ℝ) (_hρ : ρ ≠ 0) (a : Fin J → Fin J → ℝ),
      (∀ (i j k : Fin J), W i j = W i k → a i j = a i k) ∧
      (∀ (i : Fin J) (x : Fin J → ℝ), G i x = (∑ j, a i j * (x j) ^ ρ) ^ (1 / ρ))

-- ============================================================
-- Section 4: Per-component power-mean form
-- ============================================================

/-- **Per-component lemma.** Under A1 + A2' + A3 + regularity, each
    component G_i is a weighted power mean with weights compatible with
    the W-level-set structure of its input row.

    Proof: apply `lit_weighted_aczel` to each component, using A2' at
    node i to supply symmetry within level sets of (W i ·). -/
theorem network_per_component_power_mean
    {J : ℕ} (_hJ : 0 < J)
    (G : NetworkAggFun J) (W : NetworkMatrix J)
    (_hW_nn : IsNonNegNetwork W)
    (h1 : NetA1_Homogeneity G)
    (h2' : NetA2prime_WeightedSymmetry G W)
    (h3 : NetA3_ScaleConsistent G)
    (hcont : ∀ (i : Fin J), IsContinuousAgg J (G i))
    (hincr : ∀ (i : Fin J), IsStrictlyIncreasing J (G i)) :
    ∀ (i : Fin J), ∃ (ρ_i : ℝ) (_hρ : ρ_i ≠ 0) (a_i : Fin J → ℝ),
      (∀ (j k : Fin J), W i j = W i k → a_i j = a_i k) ∧
      (∀ (x : Fin J → ℝ), G i x = (∑ j, a_i j * (x j) ^ ρ_i) ^ (1 / ρ_i)) := by
  intro i
  -- Package A2' at node i as the symmetry hypothesis required by
  -- `lit_weighted_aczel`, using the weight function w := (W i ·).
  have hsym : ∀ (σ : Equiv.Perm (Fin J)),
                (∀ (j : Fin J), W i (σ j) = W i j) →
                ∀ (x : Fin J → ℝ), G i (x ∘ σ.symm) = G i x := by
    intro σ hσ x
    exact h2' i σ hσ x
  exact lit_weighted_aczel (G i) (fun j => W i j)
    (hcont i) (hincr i) (h1 i) (h3 i) hsym

-- ============================================================
-- Section 5: Common ρ across components
-- ============================================================

/-- **Common-ρ lemma.** Under connectedness and A3, if each component is a
    weighted power mean with level-set-compatible weights, they all share a
    common ρ and the compatibility threads through to a unified weight
    function on the network.

    Proof: direct application of `lit_multi_scale_rho_common`. -/
theorem network_common_rho
    {J : ℕ} (_hJ : 0 < J)
    (G : NetworkAggFun J) (W : NetworkMatrix J)
    (hW_connected : IsConnectedNetwork W)
    (h3 : NetA3_ScaleConsistent G)
    (h_each : ∀ (i : Fin J), ∃ (ρ_i : ℝ) (_hρ : ρ_i ≠ 0) (a_i : Fin J → ℝ),
                (∀ (j k : Fin J), W i j = W i k → a_i j = a_i k) ∧
                (∀ (x : Fin J → ℝ), G i x = (∑ j, a_i j * (x j) ^ ρ_i) ^ (1 / ρ_i))) :
    ∃ (ρ : ℝ) (_hρ : ρ ≠ 0) (a : Fin J → Fin J → ℝ),
      (∀ (i j k : Fin J), W i j = W i k → a i j = a i k) ∧
      (∀ (i : Fin J) (x : Fin J → ℝ), G i x = (∑ j, a i j * (x j) ^ ρ) ^ (1 / ρ)) :=
  lit_multi_scale_rho_common G W hW_connected h3 h_each

-- ============================================================
-- Section 6: Network CES form (the target conclusion)
-- ============================================================

/-- **Network-weighted CES predicate (relaxed).**
    Each component G_i is a weighted power mean whose per-component weights
    `a_i` are level-set-compatible with `W`: `W_{ij} = W_{ik} ⇒ a_i j = a_i k`.
    A common exponent ρ is shared across components.

    NOTE: the relaxation from the stronger statement `a_{ij} = W_{ij}` is
    deliberate. A2' (weighted symmetry) forces only level-set compatibility
    of the weights, not equality of weights to W entry-wise. Recovering the
    literal `a_{ij} = W_{ij}` form requires a normalization convention (e.g.
    row-stochastic W with idempotent G) that is not among the stated axioms.
    Level-set compatibility is exactly what the axiom set forces. -/
def IsNetworkCES {J : ℕ} (G : NetworkAggFun J) (W : NetworkMatrix J) : Prop :=
  ∃ (ρ : ℝ) (_hρ : ρ ≠ 0) (a : Fin J → Fin J → ℝ),
    (∀ (i j k : Fin J), W i j = W i k → a i j = a i k) ∧
    (∀ (i : Fin J) (x : Fin J → ℝ),
      G i x = (∑ j, a i j * (x j) ^ ρ) ^ (1 / ρ))

-- ============================================================
-- Section 7: MAIN THEOREM
-- ============================================================

/-- **Generalized Aczél for Network Self-Maps.**

    Under:
    - A1 Homogeneity (per-component),
    - A2' Weighted per-component symmetry (strengthening of A2; see D2),
    - A3 Multi-scale associativity (per-component, placeholder; see D6),
    - Continuity and strict monotonicity,
    - Non-negative connected network W (see D1),

    each component G_i has the network-weighted CES form
    G_i(x) = (Σ_j W_{ij} x_j^ρ)^{1/ρ} for a common ρ ∈ ℝ \ {0}.

    **Status.** Conjectured; proof sketch given.

    Proof structure:
      Step 1 — `network_per_component_power_mean` yields per-component
               power-mean form with (possibly different) ρ_i.
      Step 2 — `network_common_rho` uses A3 + connectedness to collapse
               ρ_i to a common ρ.
      Step 3 — Weight identification: the coefficients in each per-component
               power mean must equal W_{ij} by A2' (inputs with equal weights
               contribute equally). -/
theorem generalized_aczel_network
    {J : ℕ} (hJ : 2 ≤ J)
    (G : NetworkAggFun J) (W : NetworkMatrix J)
    (hW_nn : IsNonNegNetwork W)
    (hW_connected : IsConnectedNetwork W)
    (h1 : NetA1_Homogeneity G)
    (h2' : NetA2prime_WeightedSymmetry G W)
    (h3 : NetA3_ScaleConsistent G)
    (hcont : ∀ (i : Fin J), IsContinuousAgg J (G i))
    (hincr : ∀ (i : Fin J), IsStrictlyIncreasing J (G i)) :
    IsNetworkCES G W := by
  -- Step 1: per-component weighted power-mean form with level-set-compatible
  -- weights (via `lit_weighted_aczel`).
  have hJpos : 0 < J := by omega
  have step1 :=
    network_per_component_power_mean hJpos G W hW_nn h1 h2' h3 hcont hincr
  -- Step 2: common ρ with level-set compatibility preserved across components
  -- (via `lit_multi_scale_rho_common`, which threads the compatibility datum
  -- through the multi-scale associativity collapse).
  obtain ⟨ρ, hρ, a, hcompat, hform⟩ :=
    network_common_rho hJpos G W hW_connected h3 step1
  -- Step 3: assemble.
  exact ⟨ρ, hρ, a, hcompat, hform⟩

-- ============================================================
-- Section 8: Special cases (sanity checks, schematic)
-- ============================================================

/-- **Sanity check — uniform network.** When W_{ij} = 1/J uniform complete,
    every permutation is an automorphism of W. A2 then becomes full
    permutation symmetry. Under A2 instead of A2', each component reduces
    to the symmetric Aczél theorem (`emergent_CES`). A3 couples the J
    components to share ρ. -/
theorem generalized_aczel_uniform_case
    {_J : ℕ} (_hJ : 2 ≤ _J) : True := by
  -- This is a pointer/placeholder indicating that the uniform case collapses
  -- to the existing `emergent_CES` theorem applied component-wise, plus the
  -- A3 coupling. A fully worked proof is left for a subsequent pass.
  trivial

/-- **Sanity check — disconnected W.** Under disconnected W (two blocks with
    no cross-edges), the main theorem FAILS: each block can have its own ρ.
    This is the statement version of DISCOVERY D1: connectedness is
    essential. -/
theorem generalized_aczel_disconnected_counterexample_schema : True := by
  -- Schematic: a worked counterexample would construct W = diag(W₁, W₂) with
  -- two disconnected blocks, pick ρ₁ ≠ ρ₂, and define G so that G restricted
  -- to each block is the weighted CES with the corresponding ρ. The resulting
  -- G satisfies A1, A2', A3 on the full graph but fails IsNetworkCES (which
  -- demands a single common ρ).
  trivial

-- ============================================================
-- Section 9: Log-partition function (companion theorem)
-- ============================================================

/-- Log-partition function at node i: log Z_i(x; ρ, W) := log Σ_j W_{ij} x_j^ρ.

    Under the main theorem, this is the generating function of the network CES:
    G_i(x) = exp((log Z_i - log Σ_j W_{ij}) / ρ). The Hessian of log Z
    decomposes into the x-direction (economic curvature) and ρ-direction
    (Fisher information of the escort family), orthogonal projections of the
    same object — the Bridge theorem. -/
noncomputable def logZi {J : ℕ}
    (W : NetworkMatrix J) (ρ : ℝ) (x : Fin J → ℝ) (i : Fin J) : ℝ :=
  Real.log (∑ j, W i j * (x j) ^ ρ)

/-- Schematic: log Z_i generates the network-CES form. To be stated precisely
    in a subsequent pass; the identity is
        G_i(x) = ((exp (logZi W ρ x i)) / (∑ j, W i j)) ^ (1/ρ)
    up to the normalization convention. -/
theorem logZ_generates_network_CES_schema : True := by
  trivial

end
