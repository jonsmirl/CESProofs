/-
  Endogenous Hierarchy: Network CES ↔ Spectral Hierarchy Bridge

  Resolves Gap 9 ("Why N levels?") by connecting Gap 4 (Network CES,
  heterogeneous pairwise complementarity) to the spectral hierarchy
  theory (Paper4/SpectralHierarchy.lean).

  Central insight (Simon 1962, formalized):
  The hierarchy IS the spectral decomposition of the network CES.
  - Network CES = microscopic view (full Laplacian L)
  - Hierarchical CES = macroscopic view (projection onto N eigenspaces)

  Key algebraic result (proved without eigenvalue theory):
  L(v) = L_intra(v) + L_inter(v) for ANY partition into N levels.
  The intra-level QF captures fast within-block dynamics;
  the inter-level QF captures slow between-block coupling.

  Near-decomposability (ε-bounded inter-level coupling) implies
  the inter-level QF is O(ε), making the hierarchy emergent.

  Nobel connections:
  - Simon: near-decomposability → hierarchy (Architecture of Complexity)
  - Williamson: transaction costs → spectral gaps → more levels
  - North: institutional layers add spectral gaps sequentially
  - Ostrom: polycentric governance = soft spectral clustering

  Results: 19 theorems (15 fully proved, 4 schematic), 0 axioms.
-/

import CESProofs.CurvatureRoles.NetworkCES
import CESProofs.Hierarchy.SpectralHierarchy

open Real Finset BigOperators

noncomputable section

variable {J N : ℕ}

-- ============================================================
-- Section 1: Hierarchical Partition
-- ============================================================

/-- A hierarchical partition assigns each of J sectors to one of N levels.
    In Simon's framework: each sector belongs to one "nearly decomposable block."
    For soft clustering (Ostrom's polycentricity), see overlapWeight in
    SpectralHierarchy.lean. -/
structure HierarchicalPartition (J : ℕ) (N : ℕ) where
  level : Fin J → Fin N
  nonempty_levels : ∀ n : Fin N, ∃ j : Fin J, level j = n

-- ============================================================
-- Section 2: Intra/Inter Level QF
-- ============================================================

/-- Intra-level Laplacian QF: sum over sector pairs within the SAME level.
    Captures "fast" within-block adjustment dynamics (high eigenvalues).
    In the singular perturbation framework: these are the O(1/ε) modes. -/
def intraLevelQF (net : ComplementarityNetwork J) (P : HierarchicalPartition J N)
    (v : Fin J → ℝ) : ℝ :=
  (1 / 2) * ∑ j : Fin J, ∑ k : Fin J,
    (if P.level j = P.level k then net.w j k else 0) * (v j - v k) ^ 2

/-- Inter-level Laplacian QF: sum over sector pairs in DIFFERENT levels.
    Captures "slow" between-block coupling dynamics (low eigenvalues).
    In the singular perturbation framework: these are the O(ε) modes. -/
def interLevelQF (net : ComplementarityNetwork J) (P : HierarchicalPartition J N)
    (v : Fin J → ℝ) : ℝ :=
  (1 / 2) * ∑ j : Fin J, ∑ k : Fin J,
    (if P.level j ≠ P.level k then net.w j k else 0) * (v j - v k) ^ 2

-- ============================================================
-- Theorems: QF Decomposition (Simon's Near-Decomposability)
-- ============================================================

/-- **EH-1**: QF decomposition theorem (Simon's algebraic core).
    The network Laplacian QF decomposes exactly into within-level
    and between-level components for ANY partition:

    L(v) = L_intra(v) + L_inter(v)

    This is the algebraic content of Simon (1962) "The Architecture
    of Complexity": the dynamics of a nearly decomposable system
    separate into fast (intra-block) and slow (inter-block) components,
    determined by the modular structure.

    The decomposition is EXACT for any partition — the "quality"
    of a partition is measured by how small L_inter is relative to L. -/
theorem qf_decomposition (net : ComplementarityNetwork J) (P : HierarchicalPartition J N)
    (v : Fin J → ℝ) :
    laplacianQF net v = intraLevelQF net P v + interLevelQF net P v := by
  simp only [laplacianQF, intraLevelQF, interLevelQF]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro k _
  by_cases h : P.level j = P.level k <;> simp [h]

/-- **EH-2**: Intra-level QF is non-negative (for complementary networks).
    The within-block adjustment cost is always non-negative when
    all pairwise complementarities are positive (ρ_{jk} ≤ 1). -/
theorem intraLevelQF_nonneg (net : ComplementarityNetwork J)
    (hw : ∀ j k, 0 ≤ net.w j k)
    (P : HierarchicalPartition J N) (v : Fin J → ℝ) :
    0 ≤ intraLevelQF net P v := by
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  apply Finset.sum_nonneg; intro j _
  apply Finset.sum_nonneg; intro k _
  apply mul_nonneg _ (sq_nonneg _)
  by_cases h : P.level j = P.level k <;> simp [h, hw j k]

/-- **EH-3**: Inter-level QF is non-negative (for complementary networks).
    The between-block coupling cost is always non-negative. -/
theorem interLevelQF_nonneg (net : ComplementarityNetwork J)
    (hw : ∀ j k, 0 ≤ net.w j k)
    (P : HierarchicalPartition J N) (v : Fin J → ℝ) :
    0 ≤ interLevelQF net P v := by
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  apply Finset.sum_nonneg; intro j _
  apply Finset.sum_nonneg; intro k _
  apply mul_nonneg _ (sq_nonneg _)
  by_cases h : P.level j ≠ P.level k <;> simp [h, hw j k]

-- ============================================================
-- Theorems: Boundary Cases
-- ============================================================

/-- **EH-4**: With a single level (N=1), the inter-level QF is zero.
    No hierarchy = no between-block dynamics. All adjustment is
    within-block. The economy is a "flat" system.

    This is the antithesis of Simon: without modular structure,
    there is no hierarchy and no timescale separation. -/
theorem single_level_inter_zero (net : ComplementarityNetwork J)
    (P : HierarchicalPartition J 1) (v : Fin J → ℝ) :
    interLevelQF net P v = 0 := by
  simp only [interLevelQF, ne_eq]
  convert mul_zero (1 / 2 : ℝ)
  apply Finset.sum_eq_zero; intro j _
  apply Finset.sum_eq_zero; intro k _
  have : P.level j = P.level k := Subsingleton.elim _ _
  simp [this]

/-- A disconnected partition has zero coupling between all cross-level pairs. -/
def isDisconnected (net : ComplementarityNetwork J) (P : HierarchicalPartition J N) : Prop :=
  ∀ j k : Fin J, P.level j ≠ P.level k → net.w j k = 0

/-- **EH-5**: Disconnected components → zero inter-level QF.
    When different levels have no coupling (w_{jk} = 0 for j,k in
    different levels), the economy decomposes into independent blocks.
    Each block evolves autonomously — there is no cross-level influence.

    Economically: if sectors in different levels don't interact at all,
    the hierarchy is purely organizational, not dynamical. -/
theorem disconnected_inter_zero (net : ComplementarityNetwork J)
    (P : HierarchicalPartition J N) (v : Fin J → ℝ)
    (hdisc : isDisconnected net P) :
    interLevelQF net P v = 0 := by
  simp only [interLevelQF, ne_eq]
  convert mul_zero (1 / 2 : ℝ)
  apply Finset.sum_eq_zero; intro j _
  apply Finset.sum_eq_zero; intro k _
  by_cases h : P.level j = P.level k
  · simp [h]
  · simp [h, hdisc j k h]

-- ============================================================
-- Theorems: Near-Decomposability
-- ============================================================

/-- Near-decomposable network: all cross-level coupling bounded by ε.
    Small ε means the economy is nearly modular — strong intra-level
    coupling, weak inter-level coupling (Simon's key assumption). -/
def isNearDecomposable (net : ComplementarityNetwork J)
    (P : HierarchicalPartition J N) (ε : ℝ) : Prop :=
  ∀ j k : Fin J, P.level j ≠ P.level k → net.w j k ≤ ε

/-- **EH-6**: Near-decomposability bounds inter-level coupling pointwise.
    If all cross-level weights are ≤ ε, then each cross-level term
    in the Laplacian QF is bounded by ε times the squared difference.

    This is the mechanism through which hierarchy EMERGES:
    small ε → small inter-level QF → timescale separation →
    fast intra-level dynamics + slow inter-level dynamics. -/
theorem near_decomposable_pointwise (net : ComplementarityNetwork J)
    (P : HierarchicalPartition J N) (ε : ℝ)
    (hnd : isNearDecomposable net P ε) (v : Fin J → ℝ) (j k : Fin J)
    (hne : P.level j ≠ P.level k) :
    net.w j k * (v j - v k) ^ 2 ≤ ε * (v j - v k) ^ 2 :=
  mul_le_mul_of_nonneg_right (hnd j k hne) (sq_nonneg _)

-- ============================================================
-- Theorems: Connection to Network CES
-- ============================================================

/-- **EH-7**: Network-hierarchy bridge theorem.
    A ComplementarityNetwork defines both:
    (a) the Laplacian QF (network curvature, Gap 4)
    (b) the intra/inter decomposition (hierarchical structure, Gap 9)

    These are the SAME object at different scales:
    - Network CES = microscopic (the full matrix L)
    - Hierarchical CES = macroscopic (L_intra + L_inter decomposition)

    The "good" partition minimizes L_inter/L, recovering the
    spectral clustering that defines the hierarchy. -/
theorem network_hierarchy_bridge (net : ComplementarityNetwork J)
    (hw : ∀ j k, 0 ≤ net.w j k)
    (P : HierarchicalPartition J N) (v : Fin J → ℝ) :
    laplacianQF net v = intraLevelQF net P v + interLevelQF net P v ∧
    0 ≤ intraLevelQF net P v ∧
    0 ≤ interLevelQF net P v :=
  ⟨qf_decomposition net P v,
   intraLevelQF_nonneg net hw P v,
   interLevelQF_nonneg net hw P v⟩

/-- **EH-8**: Intra-level QF is bounded by total QF.
    Since L = L_intra + L_inter and L_inter ≥ 0:
    L_intra ≤ L. The within-block dynamics never exceed the total.

    Equivalently: the "fast" adjustment cost is bounded by the
    total adjustment cost. Removing inter-level coupling can only
    REDUCE the Laplacian QF, never increase it. -/
theorem intra_bounded_by_total (net : ComplementarityNetwork J)
    (hw : ∀ j k, 0 ≤ net.w j k)
    (P : HierarchicalPartition J N) (v : Fin J → ℝ) :
    intraLevelQF net P v ≤ laplacianQF net v := by
  rw [qf_decomposition net P v]
  linarith [interLevelQF_nonneg net hw P v]

-- ============================================================
-- Section 5: Effective Curvature per Level
-- ============================================================

/-- Number of sectors assigned to level n. -/
def levelSize (P : HierarchicalPartition J N) (n : Fin N) : ℕ :=
  (Finset.univ.filter fun j : Fin J => P.level j = n).card

/-- Total intra-level coupling strength for level n:
    sum of complementarity weights within the level. -/
def levelCoupling (net : ComplementarityNetwork J) (P : HierarchicalPartition J N)
    (n : Fin N) : ℝ :=
  ∑ j : Fin J, ∑ k : Fin J,
    if P.level j = n ∧ P.level k = n ∧ j ≠ k then net.w j k else 0

/-- Effective curvature for level n: mean intra-level complementarity.
    Analogous to K = (1-ρ)(J-1)/J for the whole economy, but restricted
    to sectors within level n. Higher value → stronger complementarity
    within the level → lower effective ρ_n. -/
def effectiveLevelCurvature (net : ComplementarityNetwork J)
    (P : HierarchicalPartition J N) (n : Fin N) : ℝ :=
  let J_n := levelSize P n
  if J_n ≤ 1 then 0
  else levelCoupling net P n / (↑J_n * (↑J_n - 1))

/-- **EH-9**: Effective level curvature is non-negative
    for complementary networks. -/
theorem effectiveLevelCurvature_nonneg (net : ComplementarityNetwork J)
    (hw : ∀ j k, 0 ≤ net.w j k)
    (P : HierarchicalPartition J N) (n : Fin N) :
    0 ≤ effectiveLevelCurvature net P n := by
  simp only [effectiveLevelCurvature, levelCoupling]
  split
  · exact le_refl 0
  · rename_i h; push_neg at h
    apply div_nonneg
    · apply Finset.sum_nonneg; intro j _
      apply Finset.sum_nonneg; intro k _
      by_cases hc : P.level j = n ∧ P.level k = n ∧ j ≠ k
      · simp [hc, hw j k]
      · simp [hc]
    · have hJn : (2 : ℝ) ≤ ↑(levelSize P n) := by
        exact_mod_cast (show 2 ≤ levelSize P n by omega)
      exact le_of_lt (mul_pos (by linarith) (by linarith))

-- ============================================================
-- Section 6: Derived Definitions
-- ============================================================

/-- Recover ρ_n from effective curvature: ρ_n = 1 - K_n.
    For uniform networks with 1 level, this recovers ρ.
    See `uniform_effectiveLevelRho_trivial` for the proved algebraic core. -/
def effectiveLevelRho (net : ComplementarityNetwork J)
    (P : HierarchicalPartition J N) (n : Fin N) : ℝ :=
  1 - effectiveLevelCurvature net P n

/-- Cross-level distance quadratic form: unweighted sum of squared
    differences across levels. Measures the "amount of cross-level variation"
    independent of coupling strength. Used to bound inter-level QF
    in near-decomposable networks. -/
def crossLevelDistQF (P : HierarchicalPartition J N) (v : Fin J → ℝ) : ℝ :=
  (1 / 2) * ∑ j : Fin J, ∑ k : Fin J,
    (if P.level j ≠ P.level k then 1 else 0) * (v j - v k) ^ 2

-- ============================================================
-- Theorems: Near-Decomposable Approximation Quality
-- ============================================================

/-- **EH-9a**: Cross-level distance QF is non-negative. -/
theorem crossLevelDistQF_nonneg (P : HierarchicalPartition J N) (v : Fin J → ℝ) :
    0 ≤ crossLevelDistQF P v := by
  apply mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2)
  apply Finset.sum_nonneg; intro j _
  apply Finset.sum_nonneg; intro k _
  apply mul_nonneg _ (sq_nonneg _)
  by_cases h : P.level j ≠ P.level k <;> simp [h]

/-- **EH-9b**: Near-decomposable → inter-level QF bounded by ε times cross-level distance.
    This is the quantitative content of Simon's near-decomposability:
    weak inter-level coupling (all cross-level weights ≤ ε) implies
    inter-level dynamics are O(ε). The hierarchy approximation quality
    is controlled by the near-decomposability parameter.

    Proved algebraically without eigenvalue theory. -/
theorem hierarchy_approximation_quality (net : ComplementarityNetwork J)
    (P : HierarchicalPartition J N) {ε : ℝ} (_hε : 0 ≤ ε)
    (hnd : isNearDecomposable net P ε) (v : Fin J → ℝ) :
    interLevelQF net P v ≤ ε * crossLevelDistQF P v := by
  unfold interLevelQF crossLevelDistQF
  set A := ∑ j : Fin J, ∑ k : Fin J,
    (if P.level j ≠ P.level k then net.w j k else 0) * (v j - v k) ^ 2
  set B := ∑ j : Fin J, ∑ k : Fin J,
    (if P.level j ≠ P.level k then (1:ℝ) else 0) * (v j - v k) ^ 2
  -- Reduce to pointwise bound on inner sums
  suffices hAB : A ≤ ε * B by
    calc 1 / 2 * A ≤ 1 / 2 * (ε * B) := mul_le_mul_of_nonneg_left hAB (by norm_num)
      _ = ε * (1 / 2 * B) := by ring
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro k _
  by_cases h : P.level j ≠ P.level k
  · rw [if_pos h, if_pos h, one_mul]
    exact mul_le_mul_of_nonneg_right (hnd j k h) (sq_nonneg _)
  · push_neg at h; simp [h]

/-- **EH-9c**: Corollary: total QF minus intra-level QF is O(ε).
    The hierarchy (intra-level QF) approximates the full network (total QF)
    with error bounded by ε times the cross-level distance. -/
theorem near_decomposable_intra_approximation (net : ComplementarityNetwork J)
    (_hw : ∀ j k, 0 ≤ net.w j k)
    (P : HierarchicalPartition J N) {ε : ℝ} (hε : 0 ≤ ε)
    (hnd : isNearDecomposable net P ε) (v : Fin J → ℝ) :
    laplacianQF net v - intraLevelQF net P v ≤ ε * crossLevelDistQF P v := by
  have hdecomp := qf_decomposition net P v
  linarith [hierarchy_approximation_quality net P hε hnd v]

-- ============================================================
-- Theorems: Uniform Network Recovery
-- ============================================================

/-- **EH-9d**: For uniform network with 1-level partition, total coupling = J(J-1)(1-ρ).
    All sectors are in the same level, and each pair contributes weight (1-ρ). -/
theorem uniform_levelCoupling_trivial (_hJ : 2 ≤ J) (ρ : ℝ)
    (P : HierarchicalPartition J 1) (n : Fin 1) :
    levelCoupling (uniformNetwork J ρ) P n = ↑J * (↑J - 1) * (1 - ρ) := by
  simp only [levelCoupling, uniformNetwork]
  -- In Fin 1, all levels equal: conditions become j ≠ k
  have hcond : ∀ (j k : Fin J),
      (if P.level j = n ∧ P.level k = n ∧ j ≠ k
       then (if j = k then (0 : ℝ) else 1 - ρ) else 0) =
      if j ≠ k then (1 - ρ) else 0 := by
    intro j k
    have hj := Subsingleton.elim (P.level j) n
    have hk := Subsingleton.elim (P.level k) n
    by_cases hjk : j = k <;> simp [hj, hk, hjk]
  simp_rw [hcond]
  -- Count: ∑ j, ∑ k, if j ≠ k then (1-ρ) else 0 = J*(J-1)*(1-ρ)
  -- Handle inner sum first to avoid simp_rw applying at both levels
  have inner : ∀ j : Fin J,
      ∑ k : Fin J, (if j ≠ k then (1 - ρ) else (0 : ℝ)) = (↑J - 1) * (1 - ρ) := by
    intro j
    have : ∀ k : Fin J, (if j ≠ k then (1 - ρ) else (0 : ℝ)) =
        (1 - ρ) - if j = k then (1 - ρ) else 0 := by
      intro k; by_cases h : j = k <;> simp [h]
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  simp_rw [inner, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **EH-9e**: For uniform network with 1-level partition, effective curvature = 1-ρ.
    Recovers the standard CES curvature from the network framework. -/
theorem uniform_effectiveLevelCurvature_trivial (hJ : 2 ≤ J) (ρ : ℝ)
    (P : HierarchicalPartition J 1) (n : Fin 1) :
    effectiveLevelCurvature (uniformNetwork J ρ) P n = 1 - ρ := by
  have hls : levelSize P n = J := by
    simp only [levelSize]
    rw [Finset.filter_true_of_mem (fun j _ => Subsingleton.elim (P.level j) n)]
    rw [Finset.card_univ, Fintype.card_fin]
  unfold effectiveLevelCurvature
  dsimp only
  simp only [hls]
  rw [if_neg (show ¬(J ≤ 1) from by omega)]
  rw [uniform_levelCoupling_trivial hJ ρ P n]
  have hne : (↑J : ℝ) * ((↑J : ℝ) - 1) ≠ 0 := by
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (by omega)
    · have : (1:ℝ) < ↑J := by exact_mod_cast (show 1 < J by omega)
      linarith
  exact mul_div_cancel_left₀ (1 - ρ) hne

/-- **EH-9f**: For uniform network with 1-level partition, effective ρ = ρ.
    The hierarchy recovers the underlying network parameter:
    the proved algebraic core of EH-12. -/
theorem uniform_effectiveLevelRho_trivial (hJ : 2 ≤ J) (ρ : ℝ)
    (P : HierarchicalPartition J 1) (n : Fin 1) :
    effectiveLevelRho (uniformNetwork J ρ) P n = ρ := by
  simp only [effectiveLevelRho, uniform_effectiveLevelCurvature_trivial hJ ρ P n]
  ring

-- ============================================================
-- Theorems: Spectral Structure (Schematic)
-- ============================================================

/-- **EH-10**: Eigenvalue clustering implies natural partition.
    If the Laplacian eigenvalues cluster into N groups separated by
    spectral gaps exceeding threshold γ, the economy has a natural
    N-level hierarchical structure.

    The partition is determined by eigenvector signs/magnitudes
    (spectral clustering, Fiedler vector generalization).

    **Proof.** By spectral clustering theory (von Luxburg 2007): if
    the Laplacian eigenvalues λ₁ ≤ λ₂ ≤ ⋯ have N clusters separated
    by gaps exceeding threshold γ, the eigenvectors of the N smallest
    eigenvalues define indicator vectors for a natural N-level partition.
    The gap condition λ_{k+1} - λ_k > γ ensures the partition is robust
    to perturbation (Davis-Kahan theorem). Schematic: spectral clustering
    theorem not in Mathlib. -/
theorem eigenvalue_clustering_partition
    {M : ℕ} (_spec : OrderedSpectrum M) (_γ : ℝ)
    (_hs : HierarchySpec M) (_hj : _hs.isJustified _spec _γ) :
    True := trivial

/-- **EH-11**: Optimal N maximizes spectral gap quality.
    The "right" number of hierarchical levels is the one that
    maximizes the total spectral gap quality — the sum of
    gap ratios at the declared gap positions.

    **Proof.** Define the spectral gap quality for a partition into $N$ levels as $Q(N) = \sum_{k \in \text{gaps}} (\lambda_{k+1} - \lambda_k)/\lambda_k$, where the sum runs over the $N-1$ declared gap positions in the ordered Laplacian spectrum $\lambda_1 \le \lambda_2 \le \cdots \le \lambda_M$. The optimal $N^*$ maximizes $Q(N)$ over all possible gap placements and all $N \le M$. Since $Q(N)$ is bounded above (the total spectral range is finite) and the search space is finite (at most $\binom{M-1}{N-1}$ placements for each $N$), a maximizer exists. Adding a level at a position with a small gap ratio contributes little to $Q$ while increasing information cost, so $N^*$ balances parsimony against near-decomposability fidelity. -/
theorem optimal_N_spectral
    {M : ℕ} (_spec : OrderedSpectrum M) :
    True := trivial

/-- **EH-12**: Each spectral cluster defines an effective ρ per level.
    The eigenvalues within cluster n determine the effective curvature
    K_n and hence the effective ρ_n = 1 - K_n·J_n/(J_n-1) for that level.

    This connects the spectral hierarchy to HierarchicalCESEconomy:
    the ρ_n parameters are not free but emerge from the network.

    **Proof.** For each spectral cluster n, the mean intra-cluster
    eigenvalue μ̄_n determines the effective curvature K_n = μ̄_n · J_n/(J_n - 1)
    and hence ρ_n = 1 - K_n. The proved algebraic core
    (`uniform_effectiveLevelRho_trivial`) confirms that for uniform
    networks with 1 level, this recovers ρ exactly. Schematic: mapping
    eigenvalue clusters to CES parameters for general networks requires
    the full secular equation. -/
theorem effective_rho_from_clustering
    {M : ℕ} (_spec : OrderedSpectrum M) :
    True := trivial

/-- **EH-13**: Grand unification — Network CES = Hierarchical CES.
    The network CES (Gap 4) and the hierarchical CES (Gap 9) are the
    SAME mathematical object viewed at different scales:

    - Network CES: the full Laplacian L on J sectors
    - Hierarchical CES: the coarse-grained projection of L onto
      N spectral clusters, each with its own effective ρ_n and ε_n

    The projection is:
    - L ↦ (L_intra^{(1)}, ..., L_intra^{(N)}, L_inter)
    - Effective parameters: ρ_n from intra-level eigenvalues,
      ε_n from the spectral gap below level n

    The HierarchicalCESEconomy with N levels is the leading-order
    approximation of the network CES, valid when L_inter << L_intra
    (i.e., the economy is nearly decomposable with ε << 1).

    **Proof.** The network CES with full Laplacian L and the hierarchical
    CES with N effective parameters (ρ_n, ε_n) are related by spectral
    projection: L ↦ (L_intra^{(1)}, …, L_intra^{(N)}, L_inter). The
    proved bound (`hierarchy_approximation_quality`) shows L_inter ≤ ε · D
    where D is the cross-level distance QF, making the hierarchy a
    leading-order approximation valid when ε ≪ 1 (near-decomposable).
    Schematic: full spectral projection theory not in Mathlib. -/
theorem hierarchy_is_spectral_decomposition
    (net : ComplementarityNetwork J) (P : HierarchicalPartition J N)
    (_hnd : ∃ ε, ε < 1 ∧ isNearDecomposable net P ε) :
    True := trivial

end
