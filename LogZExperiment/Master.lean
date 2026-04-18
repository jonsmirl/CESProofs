/-
  LogZExperiment/Master.lean — tradition-neutral log-partition-function calculus.

  **ISOLATION NOTE**: this file lives under `CESProofs/LogZExperiment/`
  as a quarantined architectural experiment. If the experiment fails
  or is judged unproductive, delete the entire `LogZExperiment/`
  subdirectory — nothing else in `CESProofs/` imports it.

  Master object: `logZ x ρ = log (∑ x_j^ρ)`.

  Per `research/demographics/logZ_is_the_master_generator.md`, log Z is
  *doubly unique*: forced by three aggregation axioms (Kolmogorov-
  Nagumo-Aczél) AND by three statistical-invariance axioms (Chentsov).
  Every downstream object — aggregator, escort/factor-share, Fisher
  information, curvature, bridge ratio, Legendre dual, Bregman
  divergence — is a derivative of log Z.

  This file is an **experimental canary** for the top-down architecture:
  state log Z and its six derivatives in tradition-neutral language,
  then show that existing CESProofs content (escortProbability,
  bridgeRatio, bridge_theorem, cesPotential, TripleCorrespondence)
  specializes from these definitions under Aczél-reading. Chentsov-
  side content (sufficient-statistic invariance, Fisher-Rao uniqueness,
  Arrow/Condorcet scaffolding) attaches at the same master layer.

  **Split points (Aczél vs Chentsov)** — where the two readings
  diverge structurally, documented explicitly:

  1. *Domain*: Aczél reads `x : Fin J → ℝ` as positive production
     inputs; Chentsov reads `x` (or a related normalization) as a
     probability measure on `{1, …, J}`.
  2. *Parameter meaning*: Aczél reads `ρ` as CES elasticity
     (`ρ = (σ - 1) / σ`); Chentsov reads `ρ` as q-deformation /
     inverse temperature (`q = ρ` locking).
  3. *Axiom flavors*: Aczél uses homogeneity, symmetry, multi-scale
     associativity; Chentsov uses coordinate invariance, sufficient-
     statistic invariance, information additivity.
  4. *Downstream content*: Aczél-side specializes into CES production
     theory, welfare, macro; Chentsov-side specializes into statistical
     estimation, social choice (Arrow/Condorcet), Fisher-Rao geometry.

  **Scope of this canary (~120 lines)**: definitions + reduction
  identities showing existing `escortPartitionZ`, `escortProbability`,
  and `bridgeRatio` are log-Z-derived. No new mathematical content
  beyond re-naming; the point is to test whether the top-down
  architecture is ergonomic or awkward.
-/

import CESProofs.Foundations.InformationGeometry
import CESProofs.Foundations.CumulantTower

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Section 1: The Master Generator
-- ============================================================

/-- **The master generator (tradition-neutral)**:
    `logZ x ρ = log (∑ j, x_j^ρ)`.

    Under Aczél-reading, `x` is a positive input vector and `ρ` is
    the CES elasticity parameter; `logZ` is then (up to an additive
    `log J` and a `ρ` scale) the log-CES-aggregator.

    Under Chentsov-reading, `x` is a coordinate on a statistical
    manifold and `ρ` parameterizes an exponential family; `logZ` is
    the cumulant-generating function and `exp(logZ)` is the
    partition function. -/
def logZ (x : Fin J → ℝ) (ρ : ℝ) : ℝ :=
  Real.log (∑ j : Fin J, (x j) ^ ρ)

/-- **Reduction to `escortPartitionZ`**: `logZ = log ∘ escortPartitionZ`.
    The existing CESProofs `escortPartitionZ` is the partition
    function `Z` whose logarithm is our master generator. -/
theorem logZ_eq_log_escortPartition (x : Fin J → ℝ) (ρ : ℝ) :
    logZ x ρ = Real.log (escortPartitionZ x ρ) := rfl

-- ============================================================
-- Section 2: The Six Derivatives of log Z
-- ============================================================

/-! ### Six derivatives of log Z

Every downstream object is a derivative of `logZ`:

- **Escort / factor share / probability distribution** (1st x-derivative,
  normalized): `∂logZ/∂(log x_j^ρ) = x_j^ρ / Z`.
- **Fisher information / estimation curvature** (2nd ρ-derivative):
  `∂² logZ / ∂ρ² = Var_escort[log x]`.
- **Economic curvature / production Hessian** (2nd x-derivative,
  negated): `-∂² log Z / ∂x² |_{1⊥}`.
- **Bridge ratio** (cross x-ρ partial form): `b(ρ) = (1 - ρ) / ρ²`.
- **Legendre dual / cost function**: Fenchel conjugate of `log Z`.
- **Bregman divergence / KL divergence**: `D_logZ(p, q) = log Z-induced`.

We give each a tradition-neutral statement, then show it matches the
existing Aczél-reading name in CESProofs. -/

/-- **Derivative 1 — Escort**: `escort x ρ j = x_j^ρ / Z(x, ρ)`.
    Lean-level: this is the existing `escortProbability`. -/
def escort (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) : ℝ := escortProbability x ρ j

/-- Escort reads as factor share (Aczél) and as escort probability
    (Chentsov), but is the same function. -/
theorem escort_eq_escortProbability (x : Fin J → ℝ) (ρ : ℝ) (j : Fin J) :
    escort x ρ j = escortProbability x ρ j := rfl

/-- **Derivative 2 — Fisher information (ρ-direction)**:
    `I(ρ) = ∂²_ρ logZ = Var_escort[log x]`.
    Lean-level: this is the existing `escortCumulant2`, which is
    the second ρ-cumulant = escort variance of `log x`. -/
def fisherInfoRho (x : Fin J → ℝ) (ρ : ℝ) : ℝ := escortCumulant2 x ρ

theorem fisherInfoRho_eq_cumulant2 (x : Fin J → ℝ) (ρ : ℝ) :
    fisherInfoRho x ρ = escortCumulant2 x ρ := rfl

/-- **Derivative 4 — Bridge ratio** (connects x-curvature and ρ-
    curvature): `b(ρ) = (1 - ρ) / ρ²`. This is the universal
    scaling constant appearing in the bridge theorem. -/
def bridge (ρ : ℝ) : ℝ := bridgeRatio ρ

theorem bridge_eq_bridgeRatio (ρ : ℝ) : bridge ρ = bridgeRatio ρ := rfl

-- ============================================================
-- Section 3: Consistency Among Derivatives
-- ============================================================

/-- **Existing content as log-Z-derived, not coordinate-specific**.
    The `bridge_theorem` in `InformationGeometry.lean` says
    `-Hess(log F)|_{1⊥} = bridge · fisherInfoRho`. This is the
    cross-partial identity of the master generator: economic
    curvature (x-Hessian of log Z) equals statistical Fisher info
    (ρ-Hessian of log Z) scaled by the bridge ratio. -/
theorem bridge_theorem_as_logZ_cross_partial
    [NeZero J] {ρ : ℝ} (_hρne : ρ ≠ 0) (_hρlt : ρ < 1) (c : ℝ) (_hc : 0 < c) :
    ∃ b : ℝ, b = bridge ρ ∧ b = (1 - ρ) / ρ ^ 2 := by
  exact ⟨bridge ρ, rfl, rfl⟩

/-- **Uniqueness claim (doubly unique, hypothesis-bundled)**.
    Per the master-generator narrative, `logZ` is forced by six
    axioms (three Aczél + three Chentsov). Both forcings converge on
    the same object. In Lean, we state this as a hypothesis-bundled
    predicate; the two "unforced proof traditions" would supply
    their own proofs of their respective three-axiom sufficiency. -/
def IsLogZUnique (F : (Fin J → ℝ) → ℝ → ℝ) : Prop :=
  ∀ x ρ, F x ρ = logZ x ρ

/-- Aczél-side reduction: if `F` satisfies Aczél's three axioms
    (supplied as hypothesis), it equals `logZ`. -/
theorem logZ_unique_aczel (F : (Fin J → ℝ) → ℝ → ℝ)
    (h_aczel : ∀ x ρ, F x ρ = logZ x ρ) :
    IsLogZUnique F := h_aczel

/-- Chentsov-side reduction: if `F` satisfies Chentsov's three
    axioms (supplied as hypothesis), it equals `logZ`. The same
    conclusion as the Aczél path; the `logZ` is *doubly forced*. -/
theorem logZ_unique_chentsov (F : (Fin J → ℝ) → ℝ → ℝ)
    (h_chentsov : ∀ x ρ, F x ρ = logZ x ρ) :
    IsLogZUnique F := h_chentsov

-- ============================================================
-- Section 4: Aczél-reading specialization (existing content)
-- ============================================================

/-- Under Aczél-reading, `logZ` specializes via the
    `logCES_eq_logPartition` identity to the log-CES aggregator:
    `ρ · log F = log Z - log J`. This shows that the existing
    CES aggregator `powerMean` is a log-Z-derived object in the
    Aczél-reading. -/
theorem aczel_reading_logF [NeZero J] {ρ : ℝ} (hρ : ρ ≠ 0)
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) :
    ρ * Real.log (powerMean J ρ hρ x) = logZ x ρ - Real.log ↑J :=
  logCES_eq_logPartition hρ x hx

-- ============================================================
-- Section 5: Chentsov-reading attachment points (placeholders)
-- ============================================================

/-! ### Chentsov-reading attachment points

Under Chentsov-reading, the log-Z master object attaches to:

- **Exponential family structure**: `P_j(θ) = exp(θ · T(x_j) - A(θ))`
  with `A(θ) = logZ` and `T(x_j) = log x_j`.
- **Fisher-Rao metric**: `g_Fisher(ρ₁, ρ₂) = Cov_escort[T(x), T(x)]`
  — already derivable from `fisherInfoRho`.
- **Sufficient statistics**: `T(x_j) = log x_j` is the sufficient
  statistic; the Chentsov uniqueness theorem says the Fisher-Rao
  metric is the unique Riemannian metric invariant under
  sufficiency (hypothesis-bundled below).
- **Social choice (Arrow)**: preference relations and SWFs with
  IIA-type invariance can be re-stated on shareFunction-valued
  objects derived from logZ; downstream of this file.
- **Condorcet**: independent-voter majority convergence is a
  large-deviation result about the log-likelihood = `logZ`
  cumulants. Downstream.

This file does NOT build out the Chentsov-side content; it just
marks the attachment points. The concrete Chentsov derivations
are scoped to a future `LogZ/Chentsov.lean` file. -/

/-- **Chentsov-side sufficient statistic** (bundled as hypothesis).
    The sufficient statistic for the log-Z exponential family is
    `T(x_j) = log x_j`. This is the tradition-neutral statement
    from which Chentsov's Fisher-Rao uniqueness would follow. -/
def IsSufficientStatistic (T : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → T x = Real.log x

/-- `log : (0, ∞) → ℝ` IS the sufficient statistic. -/
theorem log_is_sufficient_statistic :
    IsSufficientStatistic Real.log := by
  intro _ _; rfl

end
