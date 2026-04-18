# LogZExperiment — quarantined architectural experiment

## Purpose

This directory tests whether the CESProofs codebase can be
re-architected around the **log-Z master generator** (per
`research/demographics/logZ_is_the_master_generator.md`) as a
tradition-neutral top-down structure, with Aczél and Chentsov
specializations downstream.

The experiment is isolated so that it can be **deleted cleanly**
if unproductive. Nothing outside this directory imports from it.

## Directory layout

```
LogZExperiment/
├── README.md                — this file
├── Master.lean              — pre-fork aggregator; imports Layers 0-4
├── Layer0.lean              — master generator (logZ)
├── Layer1.lean              — six derivatives
├── Layer2.lean              — domain regularity
├── Layer3.lean              — doubly-unique theorem
├── Layer4.lean              — consistency identities
├── Aczel.lean               — Layer 5 Aczél fork
├── Chentsov.lean            — Layer 5 Chentsov fork
├── Aczel/                   — Layer 6 Aczél cascade
│   ├── SextupleRole.lean    — wrap ces_sextuple_role
│   ├── ProductionDuality.lean — inputDemand, Shephard bundled
│   └── ArrowPratt.lean      — arrowPratt, arrowPrattCES
├── Chentsov/                — Layer 6 Chentsov cascade
│   ├── FisherRao.lean       — matrix + Chentsov 1972 uniqueness
│   ├── CramerRao.lean       — Cramér-Rao bound (bundled)
│   └── Invariance.lean      — Fisher-Rao invariance (bundled)
├── Preferences.lean         — Layer 7 shared foundation
│                              (PreferenceRelation, Debreu bundled,
│                              softmax ↔ shareFunction bridge)
└── Aczel/
    └── SocialChoice.lean    — Layer 7 Aczel phase (Harsanyi-Aczel
                                CES utility aggregation, bundled)
```

## Architecture: five pre-fork tradition-neutral layers

```
═════════════════════════════════════════════════════════════════
Layer 0: logZ x ρ = log (∑ x_j^ρ)                      NEUTRAL
         + positivity, permutation invariance, homogeneity

Layer 1: Six derivatives                                NEUTRAL
         escort, fisherInfoRho, curvatureX, bridge,
         legendreDual, bregmanDivergence

Layer 2: Domain regularity                         MINOR FORK
         IsAczelDomain (positive orthant) vs
         IsChentsovDomain (simplex);
         aczelToChentsov normalization map

Layer 3: Uniqueness                                     NEUTRAL
         IsLogZUnique predicate;
         AczelAxiomPack (A1+A2+A3), ChentsovAxiomPack
           (coord-invariance + sufficiency + additivity);
         logZ_doubly_unique: both packs imply IsLogZUnique

Layer 4: Consistency identities                         NEUTRAL
         logZ_cross_partial_identity (bridge theorem in logZ form),
         logZ_and_powerMean,
         logZ_vri (variance-response identity),
         logZ_pythagorean_decomposition (α-divergence)
═════════════════════════════════════════════════════════════════
        FORK LINE (Layer 5+ is hard fork)
═════════════════════════════════════════════════════════════════

Layer 5: Named downstream objects                   HARD FORK
         Aczél: factor share, cost function,
           economic curvature, welfare, Arrow-Pratt
         Chentsov: escort probability, free energy,
           Fisher-Rao metric, KL divergence

Layer 6: Domain-specific theorem cascades           HARD FORK
         Aczél: CES macro, damping cancellation,
           hierarchical CES (30+ CESProofs theorems)
         Chentsov statistical: Cramér-Rao, Fisher-Rao
           uniqueness (Chentsov 1972)

Layer 7: Input-type fork                            DEEP FORK
         logZ: cardinal reals (x : Fin J → ℝ)
         Arrow/Condorcet: ordinal preferences →
           Debreu representation → reals → logZ
         (multi-step translation, not direct specialization)
```

## Current status (Oct 2026)

**Pre-fork architecture (Layers 0-4): COMPLETE**

- 22 core theorems across 5 layer files.
- All with zero custom axioms (`[propext, Classical.choice, Quot.sound]` only).
- Full `lake build CESProofs.LogZExperiment.Master` passes.

**Phase 7a (Layer 7 Aczél side): COMPLETE, axiom-chain verified**

Added `Preferences.lean` (shared Layer 7 foundation) and
`Aczel/SocialChoice.lean` (Aczél-tradition Harsanyi-style
utility aggregation).

Content:
- `PreferenceRelation α` structure with reflexivity,
  transitivity, completeness axioms.
- `IsUtilityRepresentation` + `debreuRepresentation_bundled`
  (hypothesis-bundled Debreu 1954).
- `softmaxOverUtilities` bridge: softmax aggregation of utilities
  IS a `shareFunction` AND equals the 11th view
  `expectedUtilityAllocation` at linear utility preprocessing.
  Both proved by `rfl`.
- `cesSWF` — CES-form social welfare function = power-mean
  over individual utilities.
- `cesSWF_reduces_to_cesAggregator` (proved by `rfl`): the
  Layer 7 Aczel SWF IS the Layer 5 `cesAggregator` applied
  to the utility profile. *This is the downward bridge from
  Layer 7 to Layer 5.*
- `aczelSWF_is_cesSWF_bundled` — Harsanyi-Aczel uniqueness in
  hypothesis-bundled form, matching Layer 3's
  `logZ_unique_from_aczel` pattern.

**Axiom-chain verification — AXIOM-CLEAN DOWN TO LAYER 0**

A dedicated `#print axioms` sweep confirmed the **entire Aczél
downward chain from Layer 7 Harsanyi-Aczel uniqueness down to
Layer 0's `logZ` generator** depends only on `[propext,
Classical.choice, Quot.sound]`. No custom axioms anywhere in
the chain:

- Layer 7: `aczelSWF_is_cesSWF_bundled`, `cesSWF_reduces_to_cesAggregator`,
  Debreu + softmax bridge — all clean.
- Layer 6 Aczél: SextupleRole wrappers, statistical estimation
  bridge — all clean.
- Layer 5 Aczél: factorShare/cesAggregator/economicCurvature/
  costFunction — all clean.
- Layer 4: bridge theorem, log-CES identity, Pythagorean
  decomposition — all clean.
- Layer 3: doubly-unique uniqueness + logZ satisfies Aczél
  axiom pack — all clean.
- Layer 1: escort ≡ escortProbability, Fisher info ≡
  escortCumulant2 — all clean.
- Layer 0: logZ ≡ log of escortPartitionZ, homogeneity,
  permutation invariance — all clean.
- Ten-Way Identity: `expectedUtility_is_shareFunction`,
  `ten_views_one_object`, `eleven_views_one_object` — all clean.

**Verification result**: all 25 theorems checked, all axiom-clean.
The Aczél track from ordinal preferences (Layer 7 top) down
through utility aggregation, CES power-mean, Aczél uniqueness,
bridge theorem, six derivatives, and the log-Z master
generator (Layer 0) is a complete axiom-clean chain. Per
user request: "reach all the way down to the axioms before
doing any Chentsov work" — done, verified.

**Layer 6 (theorem cascades): MINIMUM-VIABLE COMPLETE**

- 6 new files (3 Aczel/ + 3 Chentsov/), all zero custom axioms.
- 14+ theorems across the two traditions.

Aczél cascade:
- `Aczel/SextupleRole.lean` — wraps the existing `ces_sextuple_role`
  (QuadrupleRole.lean) under Layer-5-namespaced theorem names;
  six individual role corollaries (a) superadditivity,
  (b) correlation robustness, (c) strategic independence,
  (d) network scaling, (e) statistical estimation (the
  Aczél⇔Chentsov bridge), (f) phase ordering.
- `Aczel/ProductionDuality.lean` — `inputDemand` definition
  (Shephard algebraic form), primal-dual identity bundled,
  Hölder-conjugate chaining from Layer 5, cost-function
  homogeneity bundled.
- `Aczel/ArrowPratt.lean` — univariate `arrowPratt = -u''/u'`,
  CES multivariate `arrowPrattCES = economicCurvature / c`,
  log-utility characteristic check.

Chentsov cascade:
- `Chentsov/FisherRao.lean` — matrix-valued `fisherRaoMatrix`
  (diagonal in escort-coordinate for the 1-parameter family),
  `IsChentsovInvariant` + `IsRiemannianMetric` predicates,
  Chentsov 1972 uniqueness (hypothesis-bundled).
- `Chentsov/CramerRao.lean` — `IsUnbiasedEstimator`,
  `cramerRaoBound`, the bound theorem (hypothesis-bundled
  matching `mechanism_efficiency_bound` Phase 3 pattern),
  attainment at exponential family (bundled), scaling identity.
- `Chentsov/Invariance.lean` — `IsDeterministicReduction`,
  `IsSufficientForEscort`, Fisher-Rao monotonicity under
  sufficient reductions (bundled), Chentsov invariance
  capstone theorem.

**Aczél cascade inventory** — existing axiom-clean CESProofs
content not wrapped inside LogZExperiment/, living directly
under `CESProofs.*` and already usable:
- `CurvatureRoles/Superadditivity.lean` (Gap #3 resolved,
  ~504 lines).
- `CurvatureRoles/CorrelationRobust.lean` (Theorem 6).
- `CurvatureRoles/Strategic.lean` + `GameTheory.lean`
  (Theorem 7 + CES public goods game).
- `CurvatureRoles/NetworkCES.lean` (14 results, ~900 lines).
- `Hierarchy/DampingCancellation.lean` (dynamical integral,
  commit `bb7a384`).
- `Hierarchy/*.lean` (hierarchical CES activation structure).
- `Potential/MacroApplications.lean` (6 macro theorems).
- All axiom-clean; formal wrapping into `LogZExperiment.Aczel.*`
  deferred as bookkeeping.

**Layer 5 (first hard fork): COMPLETE**

- `Aczel.lean` (~170 lines): 4 Aczél-side named objects
  (`factorShare`, `cesAggregator`, `economicCurvature`,
  `costFunction`) + `arrowPratt` docstring anchor + 4 characteristic
  theorems (including the Hölder-conjugate-exponent identity
  `1/ρ + 1/r = 1`).
- `Chentsov.lean` (~180 lines): 4 Chentsov-side named objects
  (`escortProbability`, `fisherRaoRho`, `sufficientStat`,
  `klDivergence`) + `naturalParameter` docstring anchor + 4
  characteristic theorems (including `fisherRaoRho_nonneg` via
  `escort_variance_nonneg`).
- 8 Layer 5 theorems total; all zero custom axioms.
- Equivalence theorems (`factorShare_is_escort`,
  `escortProbability_is_escort`, `sufficientStat_is_log`) prove
  by `rfl` — confirming the two Layer 5 forks refer to the
  same underlying objects with only the names differing.

Canary findings:
- **The architecture is ergonomic.** Existing CESProofs code is
  structurally log-Z calculus, just under CES-production names.
  Reductions (`logZ_eq_log_escortPartition`, `escort_eq_escortProbability`,
  `fisherInfoRho_eq_cumulant2`, `bridge_eq_bridgeRatio`) are all `rfl`.
- **Layer 0's structural properties** (permutation invariance,
  homogeneity) are stated tradition-neutrally with concrete proofs
  using existing Mathlib / CESProofs infrastructure.
- **Layer 3's uniqueness statement** is tradition-neutral; proof
  paths fork: Aczél-side has concrete CES content in `emergent_CES`
  and `generalized_aczel_network_via_pmf`; Chentsov-side remains
  research-grade external work (Chentsov 1972).
- **Layer 4's consistency identities** re-expose existing
  CESProofs theorems (`bridge_theorem`, `logCES_eq_logPartition`,
  `escortCumulant2_eq_variance`, `pythagorean_welfare`) in
  tradition-neutral log-Z-level language via simple invocations.

## Future phases (post-fork)

**Phase 2 (Layer 5, Aczél side): DONE** — `Aczel.lean` shipped.

**Phase 3 (Layer 5, Chentsov side): DONE** — `Chentsov.lean` shipped.

**Phase 4 (Layer 6): theorem cascades per tradition: DONE
(minimum-viable).** 6 new files shipped. Aczél-side
SextupleRole wrapper + ProductionDuality + ArrowPratt;
Chentsov-side matrix FisherRao + CramerRao bound (bundled)
+ Invariance (bundled). Optional extensions deferred:
formal wrappers for the 8 pre-existing Aczél cascade topics
(damping, hierarchical, macro, etc.); full measure-theoretic
Chentsov content; geodesic computation on Fisher-Rao.

**Phase 5 (Layer 7): `SocialChoice.lean`.** Input-type fork
to preference orderings; Debreu representation (preferences →
utility function → real-valued inputs → logZ); Arrow
impossibility (hypothesis-bundled); Condorcet convergence
(bundled via log-likelihood tail bounds). Requires novel
preference-framework infrastructure that doesn't yet exist
in any form in CESProofs; this is where the Aczél/Chentsov
unification claim becomes thesis-novel.

## Deletion protocol

If the experiment is abandoned:
```
cd CESProofs
rm -rf LogZExperiment/
```

No cleanup elsewhere is needed — by design, no file in
`CESProofs/` (outside `LogZExperiment/`) imports from this
directory. The main codebase remains intact.
