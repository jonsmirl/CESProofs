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
├── README.md        — this file
├── Master.lean      — pre-fork aggregator; imports Layers 0-4
├── Layer0.lean      — the master generator (logZ + basic properties)
├── Layer1.lean      — six derivatives (escort, Fisher, curvature,
│                     bridge, Legendre, Bregman)
├── Layer2.lean      — domain regularity (Aczél vs Chentsov predicates)
├── Layer3.lean      — doubly-unique theorem (both axiom packs)
├── Layer4.lean      — consistency identities (bridge, VRI, Pythagorean)
├── Aczel.lean       — Layer 5 Aczél fork: factorShare, cesAggregator,
│                     economicCurvature, costFunction
└── Chentsov.lean    — Layer 5 Chentsov fork: escortProbability,
                      fisherRaoRho, sufficientStat, klDivergence
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

**Phase 4 (Layer 6): theorem cascades per tradition.** Heavy
downstream content — on the Aczél side, production duality
(Shephard's lemma, cost-function Legendre-conjugate theorems,
the Sextuple Role connecting curvatureK to six specialized
production properties), hierarchical CES, macroeconomic
multiplier theory. On the Chentsov side, full exponential-family
theory, Cramér-Rao bound as hypothesis-bundled statement,
matrix-valued Fisher-Rao metric, geodesic distance computation,
Chentsov's invariance theorem (monotonicity under Markov kernels,
hypothesis-bundled).

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
