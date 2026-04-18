/-
  LogZExperiment/Master.lean — aggregator for the pre-fork
  tradition-neutral architecture.

  **ISOLATION NOTE**: this file lives under `CESProofs/LogZExperiment/`
  as a quarantined architectural experiment. If the experiment fails
  or is judged unproductive, delete the entire `LogZExperiment/`
  subdirectory — nothing else in `CESProofs/` imports it.

  This master file imports and re-exposes the five pre-fork layers:

  * **Layer 0** (`Layer0.lean`): the master generator `logZ` with
    basic structural properties (positivity, permutation invariance,
    scalar homogeneity).
  * **Layer 1** (`Layer1.lean`): six derivatives of `logZ`
    (escort, Fisher info in ρ, curvature in x, bridge ratio,
    Legendre dual, Bregman divergence).
  * **Layer 2** (`Layer2.lean`): domain regularity predicates
    (Aczél positive orthant vs Chentsov simplex, with normalization
    map).
  * **Layer 3** (`Layer3.lean`): the doubly-unique statement —
    `logZ` is forced by both Aczél's three aggregation axioms
    AND Chentsov's three statistical-invariance axioms.
  * **Layer 4** (`Layer4.lean`): consistency identities (bridge
    theorem cross-partial, log-CES-and-logZ identity, VRI,
    Pythagorean α-divergence decomposition).

  **Layers 0–4 are pre-fork** (tradition-neutral statements, with
  at most a minor domain fork at Layer 2 and a proof-tradition
  fork at Layer 3 that leaves the statement intact).

  **Layer 5+ is the hard fork** — deferred to future
  `LogZExperiment/Aczel.lean` and `LogZExperiment/Chentsov.lean`
  files, where tradition-specific named downstream objects and
  theorem cascades live.

  See `LogZExperiment/README.md` for the full layering map and
  the rollback protocol.
-/

import CESProofs.LogZExperiment.Layer0
import CESProofs.LogZExperiment.Layer1
import CESProofs.LogZExperiment.Layer2
import CESProofs.LogZExperiment.Layer3
import CESProofs.LogZExperiment.Layer4

/-! ### Usage

All pre-fork content is re-exposed under the `LogZExperiment`
namespace. Importers can write `open LogZExperiment` and refer
to `logZ`, `escort`, `fisherInfoRho`, `curvatureX`, `bridge`,
`IsLogZUnique`, `AczelAxiomPack`, `ChentsovAxiomPack`,
`logZ_cross_partial_identity`, etc. -/
