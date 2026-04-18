# LogZExperiment — quarantined architectural experiment

## Purpose

This directory tests whether the CESProofs codebase can be
re-architected around the **log-Z master generator** (per
`research/demographics/logZ_is_the_master_generator.md`) as a
tradition-neutral top-down structure, with Aczél and Chentsov
specializations downstream.

The experiment is isolated so that it can be **deleted cleanly**
if unproductive. Nothing outside this directory imports from it.

## Scope

**Phase 1 (canary, done)** — `Master.lean`: tradition-neutral log Z
definition, the six derivatives (escort, Fisher info, curvature,
bridge, Legendre dual, Bregman), reduction identities showing that
existing CESProofs content (escortProbability, bridgeRatio,
logCES_eq_logPartition) is log-Z-derived. Documents the four
split points where Aczél and Chentsov readings diverge.

**Phase 2 (future)** — `Aczel.lean`: re-expresses existing CES
content as Aczél-reading specializations of `Master.lean`.

**Phase 3 (future)** — `Chentsov.lean`: native Chentsov-side content
(Fisher-Rao uniqueness, Arrow, Condorcet scaffolding).

## Deletion protocol

If the experiment is abandoned:
```
cd CESProofs
rm -rf LogZExperiment/
```

No cleanup elsewhere is needed — by design, no file in
`CESProofs/` (outside `LogZExperiment/`) imports from this
directory. The main codebase remains intact.

## Canary findings (Phase 1)

- `Master.lean` produces 9 theorems, all zero custom axioms, in
  ~180 lines.
- Reduction identities (`logZ_eq_log_escortPartition`,
  `escort_eq_escortProbability`, `fisherInfoRho_eq_cumulant2`,
  `bridge_eq_bridgeRatio`) are all `rfl` — the existing CESProofs
  code is structurally log-Z calculus under CES-production names.
- Aczél- and Chentsov-path uniqueness claims stated via bundled
  hypothesis; no new substantive proof work.
- The parallel top-down architecture is **ergonomic at the level
  tested**: pure naming / renaming exercise, not a rewrite.

Untested: derivative-level statements of log Z (Mathlib
derivative hygiene); full Bregman / Fenchel content; native
Chentsov-side derivations.
