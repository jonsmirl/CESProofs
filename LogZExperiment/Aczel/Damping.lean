/-
  LogZExperiment/Aczel/Damping.lean — Layer 6 Aczél cascade
  (migration demonstration from `Hierarchy/DampingCancellation.lean`).

  **Layer status**: HARD FORK. Aczél-tradition downstream dynamics.

  **Migration experiment**: demonstrates how main-tree content can
  be re-exposed under LogZExperiment's layered architecture. The
  underlying proofs stay in `Hierarchy/DampingCancellation.lean`;
  this file provides the Layer-6 narrative positioning and the
  core identity wrapped with a thesis-aligned name. Downstream
  callers who want the full signature set (upstream-reform-beta,
  upstream-reform-sigma-prev, welfare integral dynamical form,
  etc.) import `CESProofs.Hierarchy.DampingCancellation` directly;
  this wrapper provides the Layer-6 anchor point.

  **Headline result** (Paper C / Paper 4): regulation σ at a
  hierarchical level cancels out in the welfare integral, so
  welfare is independent of own-level regulation. To improve
  welfare at level n, one must reform *upstream* (reduce
  σ_{n-1} or raise β_n). This is a flagship Aczél-tradition
  result — cardinal economic quantities (prices, quantities,
  regulation parameter σ, gain elasticity β).

  **Why Aczél-side**: the content is derived from CES-cascade
  dynamics via the `cesAggregator` (Layer 5) + the
  `economicCurvature` (Layer 5). The Chentsov reading would
  re-derive damping cancellation as statistical-invariance
  under sufficient-statistic reductions in the rate-of-learning
  signal — same underlying fact, different derivation, different
  theorems. That's future Phase 7b / Layer 8 work.

  **Migration pattern findings**:
  1. Import the source file; `open` where helpful.
  2. Create a Layer-6 namespace in LogZExperiment (subdirectory).
  3. Re-expose the *central* identity with a thesis-aligned name.
  4. Narrative docstring positions the theorem in the doubly-
     unique log-Z story.
  5. Specialized / high-plumbing theorems (e.g., dynamical
     integral with `Integrable` hypothesis) stay in the source;
     docstring-point to them.
  6. Namespace collision avoided via `_root_.` prefix.
  7. Zero new proof obligations — proofs stay in source.
  8. Axiom cleanness preserved.
-/

import CESProofs.LogZExperiment.Aczel
import CESProofs.Hierarchy.DampingCancellation

open Real Finset BigOperators

noncomputable section

namespace LogZExperiment
namespace Aczel
namespace Damping

-- ============================================================
-- The core damping cancellation identity (re-exposed)
-- ============================================================

/-- **Damping cancellation (algebraic)** — Layer-6 Aczél re-exposure
    of `damping_cancellation_algebraic` from
    `Hierarchy/DampingCancellation.lean`.

    Identity: `c · (φ/σ) · σ = c · φ` for `σ ≠ 0`.

    Under the Aczél-tradition reading, this is the algebraic
    core of the "welfare is independent of own-level
    regulation" claim: the own-σ in the welfare factor
    `c · (φ/σ) · σ · δ²` cancels algebraically, so the policy
    parameter σ at level `n` has no first-order effect on
    welfare there. Hence upstream reform (β or σ at level
    `n−1`) is the effective lever.

    Zero proof work — direct wrapper. -/
theorem damping_cancellation {phi_prev sigma_n c_n : ℝ}
    (h : sigma_n ≠ 0) :
    c_n * (phi_prev / sigma_n) * sigma_n = c_n * phi_prev :=
  damping_cancellation_algebraic h

-- ============================================================
-- Pointers to specialized results
-- ============================================================

/-! ### Specialized damping-cancellation results (pointer-only)

The following results live in `Hierarchy/DampingCancellation.lean`
under the root namespace; downstream callers import that file
directly and call them by their original names. Wrapping them
here would duplicate the Mathlib-plumbing in their signatures
(e.g., `Integrable` hypotheses for the full dynamical form)
without structural benefit.

- `_root_.welfare_independent_of_own_sigma` — any two nonzero σ
  values give identical welfare (with `δ²` factor).
- `_root_.upstream_reform_beta` — raising β at level `n` lowers
  welfare loss (higher β ⇒ less welfare degradation).
- `_root_.upstream_reform_sigma_prev` — lowering σ at level
  `n−1` lowers welfare loss.
- `_root_.damping_cancellation_dynamical` — the full welfare
  integral `∫₀^∞ c·σ·(F(t)−F̄)² dt = c·δ²/2` is σ-independent
  along the exponential-decay trajectory. Promoted from
  `True := trivial` in Phase 2 / commit `bb7a384`.
- `_root_.fastest_layer_regulation` — fastest-layer σ has zero
  long-run welfare effect (Corollary 1).
- `_root_.cascade_long_run_zero`, `_root_.hump_long_run_zero`
  — biexponential and hump IRFs decay to zero.

All axiom-clean. All remain usable via their root-namespace
names. The Layer-6 anchor above is the thesis-narrative entry
point; the rest are detailed corollaries. -/

end Damping
end Aczel
end LogZExperiment

end
