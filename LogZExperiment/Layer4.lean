/-
  LogZExperiment/Layer4.lean — Layer 4: Consistency Identities.

  The capstone pre-fork layer. Having defined `logZ` (Layer 0),
  derived six objects (Layer 1), pinned the domain (Layer 2),
  and proved uniqueness under both traditions (Layer 3), we now
  state the consistency identities that tie the derivatives
  together.

  **Layer status**: NEUTRAL.

  **Contents**:
  1. **Bridge theorem in logZ language** — the cross-partial
     identity connecting curvatureX and fisherInfoRho via
     `bridge ρ`. Central piece of the doubly-unique story.
  2. **Log-CES identity** — `ρ · log F = logZ - log J`, linking
     the aggregator `F` to `logZ` directly.
  3. **Cumulant hierarchy summary** — all higher ρ-derivatives
     of `logZ` are cumulants of `log x` under the escort.
  4. **Pythagorean decomposition on α-divergences** — the
     Bregman / α-divergence triangle identity in logZ form
     (re-expressed from TripleCorrespondence's pythagorean_welfare).

  These are existing CESProofs theorems re-exposed in tradition-
  neutral logZ language.
-/

import CESProofs.LogZExperiment.Layer0
import CESProofs.LogZExperiment.Layer1
import CESProofs.LogZExperiment.Layer3
import CESProofs.Foundations.TripleCorrespondence

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

namespace LogZExperiment

-- ============================================================
-- Consistency 1: Bridge theorem in logZ language
-- ============================================================

/-- **Bridge theorem as logZ cross-partial identity**.

    The existing CESProofs `bridge_theorem` in
    `InformationGeometry.lean` states:

        -hessLogFEigenvalue J ρ c = bridgeRatio ρ * escortFisherEigenvalue J ρ c

    Re-expressed in Layer-1 logZ-level names:

        curvatureX J ρ c = bridge ρ * escortFisherEigenvalue J ρ c.

    This is the cross-partial identity of `logZ`: the second
    x-derivative (economic curvature / natural-parameter Fisher
    info) equals the second ρ-derivative (Fisher info in ρ
    direction) scaled by the bridge ratio.

    The identity is the primary evidence of the doubly-unique
    story: the same log Z generates both "curvature in x" and
    "curvature in ρ" up to a universal scaling. -/
theorem logZ_cross_partial_identity [NeZero J] {ρ : ℝ}
    (hρ : ρ ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    curvatureX J ρ c = bridge ρ * escortFisherEigenvalue J ρ c := by
  unfold curvatureX bridge
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne J)
  exact bridge_theorem hρ hc hJne

-- ============================================================
-- Consistency 2: Log-CES identity
-- ============================================================

/-- **Log-CES / log Z identity** in Layer-0 form.

    For a positive input vector, the power-mean aggregator
    `M_ρ(x)` and the log-partition function `logZ x ρ` are
    related by

        ρ · log M_ρ(x) = logZ x ρ - log J.

    Under Aczél-reading, this expresses the CES aggregator as
    a log-partition-function derivative. Under Chentsov-reading,
    this expresses the exponential-family "mean" as a
    cumulant-generating-function derivative.

    Reduction of the existing `logCES_eq_logPartition`. -/
theorem logZ_and_powerMean [NeZero J] {ρ : ℝ} (hρ : ρ ≠ 0)
    (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) :
    ρ * Real.log (powerMean J ρ hρ x) = logZ x ρ - Real.log ↑J :=
  logCES_eq_logPartition hρ x hx

-- ============================================================
-- Consistency 3: Cumulant hierarchy (escort moments)
-- ============================================================

/-- **Escort-cumulant connection**: all higher ρ-derivatives of
    `logZ` are cumulants of `log x` under the escort distribution.

    The second ρ-cumulant (variance) is `fisherInfoRho`. Higher
    cumulants are `escortCumulant3`, `escortCumulant4`, etc., all
    established in `CumulantTower.lean`.

    At Layer 4, we expose this as the log-Z-level statement:
    the cumulant tower of `log x` under the escort is the full
    Taylor series of `logZ` in ρ. -/
theorem logZ_cumulant2_eq_fisherInfo (x : Fin J → ℝ) (ρ : ℝ) :
    fisherInfoRho x ρ = escortCumulant2 x ρ := rfl

/-- The variance-response identity (VRI) at the escort level:
    `fisherInfoRho = Var_escort[log x]`. Reduction of
    `CumulantTower.escortCumulant2_eq_variance`. -/
theorem logZ_vri [NeZero J] (x : Fin J → ℝ) (hx : ∀ j, 0 < x j) (ρ : ℝ) :
    fisherInfoRho x ρ = escortVariance x ρ (fun j => Real.log (x j)) := by
  unfold fisherInfoRho
  exact escortCumulant2_eq_variance x hx ρ

-- ============================================================
-- Consistency 4: Pythagorean decomposition (α-divergence)
-- ============================================================

/-- **Pythagorean decomposition in logZ language**.

    The α-divergence induced by `logZ` satisfies a Pythagorean
    identity: for an α-orthogonal triple `(x_opt, x_eq, x)`,

        D_α(x_opt ‖ x) = D_α(x_opt ‖ x_eq) + D_α(x_eq ‖ x).

    This is the existing `pythagorean_welfare` theorem from
    `TripleCorrespondence.lean`, which at Layer 4 is a consistency
    identity of the Bregman / α-divergence derived from `logZ`.

    Under Aczél-reading, this is the welfare decomposition
    (total loss = redistributive + allocative). Under Chentsov-
    reading, this is the Amari-Nagaoka information geometric
    Pythagorean theorem. -/
theorem logZ_pythagorean_decomposition {J : ℕ} (α : ℝ) (hα : α ^ 2 ≠ 1)
    (x_opt x_eq x : Fin J → ℝ)
    (h_ortho :
      (∑ j : Fin J, x_opt j ^ ((1 + α) / 2) * x_eq j ^ ((1 - α) / 2)) +
      (∑ j : Fin J, x_eq j ^ ((1 + α) / 2) * x j ^ ((1 - α) / 2)) -
      (∑ j : Fin J, x_opt j ^ ((1 + α) / 2) * x j ^ ((1 - α) / 2)) = 1) :
    alphaDivergence α x_opt x =
    alphaDivergence α x_opt x_eq + alphaDivergence α x_eq x :=
  pythagorean_welfare α hα x_opt x_eq x h_ortho

-- ============================================================
-- Summary: the pre-fork tradition-neutral architecture
-- ============================================================

/-! ### Summary of Layers 0–4

The pre-fork architecture is complete. Tradition-neutral content:

| Layer | Object(s) | Fork status |
|-------|-----------|-------------|
| 0 | logZ, positivity, permutation invariance, homogeneity | NEUTRAL |
| 1 | escort, fisherInfoRho, curvatureX, bridge, legendreDual, bregmanDivergence | NEUTRAL |
| 2 | IsAczelDomain, IsChentsovDomain, aczelToChentsov | MINOR FORK (domain) |
| 3 | IsLogZUnique, AczelAxiomPack, ChentsovAxiomPack, doubly-unique theorem | NEUTRAL (statement); proof traditions fork |
| 4 | Bridge theorem, log-Z-and-powerMean, VRI, Pythagorean decomposition | NEUTRAL |

Everything above Layer 4 forks hard:
- Layer 5: named downstream objects (factor share vs escort probability).
- Layer 6: domain-specific theorem cascades (CES macro vs social choice).
- Layer 7: input-type fork (cardinal reals vs preferences).

See `LogZExperiment/README.md` for the full layering map. -/

end LogZExperiment

end
