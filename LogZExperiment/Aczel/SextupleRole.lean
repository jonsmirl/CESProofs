/-
  LogZExperiment/Aczel/SextupleRole.lean — Layer 6 Aczél cascade.

  **Layer status**: HARD FORK. Aczél-tradition downstream.

  Re-exposes the existing `ces_sextuple_role` theorem
  (`CurvatureRoles/QuadrupleRole.lean`) under Layer-6 naming,
  tying each of the six roles to Layer 5's `economicCurvature`.

  The Sextuple Role theorem is the central Aczél-downstream
  result: the single curvature parameter `K = (1-ρ)(J-1)/J`
  (= Layer 5's `economicCurvature`) simultaneously controls six
  distinct CES properties:

  (a) Superadditivity — complementary agents produce more together.
  (b) Correlation robustness — CES extracts idiosyncratic variation.
  (c) Strategic independence — balanced allocation is Nash equilibrium.
  (d) Network scaling — G(J) = J^{1/ρ} · c.
  (e) Statistical estimation — production curvature = bridge ratio
      × Fisher information (this is the Aczél⇔Chentsov bridge).
  (f) Phase ordering — K_eff = K · max(0, 1-T/T*).

  **Doubly-unique connection**: since `K` is forced by Aczél's
  three aggregation axioms (`emergent_CES` /
  `generalized_aczel_network`), AND all six roles are controlled
  by `K`, all six roles are forced by the Aczél axiom pack. A
  structural expression of the Layer 3 doubly-unique story on
  the Aczél side.
-/

import CESProofs.LogZExperiment.Aczel
import CESProofs.CurvatureRoles.QuadrupleRole

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

namespace LogZExperiment
namespace Aczel
namespace SextupleRole

/-- **`economicCurvature_sextuple_role`**: the Sextuple Role
    theorem stated in Layer-5-namespaced form. Since
    `economicCurvature = curvatureK` by definition (Layer 5),
    this is the existing `ces_sextuple_role` re-exposed under
    the Layer-6 Aczél naming. -/
theorem economicCurvature_sextuple_role (ρ : ℝ) :
    SextupleRoleStatement J ρ :=
  ces_sextuple_role ρ

-- ============================================================
-- Six individual role corollaries (Layer-5-namespaced)
-- ============================================================

/-- **(K-pos)**: `economicCurvature > 0` when `ρ < 1` and
    `J ≥ 2`. Layer-5-namespaced reduction of the structure's
    `K_pos` field.

    Structurally identical to `Aczel.economicCurvature_positive`;
    this lemma invokes the SextupleRole structure explicitly to
    establish the "every role starts from positive K" anchor. -/
theorem sextuple_K_positive {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1) :
    0 < economicCurvature J ρ :=
  (ces_sextuple_role (J := J) ρ).K_pos hJ hρ

/-- **(a) Superadditivity**: under Aczél complementarity
    (ρ < 1, J ≥ 2), the CES Hessian is strictly negative on
    the 1⊥ subspace. Layer-5-namespaced via the Sextuple Role
    structure. -/
theorem sextuple_superadditivity {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    (c : ℝ) (hc : 0 < c) (v : Fin J → ℝ)
    (hv : orthToOne J v) (hv_ne : ∃ j, v j ≠ 0) :
    cesHessianQF J ρ c v < 0 :=
  (ces_sextuple_role (J := J) ρ).superadd hJ hρ c hc v hv hv_ne

/-- **(c) Strategic independence**: coalition payoff reduction
    on 1⊥ (same sign as superadditivity, different economic
    interpretation — a coalition cannot internally re-allocate
    to its own benefit). -/
theorem sextuple_strategic_independence {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ}
    (hρ : ρ < 1)
    (c : ℝ) (hc : 0 < c) (δ : Fin J → ℝ)
    (hδ : orthToOne J δ) (hδ_ne : ∃ j, δ j ≠ 0) :
    cesHessianQF J ρ c δ < 0 :=
  (ces_sextuple_role (J := J) ρ).strategic hJ hρ c hc δ hδ hδ_ne

/-- **(d) Network scaling**: `G(J) = J^{1/ρ} · c` at the
    symmetric allocation. This is the Aczél-side statement of
    "log Z grows linearly in `log J`" at equal inputs. -/
theorem sextuple_network_scaling {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρne : ρ ≠ 0)
    (c : ℝ) (hc : 0 < c) :
    unnormCES J ρ (symmetricPoint J c) = (↑J : ℝ) ^ (1 / ρ) * c :=
  (ces_sextuple_role (J := J) ρ).network hJ hρne c hc

/-- **(e) Statistical estimation (the Aczél⇔Chentsov bridge)**:
    production curvature equals bridge ratio × Fisher information.
    This is the characteristic bridge identity — it's the role
    that connects Aczél and Chentsov traditions.

    Reduction of the `estimation` field; matches the existing
    `bridge_theorem` from `InformationGeometry.lean`. -/
theorem sextuple_statistical_estimation {J : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (c : ℝ) (hc : c ≠ 0) (hJne : (↑J : ℝ) ≠ 0) :
    -hessLogFEigenvalue J ρ c = bridgeRatio ρ * escortFisherEigenvalue J ρ c :=
  (ces_sextuple_role (J := J) ρ).estimation hρ c hc hJne

/-- **(f) Phase ordering**: the effective curvature decomposes
    as `K_eff = K · max(0, 1-T/T*)`. Phase-transition content
    from Paper 2 (effective curvature framework). -/
theorem sextuple_phase_ordering (ρ : ℝ) (T Tstar : ℝ) :
    effectiveCurvatureKeff J ρ T Tstar =
    curvatureK J ρ * reducedOrderParam T Tstar :=
  (ces_sextuple_role (J := J) ρ).phase T Tstar

-- ============================================================
-- Layer 5 bridge: economicCurvature = curvatureK
-- ============================================================

/-- The Sextuple Role's `curvatureK` is Layer 5's `economicCurvature`
    by definitional unfolding. Explicit consistency lemma. -/
theorem economicCurvature_eq_curvatureK (J : ℕ) (ρ : ℝ) :
    economicCurvature J ρ = curvatureK J ρ := rfl

end SextupleRole
end Aczel
end LogZExperiment

end
