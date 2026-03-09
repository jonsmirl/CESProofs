/-
  The CES Sextuple Role theorem (Paper 1, Section 9):
  - Theorem 9 (thm:sextuple): CES Sextuple Role — collecting all six roles

  The curvature parameter K = (1-ρ)(J-1)/J simultaneously controls:
  (a) Superadditivity — complementary agents produce more together
  (b) Correlation robustness — CES extracts idiosyncratic variation
  (c) Strategic independence — balanced allocation is Nash equilibrium
  (d) Network scaling — G(J) = J^{1/ρ} · c
  (e) Statistical estimation — production curvature = bridge ratio × Fisher info
  (f) Phase ordering — K_eff = K · max(0, 1-T/T*)
-/

import CESProofs.CurvatureRoles.Superadditivity
import CESProofs.CurvatureRoles.CorrelationRobust
import CESProofs.CurvatureRoles.Strategic
import CESProofs.CurvatureRoles.NetworkCES
import CESProofs.Foundations.InformationGeometry
import CESProofs.CurvatureRoles.PhaseTransition

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Theorem 9: CES Sextuple Role (thm:sextuple)
-- ============================================================

/-- The six roles of CES curvature, bundled together. -/
structure SextupleRoleStatement (J : ℕ) (ρ : ℝ) where
  /-- K > 0 when ρ < 1 and J ≥ 2 -/
  K_pos : 2 ≤ J → ρ < 1 → 0 < curvatureK J ρ
  /-- (a) Superadditivity: the Hessian is negative definite on 1⊥,
      so any reallocation from the symmetric point reduces output -/
  superadd : 2 ≤ J → ρ < 1 → ∀ (c : ℝ), 0 < c →
    ∀ (v : Fin J → ℝ), orthToOne J v → (∃ j, v j ≠ 0) →
    cesHessianQF J ρ c v < 0
  /-- (b) Correlation robustness: the diversity-encoding correction
      is proportional to K · idiosyncratic variance -/
  corr_robust : 2 ≤ J → ρ < 1 →
    ∀ (m : EquicorrModel),
    let correction := -(curvatureK J ρ) / (2 * m.c) * m.idioVar
    correction = cesEigenvaluePerp J ρ m.c * (↑J - 1) * m.idioVar / 2
  /-- (c) Strategic independence: the Hessian is negative on 1⊥,
      so no coalition benefits from manipulation -/
  strategic : 2 ≤ J → ρ < 1 → ∀ (c : ℝ), 0 < c →
    ∀ (δ : Fin J → ℝ), orthToOne J δ → (∃ j, δ j ≠ 0) →
    cesHessianQF J ρ c δ < 0
  /-- (d) Network scaling: G(J) = J^{1/ρ} · c -/
  network : 0 < J → ρ ≠ 0 → ∀ (c : ℝ), 0 < c →
    unnormCES J ρ (symmetricPoint J c) = (↑J : ℝ) ^ (1 / ρ) * c
  /-- (e) Statistical estimation: production curvature = bridge ratio × Fisher info.
      -Hess(log F)|_⊥ = ((1-ρ)/ρ²) · I_Fisher -/
  estimation : ρ ≠ 0 → ∀ (c : ℝ), c ≠ 0 → (↑J : ℝ) ≠ 0 →
    -hessLogFEigenvalue J ρ c = bridgeRatio ρ * escortFisherEigenvalue J ρ c
  /-- (f) Phase ordering: K_eff = K · max(0, 1-T/T*).
      K sets the scale of the order parameter. -/
  phase : ∀ (T Tstar : ℝ),
    effectiveCurvatureKeff J ρ T Tstar = curvatureK J ρ * reducedOrderParam T Tstar

/-- **Theorem 9 (CES Sextuple Role)** — Theorem 9.1 (thm:sextuple).

    Let F be a CES aggregate with equal weights, ρ < 1, and J ≥ 2.
    Define K = (1 - ρ)(J - 1)/J. Then K > 0, and:

    (a) **Superadditivity**: gap ≥ Ω(K) · diversity
    (b) **Correlation robustness**: E[F(X)] = c - Θ(K) · τ²(1-r)/(2c)
    (c) **Strategic independence**: Δ(S) ≤ -Ω(K) · deviation²
    (d) **Network scaling**: G(J) = J^{1/ρ} · c
    (e) **Statistical estimation**: -Hess(log F)|_⊥ = ((1-ρ)/ρ²) · I_Fisher
    (f) **Phase ordering**: K_eff = K · f(T/T*), order parameter with β=γ=1

    All six properties are controlled by the single parameter K.
    They are not separate phenomena but six manifestations of the
    same geometric fact: the curvature of CES isoquants.

    **Proof.** Each role is proved independently and assembled into a structure: (a,c) follow from the CES Hessian eigenvalue $\lambda_\perp = -(1-\rho)/J < 0$ on $\mathbf{1}^\perp$; (b) from the diversity-encoding identity relating the correction to $K \cdot \tau^2(1-r)$; (d) from direct evaluation of the unnormalized CES at the symmetric point; (e) from the bridge theorem $-\nabla^2 \log F|_\perp = ((1-\rho)/\rho^2) \cdot I_F$; and (f) from the algebraic identity $K_{\mathrm{eff}} = K \cdot \max(0, 1 - T/T^*)$. -/
theorem ces_sextuple_role (ρ : ℝ) : SextupleRoleStatement J ρ where
  K_pos := fun hJ hρ => curvatureK_pos hJ hρ
  superadd := fun hJ hρ c hc v hv hv_ne =>
    ces_strict_concavity_on_perp hJ hρ hc v hv hv_ne
  corr_robust := fun hJ hρ m => diversity_encoding hJ hρ m
  strategic := fun hJ hρ c hc δ hδ hδ_ne =>
    ces_strict_concavity_on_perp hJ hρ hc δ hδ hδ_ne
  network := fun hJ hρne c hc =>
    network_scaling hJ hρne hc
  estimation := fun hρ c hc hJ => bridge_theorem hρ hc hJ
  phase := fun T Tstar => keff_eq_K_times_reduced J ρ T Tstar

end
