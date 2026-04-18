/-
  Theorems 5-7, Corollaries 2-4, Propositions 8-11:
  q-Dynamics on the CES Potential Landscape
  (Paper 2, Section 5)

  Dynamic identities connecting the CES potential to fluctuations,
  reversibility, and barrier crossing. Many of these are deep structural
  results axiomatized for the formalization.
-/

import CESProofs.Potential.Defs
import CESProofs.Potential.EffectiveCurvature

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Theorem 5: q-Variance-Response Identity
-- ============================================================

/-- **Theorem 5 (q-Variance-Response Identity)** — Section 5.1 of Paper 2.
    [Schematic — source: Tsallis 2009, *Introduction to Nonextensive Statistical
    Mechanics*, Ch. 3, Eq. 3.48]

    The response of the q-optimal allocation to a payoff perturbation δε
    is proportional to the q-covariance of ε under the escort distribution:

    ∂p*/∂ε = (1/T) · Cov_q(ε)

    where Cov_q uses the escort (q-deformed) probabilities.

    This is the q-generalization of the fluctuation-dissipation theorem (FDT).
    At q = 1, it reduces to the standard logit covariance identity.

    The identity connects macroscopic response (how allocation changes)
    to microscopic fluctuations (how diverse the payoff distribution is).

    **Proof.** Differentiating the $q$-optimal allocation
    $p^* = \arg\max[\langle \varepsilon, p\rangle - T \cdot S_q(p)]$ with respect to
    $\varepsilon$ yields $\partial p^*/\partial\varepsilon = (1/T) \cdot \operatorname{Cov}_q(\varepsilon)$,
    where $\operatorname{Cov}_q$ uses the escort distribution $P_j^{(q)} \propto p_j^q$.
    At $q = 1$, this reduces to the standard logit covariance identity
    $\partial p/\partial\varepsilon = (1/T)[\operatorname{diag}(p) - pp^T]$.

    **Lean closure (Tier 2, hypothesis-bundled)**: the FDT identity
    `∂p*/∂ε = (1/T) · Cov_q(ε)` is supplied as hypothesis `h_FDT`
    (the classical Tsallis 2009 derivation), and the operational
    rearrangement `Cov_q = T · ∂p*/∂ε` — the form directly usable
    for empirical friction measurement (Corollary 2) — is
    concluded by algebra. -/
theorem qVariance_response (J : ℕ) (q T : ℝ) (_hq : 0 < q) (hT : 0 < T)
    (_ε : Fin J → ℝ)
    (dpStarDEps CovQ : Fin J → Fin J → ℝ)
    (h_FDT : ∀ i j, dpStarDEps i j = (1 / T) * CovQ i j) :
    ∀ i j, CovQ i j = T * dpStarDEps i j := by
  intros i j
  rw [h_FDT i j]
  have hT_ne : T ≠ 0 := ne_of_gt hT
  field_simp

-- ============================================================
-- Corollary 2: q-Friction Measurement
-- ============================================================

/-- **Corollary 2 (q-Friction Measurement)** — Section 5.1 of Paper 2.

    Rearranging the variance-response identity (Theorem 5):
    T = Cov_q(ε) / (∂p*/∂ε)

    This provides an empirical method to measure information friction T
    from observable data: the ratio of payoff covariance to allocation
    response. Higher friction → more covariance per unit of response.

    This is a rearrangement of Theorem 5. -/
theorem qFriction_measurement_formula (T Cov Response : ℝ) (hR : Response ≠ 0)
    (hFDT : Response = Cov / T) (hT : T ≠ 0) :
    T = Cov / Response := by
  have h : Response * T = Cov := by
    field_simp at hFDT
    linarith
  field_simp
  linarith

-- ============================================================
-- Theorem 6: q-Covariance Eigenstructure
-- ============================================================

/-- **Theorem 6 (q-Covariance Eigenstructure)** — Section 5.2 of Paper 2.
    [Schematic — derived extension of the CES Hessian eigendecomposition
    (Paper 1, Theorem 3) to the q-exponential family setting. Not a
    standard imported result; this is our own derivation.]

    The q-covariance matrix at the uniform allocation is:
    Cov_q = T · (∇²Φ_q)⁻¹ = T · (-H_eff)⁻¹

    where H_eff is the effective Hessian (production + entropy).

    By symmetry at the uniform point:
    - Eigenvalue on 1: 0 (allocation sums to 1)
    - Eigenvalue on 1⊥: T / |λ_eff| = T · Jc² / (1-ρ)(1-T/T*)

    The covariance eigenvalue on 1⊥ diverges as T → T* (pre-crisis
    deceleration manifests as exploding variance).

    **Proof.** The $q$-optimal allocation satisfies $\nabla \Phi_q = 0$. The $q$-covariance matrix is the inverse curvature: $\operatorname{Cov}_q = T \cdot (-\nabla^2 \Phi_q)^{-1}$. At the uniform allocation $p_j = 1/J$, the effective Hessian $\nabla^2 \Phi_q$ decomposes by symmetry into two eigenspaces: eigenvalue $0$ on $\mathbf{1}$ and eigenvalue $\lambda_\perp = -(1-\rho)/(Jc^2) \cdot (1-T/T^*)$ on $\mathbf{1}^\perp$, where the $(1-T/T^*)$ factor comes from Theorem 4 (effective curvature). Inverting gives the covariance eigenvalue on $\mathbf{1}^\perp$ as $T/|\lambda_\perp| = TJc^2/[(1-\rho)(1-T/T^*)]$. As $T \to T^*$, this diverges: the variance explosion is the statistical signature of pre-crisis deceleration.

    **Lean closure (Tier 2, hypothesis-bundled)**: the Hessian
    eigenvalue magnitude on 1⊥ is supplied as hypothesis `h_eig`
    (Theorem 4 effective-curvature content) and the covariance
    eigenvalue as `T / lamPerpAbs` is shown to equal the closed
    form `T·J·c² / ((1-ρ)(1-T/T*))` by `field_simp; ring`.
    Divergence as `T → Tstar` is manifest in the denominator. -/
theorem qCovariance_eigenstructure (J : ℕ) (q T c ρ Tstar : ℝ)
    (_hq : 0 < q) (_hT : 0 < T) (_hc : 0 < c)
    (hρ_ne : (1 - ρ) ≠ 0)
    (hJc2_ne : ((↑J : ℝ) * c ^ 2) ≠ 0)
    (hTdiff_ne : (1 - T / Tstar) ≠ 0)
    (lamPerpAbs : ℝ)
    (h_eig : lamPerpAbs = (1 - ρ) / ((↑J : ℝ) * c ^ 2) * (1 - T / Tstar))
    (h_eig_ne : lamPerpAbs ≠ 0) :
    T / lamPerpAbs =
    T * ((↑J : ℝ) * c ^ 2) / ((1 - ρ) * (1 - T / Tstar)) := by
  rw [h_eig]
  field_simp

-- ============================================================
-- Theorem 7: q-Crooks Reversibility
-- ============================================================

/-- **Theorem 7 (q-Crooks Reversibility)** — Section 5.3 of Paper 2.
    [Schematic — source: Crooks 1999, *PRE* 60:2721, extended to
    q-statistics via Tsallis 2009, Ch. 14]

    The ratio of forward to reverse path probabilities under the
    q-dynamics satisfies:
    P_forward(path) / P_reverse(path) = exp_q(ΔΦ_q / T)

    where ΔΦ_q is the change in CES potential along the path.

    This is the q-generalization of the Crooks fluctuation theorem.
    At q = 1, it reduces to the standard detailed balance relation
    P_f/P_r = exp(ΔF/T).

    **Proof.** For $q$-Langevin dynamics with stationary distribution
    $\propto \exp_q(-\Phi_q/T)$, the ratio of forward to reverse path
    probabilities satisfies detailed balance:
    $P_F/P_R = \exp_q(\Delta\Phi_q/T)$. At $q = 1$, this reduces to the
    standard $P_F/P_R = \exp(\Delta F/T)$.

    **Lean closure (Tier 2, hypothesis-bundled)**: the classical
    detailed-balance identity `P_forward = P_reverse · exp_q(ΔΦ/T)`
    (Crooks 1999 / Tsallis 2009 Ch. 14) is supplied as hypothesis
    `h_detailed_balance`, and the ratio form usable for Jarzynski
    (Corollary 3) is concluded by division (`field_simp`). -/
theorem qCrooks_reversibility (q T ΔΦ Pf Pr : ℝ)
    (hPr_pos : 0 < Pr)
    (h_detailed_balance : Pf = Pr * qExp q (ΔΦ / T)) :
    Pf / Pr = qExp q (ΔΦ / T) := by
  rw [h_detailed_balance]
  have hPr_ne : Pr ≠ 0 := ne_of_gt hPr_pos
  field_simp

-- ============================================================
-- Corollary 3: q-Jarzynski Bound
-- ============================================================

/-- **Corollary 3 (q-Jarzynski Bound)** — Section 5.3 of Paper 2.
    [Schematic — source: Jarzynski 1997, *PRL* 78:2690, extended to
    q-statistics via Tsallis 2009, §3.4 (q-Jensen inequality)]

    Taking the q-expectation of the Crooks relation (Theorem 7):
    ⟨exp_q(-W/T)⟩_q ≥ exp_q(-ΔΦ/T)

    where W is the work done along a non-equilibrium path.

    This bounds the free energy change from non-equilibrium work
    measurements, using q-deformed expectations.

    **Proof.** Apply the $q$-Jensen inequality to the Crooks relation:
    $\langle\exp_q(-W/T)\rangle_q \ge \exp_q(-\langle W\rangle_q/T) \ge \exp_q(-\Delta\Phi_q/T)$.
    The second inequality is the $q$-generalized second law:
    $\langle W\rangle_q \ge \Delta\Phi_q$. At $q = 1$, this recovers the
    Jarzynski equality.

    **Lean closure (Tier 2, hypothesis-bundled)**: the two inequalities
    making up the Jarzynski chain —
    (a) q-Jensen `⟨exp_q(-W/T)⟩_q ≥ exp_q(-⟨W⟩_q/T)` and
    (b) second-law comparison `exp_q(-⟨W⟩_q/T) ≥ exp_q(-ΔΦ/T)` —
    are supplied as hypotheses, and the chained bound is concluded
    by `linarith`. -/
theorem qJarzynski_bound (q T ΔΦ avgW expectation : ℝ)
    (h_qJensen : expectation ≥ qExp q (-avgW / T))
    (h_second_law_chain : qExp q (-avgW / T) ≥ qExp q (-ΔΦ / T)) :
    expectation ≥ qExp q (-ΔΦ / T) := by
  linarith

-- ============================================================
-- Proposition 8: q-Log-Sum-Exp Dual
-- ============================================================

/-- **Proposition 8 (q-Log-Sum-Exp Dual)** — Section 5.4 of Paper 2.

    The Legendre transform of the CES potential defines the
    q-log-sum-exp (inclusive value):

    LSE_q(ε/T) = T · ln_q(Σ exp_q(εⱼ/T))

    This is the q-generalization of the standard log-sum-exp.
    At q = 1: LSE₁ = T · log(Σ exp(εⱼ/T)) (standard).

    The inclusive value measures the total welfare of the choice set
    under information friction T.

    Partially proved: structural property of the Legendre transform. -/
def qLogSumExp (J : ℕ) (q T : ℝ) (ε : Fin J → ℝ) : ℝ :=
  T * qLog q (∑ j : Fin J, qExp q (ε j / T))

/-- At q = 1, qLogSumExp reduces to T · log(Σ exp(εⱼ/T)). -/
theorem qLogSumExp_at_one (T : ℝ) (ε : Fin J → ℝ) :
    qLogSumExp J 1 T ε = T * Real.log (∑ j : Fin J, Real.exp (ε j / T)) := by
  simp [qLogSumExp, qLog, qExp]

-- ============================================================
-- Corollary 4: q-Friction Bound — axiomatized
-- ============================================================

/-- **Corollary 4 (q-Friction Bound)** — Section 5.4 of Paper 2.
    [Schematic — our own cumulant argument, not a standard imported
    result. Proof sketch only.]

    From the cumulant expansion of the q-log-sum-exp:
    T >= Var_q(epsilon) / (2 * LSE_q)

    This gives a lower bound on information friction from observable
    payoff variance and inclusive value.

    **Proof sketch.** Expand $\mathrm{LSE}_q(\varepsilon/T)$ in a cumulant
    series: $\mathrm{LSE}_q = \bar{\varepsilon} + \operatorname{Var}_q/(2T) + O(T^{-2})$.
    Higher-order terms are non-negative (skewness/kurtosis contributions).
    Truncating: $T \ge \operatorname{Var}_q / [2(\mathrm{LSE}_q - \bar{\varepsilon})]$.

    **Prediction.** Cross-sector variance exceeding 2sigma above mean signals T -> T*.
    *Observable*: rolling cross-sector IP variance from FRED vs NFCI stress index;
    conditional crisis probability rises > 2x when variance exceeds 2sigma threshold.
    *Test*: logit regression of NBER recession indicator on standardized
    cross-sector variance; odds ratio > 2 for z > 2.

    **Lean closure (Tier 2, hypothesis-bundled)**: the cumulant
    expansion in "multiplied-through" form — `2T(LSE − εBar) ≥ Var_q`,
    which packages both the truncated-expansion identity and the
    non-negativity of higher-order cumulants — is supplied as
    hypothesis `h_cumulant_mul`, and the friction lower bound is
    concluded by `div_le_iff₀` + `linarith`. -/
theorem qFriction_bound (T εBar LSE Var_q : ℝ)
    (_hT : 0 < T)
    (h_LSE_gt : εBar < LSE)
    (h_cumulant_mul : Var_q ≤ 2 * T * (LSE - εBar)) :
    T ≥ Var_q / (2 * (LSE - εBar)) := by
  have h_gap_pos : 0 < LSE - εBar := by linarith
  have h2LE_pos : 0 < 2 * (LSE - εBar) := by linarith
  rw [ge_iff_le, div_le_iff₀ h2LE_pos]
  linarith

-- ============================================================
-- Proposition 9: Euler Identity Survives
-- ============================================================

/-- **Proposition 9 (Euler Identity Survives)** — Section 5.5 of Paper 2.

    For the CES potential with homogeneity degree 1 in inputs:
    Σ εⱼ · p*ⱼ = F_q (Euler's theorem for homogeneous functions)

    The q-deformation preserves the Euler identity because:
    (1) The CES production function is homogeneous of degree 1
    (2) The entropy term depends only on allocation shares, not levels
    (3) The first-order conditions respect the homogeneity structure

    **Proof.** Direct from Euler's theorem for degree-1 homogeneous functions.
    The entropy gradient ∂S_q/∂p adjusts only the allocation, not the
    payoff-weighted sum. -/
theorem euler_identity_at_uniform (hJ : 0 < J) (ε₀ : ℝ) :
    ∑ _j : Fin J, ε₀ * ((1 : ℝ) / ↑J) = ε₀ := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

-- ============================================================
-- Proposition 10: q-Onsager Symmetry — axiomatized
-- ============================================================

/-- **Proposition 10 (q-Onsager Symmetry)** — Section 5.6 of Paper 2.
    [Schematic — source: Onsager 1931, *Phys. Rev.* 37:405, extended
    to q-statistics via CES Hessian symmetry]

    The q-transport coefficients satisfy Onsager reciprocal relations:
    L_{ij}(q) = L_{ji}(q)

    where L_{ij} = dJ_i/dX_j is the transport coefficient relating
    flux J_i to force X_j in the q-deformed framework.

    This ensures time-reversal symmetry of the linear response regime,
    even under q-deformation. The symmetry follows from the q-detailed
    balance (Theorem 7) and the structure of the CES Hessian (symmetric
    matrix -> symmetric inverse).

    **Proof.** The transport coefficients $L_{ij}(q) = \partial J_i/\partial X_j$
    inherit symmetry from the CES Hessian. Since $\nabla^2\Phi_q$ is symmetric
    and q-detailed balance (Theorem 7) ensures microscopic reversibility,
    $L = T \cdot (\nabla^2\Phi_q)^{-1}$ is symmetric: $L_{ij} = L_{ji}$.

    **Lean closure (Tier 1, bundled)**: the transport-coefficient
    matrix `L` is supplied with the explicit symmetry hypothesis
    (which itself is the Onsager content — inheriting from the
    symmetric Hessian via symmetric-matrix-has-symmetric-inverse);
    the entrywise symmetry `L i j = L j i` follows definitionally. -/
theorem qOnsager_symmetry {J : ℕ} (L : Fin J → Fin J → ℝ)
    (hL_symm : ∀ i j, L i j = L j i) (i j : Fin J) :
    L i j = L j i := hL_symm i j

-- ============================================================
-- Proposition 11: q-Kramers Barrier Crossing — axiomatized
-- ============================================================

/-- **Proposition 11 (q-Kramers Barrier Crossing)** — Section 5.7 of Paper 2.
    [Schematic — source: Kramers 1940, *Physica* 7:284;
    Hanggi et al. 1990, *Rev. Mod. Phys.* 62:251; extended to
    q-statistics via Tsallis 2009, Ch. 14]

    The rate of escape from a metastable state in the CES potential is:
    k_escape ~ exp_q(-DeltaPhi_barrier / T)

    where DeltaPhi_barrier is the height of the potential barrier between
    the current state and the neighboring basin.

    For q < 1: compact support means escape is impossible beyond a
    critical barrier height (hard cutoff at T/(1-q)).
    For q > 1: power-law tails mean escape rate decays polynomially
    (not exponentially) -- much faster escape from metastable states.
    For q = 1: standard Kramers formula with exponential barrier.

    **Proof.** The saddle-point approximation of the $q$-path integral gives
    escape rate $k \sim \exp_q(-\Delta\Phi_{\mathrm{barrier}}/T)$.
    For $q < 1$: compact support means $k = 0$ when $\Delta\Phi > T/(1-q)$.
    For $q > 1$: power-law tail gives polynomial decay.
    For $q = 1$: standard Kramers formula.

    **Lean status (Tier 3, deferred)**: formalization requires the
    saddle-point approximation of a q-deformed path integral —
    specifically the q-Laplace method connecting the exponential
    barrier weighting to the q-exp rate formula. Mathlib currently
    has no path-integral or saddle-point infrastructure, and a
    faithful q-path-integral formalism is a multi-year research
    project in its own right. Left as `True := trivial` with full
    proof sketch in docstring; promotion blocked on external Mathlib
    progress (or a scoped restatement avoiding path-integrals —
    e.g., treating the escape rate as an externally-supplied
    function and deriving q-regime ordering algebraically). -/
theorem qKramers_barrier :
    -- k_escape ~ exp_q(-ΔΦ/T)
    -- q < 1: hard cutoff, no escape above T/(1-q)
    -- q = 1: exponential barrier (standard)
    -- q > 1: polynomial barrier (heavy-tailed agents escape faster)
    True := trivial

end
