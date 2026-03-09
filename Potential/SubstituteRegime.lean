/-
  Substitute Regime: The ρ > 1 Theory (Anti-Complementarity)

  Dual results for strong substitutes (ρ > 1, K < 0).
  Everything reverses: concavity → convexity, superadditivity → sub-additivity,
  strategic independence → strategic instability, diversification → specialization.

  Key insight: The transition at ρ = 1 (K = 0) is the boundary between
  complementary production (ρ < 1, diversification optimal) and substitute
  production (ρ > 1, specialization optimal). This is a structural bifurcation:
  - Below ρ = 1: equal allocation is Nash stable, corner is suboptimal
  - Above ρ = 1: corner allocation is optimal, equal is unstable
  - At ρ = 1: both are equivalent (linear production)

  Economic applications:
  - Winner-take-all markets (Tirole): ρ >> 1, concentration efficient
  - Competitive exclusion (Arrow): substitute inputs → specialize
  - Platform competition: substitutable platforms → monopoly/oligopoly
  - Schelling segregation: anti-complementarity → clustering
-/

import CESProofs.Foundations.Hessian
import CESProofs.CurvatureRoles.Superadditivity
import CESProofs.Potential.Defs

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Section 1: Curvature in the Substitute Regime
-- ============================================================

/-- **SR-1**: Curvature is negative in the substitute regime.
    K = (1-ρ)(J-1)/J < 0 when ρ > 1 and J ≥ 2.
    This reverses all curvature-dependent results from the
    complementary regime. -/
theorem curvatureK_neg_substitute (hJ : 2 ≤ J) {ρ : ℝ} (hρ : 1 < ρ) :
    curvatureK J ρ < 0 := by
  simp only [curvatureK]
  apply div_neg_of_neg_of_pos
  · have hJ1 : (1 : ℝ) < ↑J := by exact_mod_cast (show 1 < J by omega)
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  · exact Nat.cast_pos.mpr (by omega)

/-- **SR-2**: The magnitude of negative curvature.
    |K| = (ρ-1)(J-1)/J — the "anti-complementarity strength". -/
theorem curvatureK_abs_substitute (hJ : 2 ≤ J) {ρ : ℝ} (hρ : 1 < ρ) :
    |curvatureK J ρ| = (ρ - 1) * (↑J - 1) / ↑J := by
  rw [abs_of_neg (curvatureK_neg_substitute hJ hρ)]
  simp only [curvatureK]; ring

-- ============================================================
-- Section 2: Hessian Convexity (Reversal of Concavity)
-- ============================================================

/-- **SR-3**: The Hessian eigenvalue on 1⊥ is positive when ρ > 1.
    This reverses the sign from the complementary regime (where it
    is negative, giving concavity). Positive eigenvalue = convexity. -/
theorem eigenvalue_perp_pos_substitute (hJ : 0 < J) {ρ : ℝ} (hρ : 1 < ρ)
    {c : ℝ} (hc : 0 < c) :
    0 < cesEigenvaluePerp J ρ c := by
  simp only [cesEigenvaluePerp]
  exact div_pos (neg_pos.mpr (by linarith)) (mul_pos (Nat.cast_pos.mpr hJ) hc)

/-- **SR-4**: Hessian is positive semidefinite on 1⊥ when ρ > 1.
    The CES aggregate is convex (not concave) for substitutes.
    Dual of `cesHessianQF_neg_semidef`. -/
theorem cesHessianQF_pos_semidef_substitute (hJ : 0 < J) {ρ : ℝ} (hρ : 1 < ρ)
    {c : ℝ} (hc : 0 < c)
    (v : Fin J → ℝ) (hv : orthToOne J v) :
    0 ≤ cesHessianQF J ρ c v := by
  rw [cesHessianQF_on_perp hJ ρ c hc v hv]
  exact mul_nonneg (le_of_lt (eigenvalue_perp_pos_substitute hJ hρ hc))
    (Finset.sum_nonneg (fun j _ => sq_nonneg (v j)))

/-- **SR-5**: Hessian is strictly positive definite on 1⊥ when ρ > 1.
    Any nonzero redistribution δ ⊥ 1 INCREASES the Hessian form.
    Dual of `ces_strict_concavity_on_perp`. -/
theorem cesHessianQF_pos_on_perp (hJ : 2 ≤ J) {ρ : ℝ} (hρ : 1 < ρ)
    {c : ℝ} (hc : 0 < c)
    (v : Fin J → ℝ) (hv : orthToOne J v) (hv_ne : ∃ j, v j ≠ 0) :
    0 < cesHessianQF J ρ c v := by
  rw [cesHessianQF_on_perp (by omega) ρ c hc v hv]
  apply mul_pos (eigenvalue_perp_pos_substitute (by omega) hρ hc)
  obtain ⟨j₀, hj₀⟩ := hv_ne
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨j₀, Finset.mem_univ _, by positivity⟩

-- ============================================================
-- Section 3: Sub-additivity (Reversal of Superadditivity)
-- ============================================================

/-- **SR-6**: Sub-additivity from convexity + homogeneity of degree one.
    For convex, hom-1 F: F(x + y) ≤ F(x) + F(y).

    Dual of `superadditivity_qualitative`. Same proof structure with
    inequality direction reversed at the convexity step.

    Economic meaning: with substitutable inputs, combining heterogeneous
    bundles is LESS productive than the sum of parts. Specialization
    (keeping bundles separate) dominates diversification (pooling). -/
theorem subadditivity_qualitative
    (F : AggFun J) (hhom : IsHomogDegOne J F)
    (hconvex : ∀ (x y : Fin J → ℝ) (t : ℝ),
      (∀ j, 0 < x j) → (∀ j, 0 < y j) → 0 ≤ t → t ≤ 1 →
      F (fun j => t * x j + (1 - t) * y j) ≤ t * F x + (1 - t) * F y)
    (x y : Fin J → ℝ) (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (hFx : 0 < F x) (hFy : 0 < F y) :
    F (fun j => x j + y j) ≤ F x + F y := by
  set s := F x + F y with hs_def
  have hs_pos : 0 < s := by linarith
  set t := F x / s with ht_def
  have ht_ge : 0 ≤ t := div_nonneg (le_of_lt hFx) (le_of_lt hs_pos)
  have ht_le : t ≤ 1 := by rw [ht_def, div_le_one₀ hs_pos]; linarith
  set x' := fun j => x j / F x
  set y' := fun j => y j / F y
  have hx' : ∀ j, 0 < x' j := fun j => div_pos (hx j) hFx
  have hy' : ∀ j, 0 < y' j := fun j => div_pos (hy j) hFy
  have hFx' : F x' = 1 := by
    have h1 := hhom x (F x)⁻¹ (inv_pos.mpr hFx)
    rw [show (fun j => (F x)⁻¹ * x j) = x' from by
      ext j; simp [x', div_eq_inv_mul]] at h1
    rw [h1, inv_mul_cancel₀ (ne_of_gt hFx)]
  have hFy' : F y' = 1 := by
    have h1 := hhom y (F y)⁻¹ (inv_pos.mpr hFy)
    rw [show (fun j => (F y)⁻¹ * y j) = y' from by
      ext j; simp [y', div_eq_inv_mul]] at h1
    rw [h1, inv_mul_cancel₀ (ne_of_gt hFy)]
  have mix_eq : ∀ j, x j + y j = s * (t * x' j + (1 - t) * y' j) := by
    intro j; simp only [x', y', ht_def]
    have hFxne : F x ≠ 0 := ne_of_gt hFx
    have hFyne : F y ≠ 0 := ne_of_gt hFy
    have hsne : s ≠ 0 := ne_of_gt hs_pos
    field_simp; ring
  have hconv := hconvex x' y' t hx' hy' ht_ge ht_le
  rw [hFx', hFy'] at hconv
  -- hconv : F(t*x' + (1-t)*y') ≤ t*1 + (1-t)*1 = 1
  have hle1 : F (fun j => t * x' j + (1 - t) * y' j) ≤ 1 := by linarith
  have hmix := hhom (fun j => t * x' j + (1 - t) * y' j) s hs_pos
  rw [show (fun j => s * (t * x' j + (1 - t) * y' j)) = (fun j => x j + y j) from by
    ext j; rw [mix_eq]] at hmix
  rw [hmix]
  calc s * F (fun j => t * x' j + (1 - t) * y' j)
      ≤ s * 1 := by apply mul_le_mul_of_nonneg_left hle1 (le_of_lt hs_pos)
    _ = s := mul_one s

-- ============================================================
-- Section 4: Strategic Instability (Reversal of Independence)
-- ============================================================

/-- **SR-7**: The Hessian form equals -K/((J-1)c) · ||δ||² for ANY ρ.
    This generalizes `strategic_bound` (which assumed ρ < 1).
    For ρ > 1: K < 0, so -K > 0, and the form is positive.
    For ρ < 1: K > 0, so -K < 0, and the form is negative. -/
theorem hessianQF_eq_negK_norm (hJ : 2 ≤ J) (ρ : ℝ)
    {c : ℝ} (hc : 0 < c)
    (δ : Fin J → ℝ) (hδ : orthToOne J δ) :
    cesHessianQF J ρ c δ =
      -(curvatureK J ρ / ((↑J - 1) * c)) * vecNormSq J δ := by
  rw [cesHessianQF_on_perp (by omega) ρ c hc δ hδ]
  simp only [cesEigenvaluePerp, curvatureK, vecNormSq]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hJm1_ne : (↑J : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ↑J := by exact_mod_cast (show 1 < J by omega)
    linarith
  have hcne : c ≠ 0 := ne_of_gt hc
  field_simp

/-- **SR-8**: Strategic instability in the substitute regime.
    For ρ > 1, any nonzero zero-sum redistribution δ ⊥ 1 yields
    POSITIVE Hessian form: coalitions CAN profitably redistribute.
    This is the dual of `strategic_independence_qualitative` (ρ < 1).

    Economic meaning: with substitutable inputs, equal allocation
    is a local minimum (not maximum) of the aggregate. Any
    perturbation along the isoquant increases output. -/
theorem strategic_instability (hJ : 2 ≤ J) {ρ : ℝ} (hρ : 1 < ρ)
    {c : ℝ} (hc : 0 < c)
    (δ : Fin J → ℝ) (hδ : orthToOne J δ) (hδ_ne : ∃ j, δ j ≠ 0) :
    0 < cesHessianQF J ρ c δ :=
  cesHessianQF_pos_on_perp hJ hρ hc δ hδ hδ_ne

-- ============================================================
-- Section 5: Specialization vs. Diversification
-- ============================================================

/-- The specialization ratio: J^{(ρ-1)/ρ}.
    Equals the ratio of corner allocation value to equal allocation value
    for the power mean M_ρ with total budget B:
      M_ρ(B,0,...,0) / M_ρ(B/J,...,B/J) = J^{(ρ-1)/ρ}.

    - ρ > 1: ratio > 1 (specialization dominates)
    - ρ < 1: ratio < 1 (diversification dominates)
    - ρ = 1: ratio = 1 (indifference) -/
def specializationRatio (J : ℕ) (ρ : ℝ) : ℝ := (↑J : ℝ) ^ ((ρ - 1) / ρ)

/-- **SR-9**: In the substitute regime, specialization dominates.
    J^{(ρ-1)/ρ} > 1 for ρ > 1 and J ≥ 2.

    This is the "corner dominates equal" theorem: concentrating all
    resources on one input produces more than equal allocation.
    Winner-take-all is efficient when inputs are substitutes. -/
theorem specialization_dominates {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : 1 < ρ) :
    1 < specializationRatio J ρ := by
  unfold specializationRatio
  have hJgt : (1 : ℝ) < ↑J := by exact_mod_cast (show 1 < J by omega)
  have hexp : (0 : ℝ) < (ρ - 1) / ρ := div_pos (by linarith) (by linarith)
  calc (1 : ℝ) = (↑J : ℝ) ^ (0 : ℝ) := (rpow_zero _).symm
    _ < (↑J : ℝ) ^ ((ρ - 1) / ρ) := rpow_lt_rpow_of_exponent_lt hJgt hexp

/-- **SR-10**: In the complementary regime, diversification dominates.
    J^{(ρ-1)/ρ} < 1 for 0 < ρ < 1 and J ≥ 2.

    Equal allocation beats corner: spreading resources across all
    complementary inputs is more productive than concentrating. -/
theorem diversification_dominates {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ}
    (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    specializationRatio J ρ < 1 := by
  unfold specializationRatio
  have hJgt : (1 : ℝ) < ↑J := by exact_mod_cast (show 1 < J by omega)
  have hexp : (ρ - 1) / ρ < 0 := div_neg_of_neg_of_pos (by linarith) hρ₀
  calc (↑J : ℝ) ^ ((ρ - 1) / ρ) < (↑J : ℝ) ^ (0 : ℝ) :=
        rpow_lt_rpow_of_exponent_lt hJgt hexp
    _ = 1 := rpow_zero _

/-- **SR-11**: At the regime boundary ρ = 1, indifference.
    J^{0} = 1: corner and equal allocations are equally productive.
    This is the critical point where complementarity vanishes. -/
theorem boundary_indifference {J : ℕ} :
    specializationRatio J 1 = 1 := by
  simp [specializationRatio, sub_self, rpow_zero]

-- ============================================================
-- Section 6: Regime Transition at ρ = 1
-- ============================================================

/-- **SR-12**: Complete regime characterization by curvature sign.
    K > 0 for ρ < 1 (complements): diversification optimal
    K = 0 for ρ = 1 (linear): indifference
    K < 0 for ρ > 1 (substitutes): specialization optimal

    The sign of K equals the sign of (1-ρ), since (J-1)/J > 0 for J ≥ 2. -/
theorem regime_trichotomy (hJ : 2 ≤ J) {ρ : ℝ} :
    (ρ < 1 → 0 < curvatureK J ρ) ∧
    (ρ = 1 → curvatureK J ρ = 0) ∧
    (1 < ρ → curvatureK J ρ < 0) :=
  ⟨fun hρ => curvatureK_pos hJ hρ,
   fun hρ => by rw [hρ]; exact curvatureK_eq_zero_of_rho_one,
   fun hρ => curvatureK_neg_substitute hJ hρ⟩

/-- **SR-13**: Anti-superadditivity gap is proportional to |K|.
    The Hessian form magnitude on 1⊥ is |K|/((J-1)c) · ||δ||².
    For ρ > 1: this is the coalition's gain from redistribution.
    For ρ < 1: this is the coalition's loss from redistribution. -/
theorem manipulation_magnitude (hJ : 2 ≤ J) (ρ : ℝ)
    {c : ℝ} (hc : 0 < c)
    (δ : Fin J → ℝ) (hδ : orthToOne J δ) :
    |cesHessianQF J ρ c δ| =
      |curvatureK J ρ| / ((↑J - 1) * c) * vecNormSq J δ := by
  rw [hessianQF_eq_negK_norm hJ ρ hc δ hδ]
  have hJ1 : (0 : ℝ) < ↑J - 1 := by
    have : (1 : ℝ) < ↑J := by exact_mod_cast (show 1 < J by omega)
    linarith
  have hvn : 0 ≤ vecNormSq J δ := by
    simp only [vecNormSq]; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  rw [abs_mul, abs_neg, abs_div, abs_of_pos (mul_pos hJ1 hc), abs_of_nonneg hvn]

-- ============================================================
-- Section 7: Escort Concentration
-- ============================================================

/-- **SR-14**: Escort weight amplifies the leading input for ρ > 1.
    For x₁ > x₂ > 0 and ρ > 1: (x₁/x₂)^ρ > (x₁/x₂)^1.
    Since the escort weight p_j ∝ x_j^ρ, higher ρ concentrates
    more weight on the largest input — the "winner-take-all" effect.

    **Proof.** For ratio r = x₁/x₂ > 1 and ρ > 1, r^ρ > r^1 = r
    by monotonicity of rpow in the exponent for base > 1. -/
theorem escort_amplifies_leader {x₁ x₂ : ℝ} (_hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hgt : x₂ < x₁) {ρ : ℝ} (hρ : 1 < ρ) :
    (x₁ / x₂) ^ (1 : ℝ) < (x₁ / x₂) ^ ρ := by
  have hratio : (1 : ℝ) < x₁ / x₂ := by rwa [one_lt_div hx₂]
  exact rpow_lt_rpow_of_exponent_lt hratio hρ

/-- **SR-15**: Escort weight compresses differences for ρ < 1.
    For x₁ > x₂ > 0 and 0 < ρ < 1: (x₁/x₂)^ρ < (x₁/x₂)^1.
    Lower ρ makes the escort distribution more uniform — the
    "diversity preference" of complementary production. -/
theorem escort_compresses_leader {x₁ x₂ : ℝ} (_hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (hgt : x₂ < x₁) {ρ : ℝ} (_hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    (x₁ / x₂) ^ ρ < (x₁ / x₂) ^ (1 : ℝ) := by
  have hratio : (1 : ℝ) < x₁ / x₂ := by rwa [one_lt_div hx₂]
  exact rpow_lt_rpow_of_exponent_lt hratio hρ₁

end
