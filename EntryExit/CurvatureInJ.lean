/-
  Paper 1c, Section 2: K(J) as the Network Engine

  Theorem 1c.1: K(J) is increasing and concave in J, bounded by 1-rho.
  Proposition 1c.1: T*(J) is linear in J.
-/

import CESProofs.EntryExit.Defs
import CESProofs.Foundations.GeneralWeights

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Theorem 1c.1: K(J) Properties
-- ============================================================

/-- **Theorem 1c.1(a): K is increasing in J.**
    dK/dJ = (1-rho)/J^2 > 0 for rho < 1.
    More participants means higher curvature (diversity benefit).

    **Proof.** $K(J) = (1-\rho)(J-1)/J = (1-\rho)(1 - 1/J)$. Cross-multiplying $K(J_1) < K(J_2)$ reduces to $(J_1-1)J_2 < (J_2-1)J_1$, which simplifies to $J_1 < J_2$ after expanding and cancelling $J_1 J_2$. -/
theorem curvatureKReal_increasing {ρ : ℝ} (hρ : ρ < 1) :
    ∀ J₁ J₂ : ℝ, 0 < J₁ → J₁ < J₂ →
    curvatureKReal J₁ ρ < curvatureKReal J₂ ρ := by
  intro J₁ J₂ hJ₁ hJ₁₂
  simp only [curvatureKReal]
  have h1ρ : 0 < 1 - ρ := by linarith
  have hJ₂ : 0 < J₂ := by linarith
  -- (1-ρ)(J₁-1)/J₁ < (1-ρ)(J₂-1)/J₂
  -- ⟺ (J₁-1)/J₁ < (J₂-1)/J₂  (since 1-ρ > 0)
  -- ⟺ (J₁-1)J₂ < (J₂-1)J₁    (cross multiply)
  -- ⟺ J₁J₂ - J₂ < J₁J₂ - J₁
  -- ⟺ J₁ < J₂  ✓
  rw [div_lt_div_iff₀ hJ₁ hJ₂]
  nlinarith

/-- **Theorem 1c.1(b): K is concave in J.**
    d^2K/dJ^2 = -2(1-rho)/J^3 < 0 for rho < 1.
    Diminishing returns to adding participants. -/
theorem curvatureKReal_concave_derivative {J ρ : ℝ}
    (hJ : 0 < J) (hρ : ρ < 1) :
    -2 * (1 - ρ) / J ^ 3 < 0 := by
  apply div_neg_of_neg_of_pos
  · nlinarith
  · positivity

/-- **Theorem 1c.1(c): K is bounded above by 1-rho.**
    K(J) = (1-rho)(1 - 1/J) < 1-rho for all finite J > 1.
    Equality only in the limit J -> infinity. -/
theorem curvatureKReal_bounded {J ρ : ℝ} (hJ : 1 < J) (hρ : ρ < 1) :
    curvatureKReal J ρ < 1 - ρ := by
  simp only [curvatureKReal]
  have hJpos : 0 < J := by linarith
  have h1ρ : 0 < 1 - ρ := by linarith
  -- (1-ρ)(J-1)/J < (1-ρ) ⟺ (J-1)/J < 1 ⟺ J-1 < J
  rw [div_lt_iff₀ hJpos]
  nlinarith

/-- **Theorem 1c.1(d): K(1) = 0.**
    A single participant generates no diversity benefit. -/
theorem curvatureKReal_one (ρ : ℝ) :
    curvatureKReal 1 ρ = 0 := by
  simp [curvatureKReal]

/-- K is non-negative for J >= 1 and rho <= 1. -/
theorem curvatureKReal_nonneg {J ρ : ℝ} (hJ : 1 ≤ J) (hρ : ρ ≤ 1) :
    0 ≤ curvatureKReal J ρ := by
  simp only [curvatureKReal]
  apply div_nonneg
  · exact mul_nonneg (by linarith) (by linarith)
  · linarith

/-- K is strictly positive for J > 1 and rho < 1. -/
theorem curvatureKReal_pos {J ρ : ℝ} (hJ : 1 < J) (hρ : ρ < 1) :
    0 < curvatureKReal J ρ := by
  simp only [curvatureKReal]
  apply div_pos
  · exact mul_pos (by linarith) (by linarith)
  · linarith

-- ============================================================
-- Proposition 1c.1: T*(J) Properties
-- ============================================================

/-- **Proposition 1c.1(a): T*(J) is linear in J.**
    T*(J) = 2J * c^2 * d^2 / (1-rho).
    More participants -> higher critical friction threshold. -/
theorem criticalFriction_linear_in_J {J ρ c d_sq : ℝ}
    (hJ : 1 < J) (hρ : ρ ≠ 1) :
    criticalFrictionReal J ρ c d_sq = 2 * J * c ^ 2 * d_sq / (1 - ρ) :=
  criticalFrictionReal_eq J ρ c d_sq hJ hρ

/-- **Proposition 1c.1(b): T*(J) is increasing in J.**
    More participants raise the critical friction threshold. -/
theorem criticalFriction_increasing_in_J {J₁ J₂ ρ c d_sq : ℝ}
    (hJ₁ : 1 < J₁) (hJ₁₂ : J₁ < J₂) (hρ : ρ < 1) (hc : 0 < c) (hd : 0 < d_sq) :
    criticalFrictionReal J₁ ρ c d_sq < criticalFrictionReal J₂ ρ c d_sq := by
  have hJ₂ : 1 < J₂ := by linarith
  rw [criticalFrictionReal_eq J₁ ρ c d_sq hJ₁ (by linarith),
      criticalFrictionReal_eq J₂ ρ c d_sq hJ₂ (by linarith)]
  apply div_lt_div_of_pos_right _ (by linarith)
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  nlinarith [mul_pos hc2 hd]

/-- **Proposition 1c.1(c): The minimum viable friction.**
    T*(2) = 4c^2d^2/(1-rho) is the entry threshold:
    below this friction, even two participants generate a benefit. -/
theorem minimum_viable_friction {ρ c d_sq : ℝ} (hρ : ρ < 1) :
    criticalFrictionReal 2 ρ c d_sq = 4 * c ^ 2 * d_sq / (1 - ρ) := by
  rw [criticalFrictionReal_eq 2 ρ c d_sq (by norm_num) (by linarith)]
  ring

-- ============================================================
-- Theorem 1c.2: J-ρ Factorization and Orthogonality
-- ============================================================

/-- **Theorem 1c.2(a): The Smirl factorization.**
    K(J,ρ) = (1-ρ) · (J-1)/J factors into a ρ-only term and a J-only term.
    The two control dimensions are "orthogonal": changing ρ (complementarity)
    and changing J (variety) are independent levers for adjusting curvature. -/
theorem curvatureK_factorization (J : ℝ) (ρ : ℝ) :
    curvatureKReal J ρ = (1 - ρ) * ((J - 1) / J) := by
  simp [curvatureKReal]; ring

/-- **Theorem 1c.2(b): The Smirl Curve tradeoff vs Romer escape.**
    - ρ direction (Smirl Curve): lowering ρ raises K but (via Paper 2) lowers T*.
      There is a tradeoff: more complementarity means more curvature benefit
      but less resilience to friction.
    - J direction (Romer escape): raising J raises BOTH K and T*.
      No tradeoff: more variety is unambiguously beneficial. -/
theorem smirl_tradeoff_vs_romer_escape (J : ℝ) (hJ : 1 < J)
    {ρ : ℝ} (_hρ : ρ < 1) {c d_sq : ℝ} (_hc : 0 < c) (_hd : 0 < d_sq) :
    -- ρ direction: K up when ρ down (tradeoff with T*)
    (∀ ρ₁ ρ₂, ρ₁ < ρ₂ → ρ₂ < 1 →
      curvatureKReal J ρ₂ < curvatureKReal J ρ₁) ∧
    -- J direction: K up AND T* up (no tradeoff)
    (∀ J₁ J₂, 1 < J₁ → J₁ < J₂ →
      curvatureKReal J₁ ρ < curvatureKReal J₂ ρ ∧
      criticalFrictionReal J₁ ρ c d_sq < criticalFrictionReal J₂ ρ c d_sq) := by
  constructor
  · -- ρ direction: K decreasing in ρ
    intro ρ₁ ρ₂ hρ₁₂ hρ₂
    simp only [curvatureKReal]
    have hJpos : 0 < J := by linarith
    have hJm1 : 0 < J - 1 := by linarith
    rw [div_lt_div_iff₀ hJpos hJpos]
    have : 0 < (J - 1) * J := mul_pos hJm1 hJpos
    nlinarith [mul_pos hJm1 hJpos]
  · -- J direction: K and T* both increasing in J
    intro J₁ J₂ hJ₁ hJ₁₂
    exact ⟨curvatureKReal_increasing (by linarith) J₁ J₂ (by linarith) hJ₁₂,
           criticalFriction_increasing_in_J hJ₁ hJ₁₂ _hρ _hc _hd⟩

/-! ## Entry with General Weights
  (Merged from EntryExit/WeightedEntry.lean)

  Proposition 1c.4: Entry with general weights
  Corollary 1c.3: Equal-weight entry maximizes K-increment
-/

/-- **Proposition 1c.4 (Equal-Weight Entry Improves K).**
    Adding one more equal-weight participant always improves K.
    K(J+1, ρ) > K(J, ρ) because equal weights give H = 1/J > 1/(J+1). -/
theorem equal_weight_entry_improves_K {J : ℕ} (hJ : 1 ≤ J) {ρ : ℝ} (hρ : ρ < 1) :
    curvatureK J ρ < curvatureK (J + 1) ρ := by
  simp only [curvatureK]
  have hJpos : (0:ℝ) < ↑J := by exact_mod_cast (show 0 < J by omega)
  rw [div_lt_div_iff₀ hJpos (by push_cast; linarith)]
  push_cast; nlinarith

/-- **Corollary 1c.3 (Equal-Weight Entry Maximizes K-Increment).**
    Among all possible entry weights, equal shares maximize the
    diversity gain because H = 1/J is minimized at equal weights. -/
theorem equal_weight_entry_maximizes_K (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {a : Fin J → ℝ} (ha_pos : ∀ j, 0 < a j) (ha_sum : ∑ j : Fin J, a j = 1) :
    generalCurvatureK J ρ a ≤ curvatureK J ρ :=
  equalWeights_maximize_K hJ hρ ha_pos ha_sum

/-- The K deficit due to weight concentration is (1-rho)(H - 1/J). -/
theorem K_deficit_from_concentration (hJ : 0 < J) {ρ : ℝ}
    {a : Fin J → ℝ} (_ha_sum : ∑ j : Fin J, a j = 1) :
    curvatureK J ρ - generalCurvatureK J ρ a =
    (1 - ρ) * (herfindahlIndex J a - 1 / ↑J) := by
  simp only [curvatureK, generalCurvatureK, herfindahlIndex]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- For any non-degenerate weight vector (H < 1), K is positive. -/
theorem K_positive_nondegenerate (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {a : Fin J → ℝ} (ha_pos : ∀ j, 0 < a j) (ha_sum : ∑ j : Fin J, a j = 1)
    (hH : herfindahlIndex J a < 1) :
    0 < generalCurvatureK J ρ a :=
  gen_quadruple_K_pos hJ hρ ha_pos ha_sum hH

end
