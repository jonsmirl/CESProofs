/-
  Core definitions for the Lean formalization of Paper 2:
  "The CES Potential: Information Friction and Complementary Production"

  Defines the (ρ, T) regime diagram: CES potential Φ_q = Φ_CES(ρ) − T·S_q
  with q = ρ. Effective curvature K_eff = K·(1−T/T*)⁺.

  All other Paper 2 files import this module.
-/

import CESProofs.Foundations.Defs
import CESProofs.Foundations.Hessian

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Section 1: q-Exponential and q-Logarithm (Definition 1)
-- ============================================================

/-- The q-logarithm: ln_q(x) = (x^{1-q} - 1)/(1-q) for q ≠ 1, log(x) for q = 1.
    Generalizes the natural logarithm; recovers log as q → 1. -/
def qLog (q x : ℝ) : ℝ :=
  if q = 1 then Real.log x
  else (x ^ (1 - q) - 1) / (1 - q)

/-- The q-exponential: exp_q(x) = [1 + (1-q)x]_+^{1/(1-q)} for q ≠ 1, exp(x) for q = 1.
    The [·]_+ = max(0, ·) ensures compact support for q < 1. -/
def qExp (q x : ℝ) : ℝ :=
  if q = 1 then Real.exp x
  else (max 0 (1 + (1 - q) * x)) ^ (1 / (1 - q))

-- ============================================================
-- Section 2: q-Logarithm / q-Exponential Properties
-- ============================================================

/-- q-log at x = 1 gives 0 for any q. -/
theorem qLog_one (q : ℝ) : qLog q 1 = 0 := by
  simp only [qLog]
  split_ifs with h
  · exact Real.log_one
  · simp [rpow_def_of_pos one_pos]

/-- q-exp at x = 0 gives 1 for any q. -/
theorem qExp_zero (q : ℝ) : qExp q 0 = 1 := by
  simp only [qExp]
  split_ifs with h
  · exact Real.exp_zero
  · simp [rpow_def_of_pos one_pos]

/-- For q ≠ 1, q-log has explicit form. -/
theorem qLog_eq_of_ne {q : ℝ} (hq : q ≠ 1) (x : ℝ) :
    qLog q x = (x ^ (1 - q) - 1) / (1 - q) := by
  simp [qLog, hq]

/-- For q ≠ 1, q-exp has explicit form. -/
theorem qExp_eq_of_ne {q : ℝ} (hq : q ≠ 1) (x : ℝ) :
    qExp q x = (max 0 (1 + (1 - q) * x)) ^ (1 / (1 - q)) := by
  simp [qExp, hq]

-- ============================================================
-- Section 3: Tsallis Entropy
-- ============================================================

/-- The probability simplex: all components non-negative and sum to 1. -/
def OnSimplex (J : ℕ) (p : Fin J → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ ∑ j : Fin J, p j = 1

/-- The open simplex: all components strictly positive and sum to 1. -/
def OnOpenSimplex (J : ℕ) (p : Fin J → ℝ) : Prop :=
  (∀ j, 0 < p j) ∧ ∑ j : Fin J, p j = 1

/-- The Tsallis entropy of order q on the simplex:
    S_q(p) = (1 - Σ pⱼ^q) / (q - 1)  for q ≠ 1
    S_1(p) = -Σ pⱼ log(pⱼ)           for q = 1 (Shannon entropy).
    Uses the convention S_q ≥ 0 for probability distributions. -/
def tsallisEntropy (J : ℕ) (q : ℝ) (p : Fin J → ℝ) : ℝ :=
  if q = 1 then -∑ j : Fin J, p j * Real.log (p j)
  else (1 - ∑ j : Fin J, (p j) ^ q) / (q - 1)

/-- Tsallis entropy at the uniform distribution: S_q(1/J, ..., 1/J).
    For q ≠ 1: (1 - J^{1-q}) / (q-1).
    For q = 1: log(J). -/
theorem tsallisEntropy_uniform (hJ : 0 < J) (q : ℝ) :
    tsallisEntropy J q (fun _ => (1 : ℝ) / ↑J) =
    if q = 1 then Real.log ↑J
    else (1 - (↑J : ℝ) ^ (1 - q)) / (q - 1) := by
  simp only [tsallisEntropy]
  have hJpos : (0 : ℝ) < ↑J := Nat.cast_pos.mpr hJ
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  split_ifs with h
  · -- q = 1 case: -J · (1/J · log(1/J)) = log J
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Real.log_div one_ne_zero hJne, Real.log_one, zero_sub]
    field_simp
  · -- q ≠ 1 case: (1 - J · (1/J)^q) / (q-1) = (1 - J^{1-q}) / (q-1)
    congr 1; congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [one_div, inv_rpow (le_of_lt hJpos)]
    -- Goal: J * (J^q)⁻¹ = J^(1-q)
    rw [← rpow_neg (le_of_lt hJpos)]
    rw [show (1 : ℝ) - q = 1 + (-q) from by ring]
    rw [rpow_add hJpos, rpow_one]

-- ============================================================
-- Section 4: The CES Potential (central definition)
-- ============================================================

/-- The CES potential (information-friction generalization):
    Φ_q(p; ε, T) = Σ pⱼ·εⱼ - T·S_q(p)

    This is the objective function that agents maximize when choosing
    allocation p over options with payoffs ε, subject to information
    friction T. When T = 0, agents choose the best option deterministically.
    As T → ∞, the allocation approaches uniform.

    The parameter q = ρ links the entropy to the CES elasticity. -/
def cesPotential (J : ℕ) (q T : ℝ) (p : Fin J → ℝ) (ε : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J, p j * ε j - T * tsallisEntropy J q p

/-- The effective curvature parameter:
    K_eff = K · max(0, 1 - T/T*)

    Information friction degrades the curvature that drives all four CES roles.
    At T = T*, effective curvature vanishes — all complementarity benefits disappear. -/
def effectiveCurvatureKeff (J : ℕ) (ρ T Tstar : ℝ) : ℝ :=
  curvatureK J ρ * max 0 (1 - T / Tstar)

/-- The critical information friction (regime boundary):
    T* = 2(J-1)·c²·d² / K

    where c is the symmetric point level and d² is the dispersion.
    Above T*, effective curvature is zero and the CES aggregate behaves linearly. -/
def criticalFriction (J : ℕ) (ρ c d_sq : ℝ) : ℝ :=
  2 * (↑J - 1) * c ^ 2 * d_sq / curvatureK J ρ

-- ============================================================
-- Section 5: Basic Properties of K_eff
-- ============================================================

/-- K_eff = K when T = 0 (no information friction). -/
theorem effectiveCurvatureKeff_zero_friction (J : ℕ) (ρ Tstar : ℝ)
    (_hTs : 0 < Tstar) :
    effectiveCurvatureKeff J ρ 0 Tstar = curvatureK J ρ := by
  simp only [effectiveCurvatureKeff, zero_div, sub_zero]
  rw [max_eq_right (zero_le_one), mul_one]

/-- K_eff = 0 when T ≥ T* (information friction exceeds critical threshold).

    **Proof.** $K_{\mathrm{eff}} = K \cdot \max(0,\, 1 - T/T^*)$. When $T \geq T^*$, the ratio $T/T^* \geq 1$, so $1 - T/T^* \leq 0$, and $\max(0, 1 - T/T^*) = 0$, giving $K_{\mathrm{eff}} = K \cdot 0 = 0$. -/
theorem effectiveCurvatureKeff_above_critical (J : ℕ) (ρ T Tstar : ℝ)
    (hTs : 0 < Tstar) (hT : Tstar ≤ T) :
    effectiveCurvatureKeff J ρ T Tstar = 0 := by
  simp only [effectiveCurvatureKeff]
  have h : 1 - T / Tstar ≤ 0 := by
    rw [sub_nonpos]
    rwa [le_div_iff₀ hTs, one_mul]
  rw [max_eq_left h, mul_zero]

/-- K_eff ≥ 0 always (non-negative by the max construction). -/
theorem effectiveCurvatureKeff_nonneg (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    (T Tstar : ℝ) :
    0 ≤ effectiveCurvatureKeff J ρ T Tstar := by
  simp only [effectiveCurvatureKeff]
  apply mul_nonneg
  · exact le_of_lt (curvatureK_pos hJ hρ)
  · exact le_max_left 0 _

/-- K_eff ≤ K always (information friction only degrades curvature). -/
theorem effectiveCurvatureKeff_le_K (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T Tstar : ℝ} (hT : 0 ≤ T) (hTs : 0 < Tstar) :
    effectiveCurvatureKeff J ρ T Tstar ≤ curvatureK J ρ := by
  simp only [effectiveCurvatureKeff]
  have hK : 0 < curvatureK J ρ := curvatureK_pos hJ hρ
  have h1 : max 0 (1 - T / Tstar) ≤ 1 := by
    apply max_le (by linarith)
    rw [sub_le_self_iff]
    exact div_nonneg hT (le_of_lt hTs)
  calc curvatureK J ρ * max 0 (1 - T / Tstar)
      ≤ curvatureK J ρ * 1 := by
        exact mul_le_mul_of_nonneg_left h1 (le_of_lt hK)
    _ = curvatureK J ρ := by ring

/-- K_eff is strictly positive in the sub-critical regime T < T*. -/
theorem effectiveCurvatureKeff_pos (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {T Tstar : ℝ} (_hT : 0 ≤ T) (hTs : 0 < Tstar) (hTlt : T < Tstar) :
    0 < effectiveCurvatureKeff J ρ T Tstar := by
  simp only [effectiveCurvatureKeff]
  apply mul_pos (curvatureK_pos hJ hρ)
  rw [lt_max_iff]
  right
  rw [sub_pos, div_lt_one hTs]
  exact hTlt

-- ============================================================
-- Section 6: Simplex Properties
-- ============================================================

/-- The uniform distribution is on the open simplex. -/
theorem uniform_onOpenSimplex (hJ : 0 < J) :
    OnOpenSimplex J (fun _ : Fin J => (1 : ℝ) / ↑J) := by
  constructor
  · intro _
    exact div_pos one_pos (Nat.cast_pos.mpr hJ)
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- The open simplex implies the simplex. -/
theorem OnOpenSimplex.toSimplex {p : Fin J → ℝ} (hp : OnOpenSimplex J p) :
    OnSimplex J p :=
  ⟨fun j => le_of_lt (hp.1 j), hp.2⟩

-- ============================================================
-- Section 7: CES Potential at Equilibrium Points
-- ============================================================

/-- The CES potential at the uniform distribution with equal payoffs
    reduces to ε - T·S_q(uniform). -/
theorem cesPotential_uniform_equal (hJ : 0 < J) (q T ε₀ : ℝ) :
    cesPotential J q T (fun _ => (1 : ℝ) / ↑J) (fun _ => ε₀) =
    ε₀ - T * tsallisEntropy J q (fun _ => (1 : ℝ) / ↑J) := by
  simp only [cesPotential]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

-- ============================================================
-- Section 8: Regime Diagram Predicates
-- ============================================================

/-- The sub-critical regime: T < T*, where complementarity benefits survive. -/
def SubCriticalRegime (T Tstar : ℝ) : Prop := T < Tstar

/-- The super-critical regime: T ≥ T*, where complementarity benefits vanish. -/
def SuperCriticalRegime (T Tstar : ℝ) : Prop := Tstar ≤ T

/-- The complementary regime: ρ < 1 (inputs are complements). -/
def ComplementaryRegime (ρ : ℝ) : Prop := ρ < 1

/-- The substitute regime: ρ > 1 (inputs are substitutes). -/
def SubstituteRegime (ρ : ℝ) : Prop := 1 < ρ

end
