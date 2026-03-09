/-
  Discrete-Time Stability of CES Tâtonnement (Edge of Stability)

  Paper 3, Section: Discrete Dynamics

  Gradient ascent on CES: x_{t+1} = x_t + η·∇F(x_t).
  Linearized on 1⊥: δ_{t+1} = (1 + η·λ_⊥)·δ_t where λ_⊥ < 0.
  Stability iff |1 - η·|λ_⊥|| < 1 iff η < 2/|λ_⊥| = 2Jc/(1-ρ).

  At the boundary η = 2/|λ_⊥|, the multiplier equals -1 and
  period-2 oscillations emerge — the "Edge of Stability" (Cohen et al. 2021).

  15 theorems, 0 sorry, 0 custom axioms.
-/

import CESProofs.Foundations.Hessian
import CESProofs.Foundations.Defs
import Mathlib.Analysis.SpecificLimits.Basic

open Real Finset BigOperators Filter

noncomputable section

-- ============================================================
-- Section 1: Abstract Iteration Stability
-- ============================================================

/-- The iteration multiplier μ = 1 - η·lam. -/
def iterationMultiplier (η lam : ℝ) : ℝ := 1 - η * lam

/-- The critical step size η* = 2/lam. -/
def criticalStepSize (lam : ℝ) : ℝ := 2 / lam

/-- **Theorem 1**: Stable (|μ| < 1) iff η < 2/lam. -/
theorem abs_iterMul_lt_one_iff {η lam : ℝ} (hlam : 0 < lam) (hη : 0 < η) :
    |iterationMultiplier η lam| < 1 ↔ η < criticalStepSize lam := by
  simp only [iterationMultiplier, criticalStepSize]
  constructor
  · intro h
    rw [abs_lt] at h
    rw [lt_div_iff₀ hlam]
    linarith [h.1]
  · intro h
    rw [lt_div_iff₀ hlam] at h
    rw [abs_lt]
    constructor <;> nlinarith [mul_pos hη hlam]

/-- **Theorem 2**: At critical step size, μ = -1. -/
theorem iterMul_eq_neg_one_at_critical {lam : ℝ} (hlam : 0 < lam) :
    iterationMultiplier (criticalStepSize lam) lam = -1 := by
  simp only [iterationMultiplier, criticalStepSize]
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  field_simp
  ring

/-- **Theorem 3**: Above critical, |μ| > 1 (unstable). -/
theorem one_lt_abs_iterMul_above_critical {η lam : ℝ} (hlam : 0 < lam)
    (hη : criticalStepSize lam < η) :
    1 < |iterationMultiplier η lam| := by
  simp only [iterationMultiplier, criticalStepSize] at *
  rw [div_lt_iff₀ hlam] at hη
  have hneg : 1 - η * lam < -1 := by linarith
  rw [abs_of_neg (by linarith)]
  linarith

/-- **Theorem 4**: Below critical, μ ∈ (-1, 1). -/
theorem iterMul_in_unit_interval {η lam : ℝ} (hlam : 0 < lam) (hη : 0 < η)
    (hlt : η < criticalStepSize lam) :
    -1 < iterationMultiplier η lam ∧ iterationMultiplier η lam < 1 :=
  abs_lt.mp ((abs_iterMul_lt_one_iff hlam hη).mpr hlt)

-- ============================================================
-- Section 2: Convergence and Divergence
-- ============================================================

/-- **Theorem 5**: When |μ| < 1, μ^n · x₀ → 0. -/
theorem iterate_tendsto_zero {μ x₀ : ℝ} (hμ : |μ| < 1) :
    Tendsto (fun n => μ ^ n * x₀) atTop (nhds 0) := by
  have h1 : Tendsto (fun n => μ ^ n) atTop (nhds 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg μ) hμ)
    simp
  rw [show (0 : ℝ) = 0 * x₀ from (zero_mul _).symm]
  exact h1.mul_const x₀

/-- **Theorem 6**: When |μ| > 1, x₀ ≠ 0, |μ^n · x₀| → ∞. -/
theorem iterate_norm_tendsto_top {μ x₀ : ℝ} (hμ : 1 < |μ|) (hx : x₀ ≠ 0) :
    Tendsto (fun n => |μ ^ n * x₀|) atTop atTop := by
  simp only [abs_mul, abs_pow]
  exact (tendsto_pow_atTop_atTop_of_one_lt hμ).atTop_mul_const (abs_pos.mpr hx)

/-- **Theorem 7**: When μ = -1, period-2 oscillation. -/
theorem period_two_oscillation (x₀ : ℝ) (n : ℕ) :
    (-1 : ℝ) ^ n * x₀ = if n % 2 = 0 then x₀ else -x₀ := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    simp only [show (k + k) % 2 = 0 from by omega, ↓reduceIte]
    rw [show k + k = 2 * k from by ring, pow_mul, neg_one_sq, one_pow, one_mul]
  · subst hk
    simp [show (2 * k + 1) % 2 = 1 from by omega, pow_succ, pow_mul, one_pow]

-- ============================================================
-- Section 3: CES Specialization
-- ============================================================

/-- **Theorem 8**: λ_⊥ < 0 for ρ < 1. -/
theorem cesEigenvaluePerp_neg {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) :
    cesEigenvaluePerp J ρ c < 0 := by
  simp only [cesEigenvaluePerp]
  apply div_neg_of_neg_of_pos
  · linarith
  · exact mul_pos (Nat.cast_pos.mpr hJ) hc

private theorem cesEigenvaluePerp_abs_pos {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) :
    0 < |cesEigenvaluePerp J ρ c| :=
  abs_pos.mpr (ne_of_lt (cesEigenvaluePerp_neg hJ hρ hc))

/-- Critical step size for CES tâtonnement on 1⊥. -/
def cesCriticalStep (J : ℕ) (ρ c : ℝ) : ℝ :=
  criticalStepSize (abs (cesEigenvaluePerp J ρ c))

/-- **Theorem 9**: η* = 2Jc/(1-ρ). -/
theorem cesCriticalStep_eq {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) :
    cesCriticalStep J ρ c = 2 * ↑J * c / (1 - ρ) := by
  simp only [cesCriticalStep, criticalStepSize, cesEigenvaluePerp]
  have hJc : 0 < (↑J : ℝ) * c := mul_pos (Nat.cast_pos.mpr hJ) hc
  rw [abs_of_neg (div_neg_of_neg_of_pos (by linarith) hJc)]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcne : c ≠ 0 := ne_of_gt hc
  have hρne : (1 : ℝ) - ρ ≠ 0 := by linarith
  field_simp

/-- **Theorem 10**: CES stable iff η < 2Jc/(1-ρ). -/
theorem ces_stable_iff {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) {η : ℝ} (hη : 0 < η) :
    abs (iterationMultiplier η (abs (cesEigenvaluePerp J ρ c))) < 1 ↔
    η < cesCriticalStep J ρ c :=
  abs_iterMul_lt_one_iff (cesEigenvaluePerp_abs_pos hJ hρ hc) hη

/-- **Theorem 11**: Period-2 oscillation at CES critical step. -/
theorem ces_period_two_at_critical {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) :
    iterationMultiplier (cesCriticalStep J ρ c) (abs (cesEigenvaluePerp J ρ c)) = -1 :=
  iterMul_eq_neg_one_at_critical (cesEigenvaluePerp_abs_pos hJ hρ hc)

-- ============================================================
-- Section 4: Economic Monotonicity
-- ============================================================

/-- **Theorem 12**: Higher ρ → larger stable region. -/
theorem cesCriticalStep_increasing_in_rho {J : ℕ} (hJ : 0 < J)
    {ρ₁ ρ₂ : ℝ} (hρ12 : ρ₁ < ρ₂) (hρ2 : ρ₂ < 1)
    {c : ℝ} (hc : 0 < c) :
    cesCriticalStep J ρ₁ c < cesCriticalStep J ρ₂ c := by
  rw [cesCriticalStep_eq hJ (by linarith) hc, cesCriticalStep_eq hJ hρ2 hc]
  exact div_lt_div_of_pos_left (by positivity) (by linarith) (by linarith)

/-- **Theorem 13**: η* = 2(J-1)c/K. -/
theorem cesCriticalStep_via_curvatureK {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) :
    cesCriticalStep J ρ c = 2 * (↑J - 1) * c / curvatureK J ρ := by
  rw [cesCriticalStep_eq (by omega) hρ hc]
  simp only [curvatureK]
  have hJpos : (0 : ℝ) < ↑J := by exact_mod_cast (show 0 < J by omega)
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  have hJ1ne : (↑J : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ↑J := by exact_mod_cast (show 1 < J by omega)
    linarith
  have hρne : (1 : ℝ) - ρ ≠ 0 := by linarith
  have hcne : c ≠ 0 := ne_of_gt hc
  field_simp

-- ============================================================
-- Section 5: Edge of Stability Bridge
-- ============================================================

/-- **Theorem 14**: At the EoS boundary, |λ_⊥| = 2/η. -/
theorem eos_at_boundary {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) {η : ℝ} (_hη : 0 < η)
    (h : η = cesCriticalStep J ρ c) :
    abs (cesEigenvaluePerp J ρ c) = 2 / η := by
  have habsne : abs (cesEigenvaluePerp J ρ c) ≠ 0 :=
    ne_of_gt (cesEigenvaluePerp_abs_pos hJ hρ hc)
  rw [h, cesCriticalStep, criticalStepSize]
  field_simp

/-- **Theorem 15**: At the EoS boundary, K = 2(J-1)c/η. -/
theorem eos_curvature_determines_step {J : ℕ} (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c) {η : ℝ} (_hη : 0 < η)
    (h : η = cesCriticalStep J ρ c) :
    curvatureK J ρ = 2 * (↑J - 1) * c / η := by
  have hK : curvatureK J ρ ≠ 0 := ne_of_gt (curvatureK_pos hJ hρ)
  rw [h, cesCriticalStep_via_curvatureK hJ hρ hc]
  have hJ1ne : (↑J : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ↑J := by exact_mod_cast (show 1 < J by omega)
    linarith
  have hcne : c ≠ 0 := ne_of_gt hc
  field_simp

end
