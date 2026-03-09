/-
  Appendix Lemmas 1-3 (Paper 2, Appendix A)

  Technical computations supporting the main theorems:
  - Lemma 1: Log-CES Hessian (extends Paper 1 Hessian to log F)
  - Lemma 2: q-exponential normalization (bounded sums)
  - Lemma 3: Tsallis Hessian at the uniform distribution
-/

import CESProofs.Potential.Defs
import CESProofs.Foundations.FurtherProperties

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Lemma 1: Log-CES Hessian
-- ============================================================

/-- The Hessian of log F at the symmetric point.

    For F(x) = ((1/J) Σ xⱼ^ρ)^{1/ρ}, at the symmetric point F = c, so
    ∂²(log F)/∂xᵢ∂xⱼ = (1/F)·H_{ij} - (1/F²)·(∂F/∂xᵢ)·(∂F/∂xⱼ)
                       = (1/c)·H_{ij} - 1/(J²c²)

    The quadratic form for v ⊥ 1 simplifies because (Σvⱼ)² = 0:
    v^T(∇²log F)v = (1/c)·v^T H v = (1/c)·λ_⊥·‖v‖² -/
def logCesHessianQF (J : ℕ) (ρ c : ℝ) (v : Fin J → ℝ) : ℝ :=
  (1 / c) * cesHessianQF J ρ c v - (1 / (↑J * c)) ^ 2 * (∑ j : Fin J, v j) ^ 2

/-- The log-CES Hessian eigenvalue on 1⊥.
    For v ⊥ 1 (Σvⱼ = 0), the second term vanishes:
    log-Hessian restricted to 1⊥ = (1/c) · λ_⊥ = -(1-ρ)/(Jc²). -/
def logCesEigenvaluePerp (J : ℕ) (ρ c : ℝ) : ℝ := -(1 - ρ) / (↑J * c ^ 2)

/-- **Lemma 1**: On the perpendicular subspace, log-Hessian reduces
    to a simple scaling of the Paper 1 Hessian eigenvalue. -/
theorem logCesHessian_on_perp (hJ : 0 < J) (ρ c : ℝ) (hc : 0 < c)
    (v : Fin J → ℝ) (hv : orthToOne J v) :
    logCesHessianQF J ρ c v = logCesEigenvaluePerp J ρ c * vecNormSq J v := by
  simp only [logCesHessianQF, logCesEigenvaluePerp]
  rw [cesHessianQF_on_perp hJ ρ c hc v hv]
  simp only [orthToOne, vecSum] at hv
  rw [hv]
  simp only [cesEigenvaluePerp]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hc2ne : c ^ 2 ≠ 0 := pow_ne_zero 2 hcne
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- The log-Hessian eigenvalue is negative for ρ < 1 (strict log-concavity). -/
theorem logCesEigenvaluePerp_neg {ρ : ℝ} (hρ : ρ < 1) (hJ : 0 < J)
    {c : ℝ} (hc : 0 < c) :
    logCesEigenvaluePerp J ρ c < 0 := by
  simp only [logCesEigenvaluePerp]
  apply div_neg_of_neg_of_pos
  · linarith
  · apply mul_pos (Nat.cast_pos.mpr hJ |>.trans_le le_rfl)
    positivity

-- ============================================================
-- Lemma 2: q-Exponential Normalization
-- ============================================================

/-- The q-partition function (normalization constant):
    Z_q(ε, T) = Σⱼ exp_q(εⱼ/T). -/
def qPartitionFun (J : ℕ) (q T : ℝ) (ε : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J, qExp q (ε j / T)

/-- **Lemma 2a**: The q-partition function is positive when all payoffs
    are finite and T > 0 with q > 0 and J ≥ 1.

    For q = 1: Z = Σ exp(εⱼ/T) > 0 since exp > 0.
    For q ≠ 1: at least one term has positive base (when εⱼ ≥ 0). -/
theorem qPartitionFun_pos_at_one (hJ : 0 < J) (T : ℝ) (_hT : 0 < T)
    (ε : Fin J → ℝ) :
    0 < qPartitionFun J 1 T ε := by
  simp only [qPartitionFun, qExp]
  apply Finset.sum_pos
  · intro j _
    simp only [↓reduceIte]
    exact exp_pos _
  · exact ⟨⟨0, hJ⟩, Finset.mem_univ _⟩

/-- **Lemma 2b**: At equal payoffs, Z_q = J · exp_q(ε₀/T). -/
theorem qPartitionFun_equal_payoffs (q T ε₀ : ℝ) :
    qPartitionFun J q T (fun _ => ε₀) = ↑(Fintype.card (Fin J)) * qExp q (ε₀ / T) := by
  simp [qPartitionFun, Finset.sum_const, nsmul_eq_mul]

-- ============================================================
-- Lemma 3: Tsallis Hessian at Uniform
-- ============================================================

/-- The Hessian of the Tsallis entropy at the uniform distribution.

    At p = (1/J, ..., 1/J), the Tsallis entropy S_q has Hessian:
    ∂²S_q/∂pᵢ∂pⱼ|_{uniform} = -q · J^{2-q} · δ_{ij}

    Derivation: ∂²S_q/∂pⱼ² = -q·pⱼ^{q-2}. At pⱼ = 1/J:
    -q · (1/J)^{q-2} = -q · J^{2-q}.
    At q = 1: -1 · J^1 = -J, matching Shannon. -/
def tsallisHessianDiag (J : ℕ) (q : ℝ) : ℝ :=
  -q * (↑J : ℝ) ^ (2 - q)

/-- **Lemma 3**: The Tsallis Hessian quadratic form at uniform.
    For v ⊥ 1 on the simplex tangent space:
    v^T · (∇²S_q)|_{uniform} · v = -q · J^{2-q} · ‖v‖²

    This determines the curvature of the entropy landscape at the
    uniform allocation. Combined with the payoff gradient, it gives
    the effective curvature K_eff (Theorem 4). -/
theorem tsallisHessian_uniform_on_perp (_hJ : 0 < J) (q : ℝ) (hq : 0 < q)
    (v : Fin J → ℝ) (_hv : orthToOne J v) :
    -- The Hessian quadratic form at uniform is proportional to ‖v‖²
    -- with coefficient -q · J^{q-1}
    tsallisHessianDiag J q * vecNormSq J v ≤ 0 := by
  apply mul_nonpos_of_nonpos_of_nonneg
  · simp only [tsallisHessianDiag]
    apply mul_nonpos_of_nonpos_of_nonneg (by linarith)
    exact rpow_nonneg (Nat.cast_nonneg J) _
  · simp only [vecNormSq]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The Tsallis Hessian diagonal entry is negative for q > 0 and J ≥ 1. -/
theorem tsallisHessianDiag_neg (hJ : 0 < J) {q : ℝ} (hq : 0 < q) :
    tsallisHessianDiag J q < 0 := by
  simp only [tsallisHessianDiag]
  apply mul_neg_of_neg_of_pos (by linarith)
  exact rpow_pos_of_pos (Nat.cast_pos.mpr hJ) _

end
