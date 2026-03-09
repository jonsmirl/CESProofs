/-
  Core definitions for the Lean formalization of Paper 3:
  "Dynamics on the CES Potential Landscape"

  Defines multi-sector economy structure, conservative-dissipative
  decomposition, and key dynamical quantities. All other Paper 3 files
  import this module.

  Imports from Papers 1-2 — no redefinition of existing concepts.
-/

import CESProofs.Foundations.Defs
import CESProofs.Foundations.Hessian
import CESProofs.Potential.Defs
import CESProofs.Potential.EffectiveCurvature
import CESProofs.Foundations.GeneralWeights
import CESProofs.Foundations.FurtherProperties

open Real Finset BigOperators

noncomputable section

variable {N : ℕ}

-- ============================================================
-- Section 1: Multi-Sector Economy
-- ============================================================

/-- An N-sector economy with heterogeneous CES parameters.
    Each sector n has:
    - J_n : number of inputs (diversity)
    - ρ_n : substitution parameter (complementarity)
    - T_n : information friction (managerial noise)
    - ℓ_n : adjustment speed (mobility rate)
    - c_n : symmetric-point output level
    - d_sq_n : dispersion of inputs around symmetric point -/
structure NSectorEconomy (N : ℕ) where
  J : Fin N → ℕ
  hJ : ∀ n, 2 ≤ J n
  ρ : Fin N → ℝ
  hρ : ∀ n, ρ n < 1
  T : Fin N → ℝ
  hT : ∀ n, 0 ≤ T n
  ℓ : Fin N → ℝ
  hℓ : ∀ n, 0 < ℓ n
  c : Fin N → ℝ
  hc : ∀ n, 0 < c n
  d_sq : Fin N → ℝ
  hd : ∀ n, 0 < d_sq n

-- ============================================================
-- Section 2: Per-Sector Derived Quantities
-- ============================================================

/-- The curvature of sector n: K_n = (1-ρ_n)(J_n-1)/J_n. -/
def sectorCurvature (e : NSectorEconomy N) (n : Fin N) : ℝ :=
  curvatureK (e.J n) (e.ρ n)

/-- The critical friction of sector n:
    T*_n = 2(J_n-1)·c_n²·d²_n / K_n. -/
def sectorCriticalFriction (e : NSectorEconomy N) (n : Fin N) : ℝ :=
  criticalFriction (e.J n) (e.ρ n) (e.c n) (e.d_sq n)

/-- The effective curvature of sector n:
    K_eff_n = K_n · max(0, 1 - T_n/T*_n). -/
def sectorEffectiveCurvature (e : NSectorEconomy N) (n : Fin N) : ℝ :=
  effectiveCurvatureKeff (e.J n) (e.ρ n) (e.T n) (sectorCriticalFriction e n)

-- ============================================================
-- Section 3: Relaxation Spectrum
-- ============================================================

/-- The relaxation rate of sector n:
    λ_n = ℓ_n · (1-ρ_n)/(J_n · c_n²) · max(0, 1 - T_n/T*_n)

    This is the product of:
    - ℓ_n: adjustment speed (how fast resources move)
    - |logCesEigenvaluePerp|: log-Hessian curvature at symmetric point = (1-ρ)/(Jc²)
    - (1-T_n/T*_n)⁺: friction degradation factor

    Uses the Hessian of log F (the CES potential Φ = -log F), not of F itself.
    Units: inverse time. Higher λ_n → faster adjustment. -/
def sectorRelaxRate (e : NSectorEconomy N) (n : Fin N) : ℝ :=
  e.ℓ n * |logCesEigenvaluePerp (e.J n) (e.ρ n) (e.c n)| *
    max 0 (1 - e.T n / sectorCriticalFriction e n)

-- ============================================================
-- Section 4: Welfare Loss and Lyapunov Function
-- ============================================================

/-- Welfare loss at allocation x relative to optimum x*:
    V(x) = F(x*) - F(x) ≥ 0.
    Serves as a Lyapunov function for the adjustment dynamics. -/
def welfareLoss (Fstar Fx : ℝ) : ℝ := Fstar - Fx

/-- Welfare loss is non-negative when F(x) ≤ F(x*). -/
theorem welfareLoss_nonneg {Fstar Fx : ℝ} (h : Fx ≤ Fstar) :
    0 ≤ welfareLoss Fstar Fx := by
  simp [welfareLoss]; linarith

-- ============================================================
-- Section 5: Conservative-Dissipative Structure
-- ============================================================

/-- Predicate: a real-valued function on pairs is antisymmetric.
    Models the antisymmetric coupling J_{nm} = -J_{mn} in the
    input-output structure. -/
def IsAntisymmetric (A : Fin N → Fin N → ℝ) : Prop :=
  ∀ i j, A i j = -A j i

/-- Predicate: a real-valued function on pairs is symmetric.
    Models the friction (dissipation) matrix R_{nm} = R_{mn}. -/
def IsSymmetricMatrix (R : Fin N → Fin N → ℝ) : Prop :=
  ∀ i j, R i j = R j i

/-- Predicate: a symmetric matrix is positive semidefinite (as a quadratic form).
    Models the dissipation condition: friction always removes energy. -/
def IsPosSemidef (R : Fin N → Fin N → ℝ) : Prop :=
  ∀ v : Fin N → ℝ, 0 ≤ ∑ i, ∑ j, R i j * v i * v j

/-- The conservative-dissipative decomposition.
    Any coupling matrix A decomposes as A = J + R where:
    - J = (A - A^T)/2 is antisymmetric (energy-conserving)
    - R = (A + A^T)/2 is symmetric (energy-dissipating) -/
def antisymPart (A : Fin N → Fin N → ℝ) : Fin N → Fin N → ℝ :=
  fun i j => (A i j - A j i) / 2

def symPart (A : Fin N → Fin N → ℝ) : Fin N → Fin N → ℝ :=
  fun i j => (A i j + A j i) / 2

-- ============================================================
-- Section 6: Oscillation Parameters
-- ============================================================

/-- Damping ratio: ζ = r / ω where r is the friction rate and
    ω is the natural frequency. Controls oscillation decay:
    - ζ < 1: underdamped (oscillatory)
    - ζ = 1: critically damped
    - ζ > 1: overdamped -/
def dampingRatio (r ω : ℝ) : ℝ := r / ω

/-- Stability margin: Δ = T* - T.
    Distance from the regime boundary. Positive in sub-critical regime. -/
def stabilityMargin (T Tstar : ℝ) : ℝ := Tstar - T

/-- Stability margin is positive iff sub-critical. -/
theorem stabilityMargin_pos_iff {T Tstar : ℝ} :
    0 < stabilityMargin T Tstar ↔ T < Tstar := by
  simp only [stabilityMargin]; constructor <;> intro h <;> linarith

/-- Efficiency gap: G = K · T / (2T*).
    Measures the fraction of potential curvature lost to friction.
    At T = 0: G = 0 (no loss). At T = T*: G = K/2 (half curvature lost). -/
def efficiencyGap (K T Tstar : ℝ) : ℝ := K * T / (2 * Tstar)

/-- Efficiency gap is non-negative for non-negative inputs. -/
theorem efficiencyGap_nonneg {K T Tstar : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T) (hTs : 0 < Tstar) :
    0 ≤ efficiencyGap K T Tstar := by
  simp only [efficiencyGap]
  apply div_nonneg
  · exact mul_nonneg hK hT
  · linarith

-- ============================================================
-- Section 7: Trade Coupling and Endogenous ρ
-- ============================================================

/-- Trade coupling between sectors: J_{nm} = a_{nm} - a_{mn}.
    Antisymmetric by construction: sector n's exports to m
    minus sector m's exports to n. -/
def tradeCouplingMatrix (a : Fin N → Fin N → ℝ) : Fin N → Fin N → ℝ :=
  fun n m => a n m - a m n

/-- Trade coupling is antisymmetric. -/
theorem tradeCoupling_antisymmetric (a : Fin N → Fin N → ℝ) :
    IsAntisymmetric (tradeCouplingMatrix a) := by
  intro i j; simp only [tradeCouplingMatrix]; ring

/-- Standardization rate: the speed at which ρ converges to ρ_max
    through investment in standardized interfaces.
    dρ/dt|_std = β_S · (I/Q) · (ρ_max - ρ)
    where β_S is the standardization elasticity, I/Q is investment intensity. -/
def standardizationRate (β_S I_over_Q ρ ρ_max : ℝ) : ℝ :=
  β_S * I_over_Q * (ρ_max - ρ)

/-- Standardization rate is positive when ρ < ρ_max and parameters are positive. -/
theorem standardizationRate_pos {β_S I_over_Q ρ ρ_max : ℝ}
    (hβ : 0 < β_S) (hI : 0 < I_over_Q) (hρ : ρ < ρ_max) :
    0 < standardizationRate β_S I_over_Q ρ ρ_max := by
  simp only [standardizationRate]
  exact mul_pos (mul_pos hβ hI) (by linarith)

-- ============================================================
-- Section 8: Oscillation Energy
-- ============================================================

/-- Oscillation energy (Lagrangian form):
    L = (1/2) · Σ_n H_n · ξ_n²
    where H_n is the Hessian eigenvalue magnitude and ξ_n is the
    deviation from equilibrium in sector n.

    This is the quadratic form of the effective Hessian applied to deviations.
    Conserved (approximately) under the conservative part J of the dynamics;
    dissipated by the friction part R. -/
def oscillationEnergy (H : Fin N → ℝ) (ξ : Fin N → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ n : Fin N, H n * ξ n ^ 2

/-- Oscillation energy is non-negative when Hessian eigenvalues are non-negative. -/
theorem oscillationEnergy_nonneg {H : Fin N → ℝ} (hH : ∀ n, 0 ≤ H n)
    (ξ : Fin N → ℝ) :
    0 ≤ oscillationEnergy H ξ := by
  simp only [oscillationEnergy]
  apply mul_nonneg
  · norm_num
  · exact Finset.sum_nonneg fun n _ => mul_nonneg (hH n) (sq_nonneg _)

/-! ## Weighted N-Sector Economy
  (Merged from Dynamics/WeightedDefs.lean)

  Extends Paper 3 (Dynamics on the CES Potential Landscape) to general weights.
  Key insight: under general weights, the degenerate (J-1)-fold eigenvalue splits
  into J-1 distinct eigenvalues, producing multi-exponential relaxation.
-/

namespace CESProofs.Dynamics

/-- An N-sector economy with per-sector weight vectors.
    Extends NSectorEconomy with heterogeneous input weights at each level. -/
structure WeightedNSectorEconomy (N : ℕ) extends NSectorEconomy N where
  /-- Per-sector weight vectors: a_n : Fin J_n → ℝ -/
  a : (n : Fin N) → Fin (toNSectorEconomy.J n) → ℝ
  /-- Weights are positive -/
  ha_pos : ∀ n j, 0 < a n j
  /-- Weights sum to 1 per sector -/
  ha_sum : ∀ n, ∑ j, a n j = 1

/-- Per-sector Herfindahl index: H_n = Σ_j (a_{n,j})². -/
noncomputable def sectorHerfindahl (e : WeightedNSectorEconomy N) (n : Fin N) : ℝ :=
  herfindahlIndex (e.J n) (e.a n)

/-- Per-sector general curvature: K_n(ρ_n, a_n) = (1-ρ_n)(1-H_n). -/
noncomputable def sectorGeneralCurvature (e : WeightedNSectorEconomy N) (n : Fin N) : ℝ :=
  generalCurvatureK (e.J n) (e.ρ n) (e.a n)

/-- Per-sector general effective curvature incorporating friction:
    K_eff_n = K_n(ρ_n, a_n) · (1 - T_n/T*_n)⁺ -/
noncomputable def sectorGeneralEffectiveCurvature
    (e : WeightedNSectorEconomy N) (n : Fin N) : ℝ :=
  let K_n := sectorGeneralCurvature e n
  let Tstar_n := sectorCriticalFriction e.toNSectorEconomy n
  K_n * max 0 (1 - e.T n / Tstar_n)

/-- Herfindahl-adjusted complementarity: ρ_eff = ρ / (1 - H).
    This is the effective ordering parameter for business cycle entry. -/
noncomputable def herfindahlAdjustedRho (e : WeightedNSectorEconomy N) (n : Fin N) : ℝ :=
  e.ρ n / (1 - sectorHerfindahl e n)

/-- Knockout-triggered regime shift: critical weight above which knockout
    of a single input pushes the system past T*, causing permanent regime shift. -/
noncomputable def criticalKnockoutWeight
    (ρ T Tstar : ℝ) : ℝ :=
  if ρ ≤ 0 then 0  -- any knockout triggers failure for Leontief
  else (1 - (1 - T / Tstar) ^ ρ) ^ (1 - ρ)

/-- Per-sector general curvature is positive when weights are non-degenerate
    and ρ < 1. -/
theorem sectorGeneralCurvature_pos
    {N : ℕ} (e : WeightedNSectorEconomy N) (n : Fin N)
    (hρ : e.ρ n < 1) (hJ : 2 ≤ e.J n)
    (hH : sectorHerfindahl e n < 1) :
    0 < sectorGeneralCurvature e n := by
  unfold sectorGeneralCurvature
  exact gen_quadruple_K_pos hJ hρ (e.ha_pos n) (e.ha_sum n) hH

/-- Per-sector general curvature ≤ standard curvature (equal weights maximize). -/
theorem sectorGeneralCurvature_le_standard
    {N : ℕ} (e : WeightedNSectorEconomy N) (n : Fin N)
    (hρ : e.ρ n < 1) (hJ : 2 ≤ e.J n) :
    sectorGeneralCurvature e n ≤ sectorCurvature e.toNSectorEconomy n := by
  unfold sectorGeneralCurvature sectorCurvature
  exact equalWeights_maximize_K hJ hρ (e.ha_pos n) (e.ha_sum n)

/-- More concentrated weights reduce curvature: direct from Paper 1. -/
theorem K_decreasing_in_herfindahl_sector
    {J : ℕ} {ρ : ℝ} (hρ : ρ < 1)
    {a₁ a₂ : Fin J → ℝ}
    (hH : herfindahlIndex J a₁ < herfindahlIndex J a₂) :
    generalCurvatureK J ρ a₂ < generalCurvatureK J ρ a₁ := by
  unfold generalCurvatureK herfindahlIndex at *
  nlinarith [show 0 < 1 - ρ from by linarith]

end CESProofs.Dynamics

end
