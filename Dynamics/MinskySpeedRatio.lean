/-
  Minsky Speed Ratio Theorems

  Formalizes the asymmetry between expansion and recession speeds
  in the Minsky cycle. The key insight: exponential convergence during
  long expansions means the system is moving slowly when crisis hits,
  while the crisis itself drives fast adjustment — creating a measurable
  speed ratio that increases with expansion duration.
-/

import Mathlib

open Real Finset BigOperators

noncomputable section

namespace CESProofs.Dynamics

-- ============================================================
-- Result MSR-1: Speed Ratio from Phase Durations
-- ============================================================

/-- **Result MSR-1 (Minsky Speed Ratio from Phase Durations).**

    On a closed cycle where total ρ excursion is the same in both
    directions, the ratio of mean speeds equals the ratio of phase
    durations (inverted). Mean recession speed = total/τ_rec,
    mean expansion speed = total/τ_exp. Their ratio simplifies to
    τ_exp/τ_rec.

    **Proof.** Direct algebra: (total/τ_rec) / (total/τ_exp) =
    (total · τ_exp) / (τ_rec · total) = τ_exp/τ_rec. -/
theorem minsky_speed_ratio_duration {total τ_exp τ_rec : ℝ}
    (ht : 0 < total) (he : 0 < τ_exp) (hr : 0 < τ_rec) :
    (total / τ_rec) / (total / τ_exp) = τ_exp / τ_rec := by
  field_simp

-- ============================================================
-- Result MSR-2: Residual Gap After Exponential Convergence
-- ============================================================

/-- **Result MSR-2 (Residual Gap Smaller After Convergence).**

    After exponential convergence over duration τ with rate α,
    the residual gap Δρ₀ · exp(−ατ) is strictly smaller than
    the initial gap Δρ₀. This is why late-expansion speed is low:
    the system has already converged most of the way to equilibrium.

    **Proof.** Since α > 0 and τ > 0, we have −ατ < 0, so
    exp(−ατ) < 1 by `Real.exp_lt_one_of_neg`. Then
    Δρ₀ · exp(−ατ) < Δρ₀ by `mul_lt_of_lt_one_right`. -/
theorem minsky_residual_gap_lt {α τ Δρ₀ : ℝ}
    (hα : 0 < α) (hτ : 0 < τ) (hΔ : 0 < Δρ₀) :
    Δρ₀ * Real.exp (-α * τ) < Δρ₀ := by
  have hneg : -α * τ < 0 := by nlinarith
  have hexp_lt : Real.exp (-α * τ) < 1 := Real.exp_lt_one_iff.mpr hneg
  exact (mul_lt_iff_lt_one_right hΔ).mpr hexp_lt

-- ============================================================
-- Result MSR-3: Instantaneous Speed Ratio
-- ============================================================

/-- **Result MSR-3 (Instantaneous Speed Ratio at Recession Onset).**

    The instantaneous adjustment speed is α · |gap|. At recession
    onset the gap is Δρ_crisis; at late expansion, the gap has
    decayed to Δρ₀ · exp(−ατ). The ratio of instantaneous speeds is:

      (α · Δρ_crisis) / (α · Δρ₀ · exp(−ατ)) = (Δρ_crisis/Δρ₀) · exp(ατ)

    This ratio grows exponentially with expansion duration τ,
    explaining why recessions feel sudden relative to expansions.

    **Proof.** Cancel α, then use exp(−ατ)⁻¹ = exp(ατ) via
    `Real.exp_neg`. -/
theorem minsky_instantaneous_ratio {α τ Δρ₀ Δρ_crisis : ℝ}
    (hα : 0 < α) (_hτ : 0 < τ) (hΔ₀ : 0 < Δρ₀) (_hΔc : 0 < Δρ_crisis) :
    (α * Δρ_crisis) / (α * (Δρ₀ * Real.exp (-α * τ))) =
    (Δρ_crisis / Δρ₀) * Real.exp (α * τ) := by
  have hα' : α ≠ 0 := ne_of_gt hα
  have hΔ₀' : Δρ₀ ≠ 0 := ne_of_gt hΔ₀
  have hexp' : Real.exp (-α * τ) ≠ 0 := ne_of_gt (Real.exp_pos _)
  rw [show α * τ = -(- α * τ) by ring, Real.exp_neg]
  field_simp

-- ============================================================
-- Result MSR-4: Speed Ratio Monotone in Duration
-- ============================================================

/-- **Result MSR-4 (Speed Ratio Monotone in Expansion Duration).**

    The instantaneous speed ratio exp(α·τ) is strictly increasing
    in τ. Longer expansions produce more abrupt-feeling recessions:
    the system has converged further, so late-expansion speed is
    lower, making the recession/expansion speed contrast larger.

    **Proof.** Monotonicity of exp: α > 0 and τ₁ < τ₂ imply
    α·τ₁ < α·τ₂, so exp(α·τ₁) < exp(α·τ₂). -/
theorem minsky_ratio_monotone_duration {α τ₁ τ₂ : ℝ}
    (hα : 0 < α) (hτ : τ₁ < τ₂) :
    Real.exp (α * τ₁) < Real.exp (α * τ₂) := by
  exact Real.exp_strictMono (by nlinarith)

-- ============================================================
-- Result MSR-5: Factor Share Dampening
-- ============================================================

/-- **Result MSR-5 (Factor Share Dampening).**

    The symmetric component of adjustment dampens the raw speed
    ratio R_ρ. Dividing by (1 + κ) where κ > 0 yields a value
    strictly less than R_ρ. The symmetric component represents
    the portion of adjustment shared equally across sectors,
    which does not contribute to the asymmetry.

    **Proof.** Since κ > 0, we have 1 + κ > 1, so
    R_ρ / (1 + κ) < R_ρ by `div_lt_self`. -/
theorem minsky_share_dampening {R_ρ κ : ℝ}
    (hR : 0 < R_ρ) (hκ : 0 < κ) :
    R_ρ / (1 + κ) < R_ρ := by
  exact div_lt_self hR (by linarith)

end CESProofs.Dynamics

end
