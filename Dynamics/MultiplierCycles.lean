/-
  Multiplier-Cycle Duality in a Multi-Sector Economy
  (Paper 3, Sections 14-15 supplement)

  Lifts the CES multiplier framework from Paper 2 to the multi-sector
  NSectorEconomy setting, and connects multiplier size to business cycle
  properties. Twenty-six results:

  1-3. Helper lemmas: sector curvature/friction positivity
  4-9. Sector multiplier and effective sector multiplier
  10-11. Aggregate effective multiplier
  12-13. Rho-ordering and efficiency-volatility tradeoff
  14-16. Multi-sector stagflation and allocation distortion
  17-19. Cross-sector shock amplification
  20-22. Crisis propagation
  23-24. Underdamped oscillation criterion
  25-26. Aggregate oscillation energy

  Key insight: the same curvature K_n that generates large multipliers
  in good times also generates large cycle amplitudes — the efficiency-
  volatility tradeoff is a theorem, not a coincidence.
-/

import CESProofs.Dynamics.Defs
import CESProofs.Potential.MacroApplications

open Real Finset BigOperators

noncomputable section

variable {N : ℕ}

-- ============================================================
-- Section 1: Helper Lemmas
-- ============================================================

/-- Sector curvature is strictly positive (from NSectorEconomy hypotheses). -/
theorem sectorCurvature_pos (e : NSectorEconomy N) (n : Fin N) :
    0 < sectorCurvature e n := by
  unfold sectorCurvature
  exact curvatureK_pos (e.hJ n) (e.hρ n)

/-- Sector critical friction is strictly positive. -/
theorem sectorCriticalFriction_pos (e : NSectorEconomy N) (n : Fin N) :
    0 < sectorCriticalFriction e n := by
  simp only [sectorCriticalFriction, criticalFriction]
  apply div_pos
  · have hJm1 : (0 : ℝ) < ↑(e.J n) - 1 := by
      have : (2 : ℝ) ≤ ↑(e.J n) := by exact_mod_cast (e.hJ n)
      linarith
    exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hJm1)
      (pow_pos (e.hc n) 2)) (e.hd n)
  · exact curvatureK_pos (e.hJ n) (e.hρ n)

/-- Sector effective curvature is non-negative. -/
theorem sectorEffectiveCurvature_nonneg (e : NSectorEconomy N) (n : Fin N) :
    0 ≤ sectorEffectiveCurvature e n := by
  unfold sectorEffectiveCurvature
  exact effectiveCurvatureKeff_nonneg (e.hJ n) (e.hρ n) (e.T n)
    (sectorCriticalFriction e n)

-- ============================================================
-- Section 2: Sector Multiplier
-- ============================================================

/-- **Sector multiplier**: the complementarity premium of sector n.
    M_n = K_n · d²_n, where K_n is the CES curvature and d²_n is
    the cross-sectional dispersion of inputs in sector n. -/
def sectorMultiplier (e : NSectorEconomy N) (n : Fin N) : ℝ :=
  sectorCurvature e n * e.d_sq n

/-- The sector multiplier is strictly positive. -/
theorem sectorMultiplier_pos (e : NSectorEconomy N) (n : Fin N) :
    0 < sectorMultiplier e n := by
  unfold sectorMultiplier
  exact mul_pos (sectorCurvature_pos e n) (e.hd n)

/-- The sector multiplier equals the CES multiplier of sector n. -/
theorem sectorMultiplier_eq_cesMultiplier (e : NSectorEconomy N) (n : Fin N) :
    sectorMultiplier e n = cesMultiplier (e.J n) (e.ρ n) (e.d_sq n) := by
  rfl

/-- **Effective sector multiplier**: the friction-degraded multiplier.
    M_eff_n = K_eff_n · d²_n, where K_eff_n = K_n · (1 - T_n/T*_n)⁺. -/
def effectiveSectorMultiplier (e : NSectorEconomy N) (n : Fin N) : ℝ :=
  sectorEffectiveCurvature e n * e.d_sq n

/-- The effective sector multiplier is non-negative. -/
theorem effectiveSectorMultiplier_nonneg (e : NSectorEconomy N) (n : Fin N) :
    0 ≤ effectiveSectorMultiplier e n := by
  unfold effectiveSectorMultiplier
  exact mul_nonneg (sectorEffectiveCurvature_nonneg e n) (le_of_lt (e.hd n))

/-- **Friction degrades the sector multiplier.** The effective multiplier
    never exceeds the frictionless multiplier: M_eff_n ≤ M_n. -/
theorem effectiveSectorMultiplier_le (e : NSectorEconomy N) (n : Fin N) :
    effectiveSectorMultiplier e n ≤ sectorMultiplier e n := by
  simp only [effectiveSectorMultiplier, sectorMultiplier,
             sectorEffectiveCurvature, sectorCurvature]
  exact mul_le_mul_of_nonneg_right
    (effectiveCurvatureKeff_le_K (e.hJ n) (e.hρ n) (e.hT n)
      (sectorCriticalFriction_pos e n))
    (le_of_lt (e.hd n))

-- ============================================================
-- Section 3: Aggregate Effective Multiplier
-- ============================================================

/-- **Aggregate effective multiplier**: the economy-wide complementarity
    premium. M_eff = Σ_n K_eff_n · d²_n. -/
def aggregateEffectiveMultiplier (e : NSectorEconomy N) : ℝ :=
  ∑ n : Fin N, effectiveSectorMultiplier e n

/-- The aggregate effective multiplier is non-negative. -/
theorem aggregateEffectiveMultiplier_nonneg (e : NSectorEconomy N) :
    0 ≤ aggregateEffectiveMultiplier e := by
  unfold aggregateEffectiveMultiplier
  exact Finset.sum_nonneg fun n _ => effectiveSectorMultiplier_nonneg e n

-- ============================================================
-- Section 4: Multiplier Rho-Ordering
-- ============================================================

/-- **Multiplier rho-ordering.** For two sectors with the same J and d²
    but different ρ, the more complementary sector (lower ρ) has a
    strictly higher multiplier. -/
theorem multiplier_rho_ordering (e : NSectorEconomy N) {n m : Fin N}
    (hJ_eq : e.J n = e.J m) (hd_eq : e.d_sq n = e.d_sq m)
    (hρ : e.ρ n < e.ρ m) :
    sectorMultiplier e m < sectorMultiplier e n := by
  simp only [sectorMultiplier, sectorCurvature]
  rw [← hJ_eq, ← hd_eq]
  exact mul_lt_mul_of_pos_right
    (curvatureK_decreasing_in_rho (e.hJ n) hρ) (e.hd n)

/-- **Efficiency-volatility tradeoff.** The more complementary sector
    has both a higher multiplier (more efficient) and higher curvature
    (more volatile business cycles). This is a theorem, not a coincidence:
    both properties flow from the same curvature parameter K. -/
theorem efficiency_volatility_tradeoff (e : NSectorEconomy N) {n m : Fin N}
    (hJ_eq : e.J n = e.J m) (hd_eq : e.d_sq n = e.d_sq m)
    (hρ : e.ρ n < e.ρ m) :
    sectorMultiplier e m < sectorMultiplier e n ∧
    sectorCurvature e m < sectorCurvature e n :=
  ⟨multiplier_rho_ordering e hJ_eq hd_eq hρ,
   by simp only [sectorCurvature]; rw [← hJ_eq];
      exact curvatureK_decreasing_in_rho (e.hJ n) hρ⟩

-- ============================================================
-- Section 5: Multi-Sector Allocation Distortion and Stagflation
-- ============================================================

/-- **Per-sector allocation distortion**: measures how far sector n's
    allocation deviates from the efficient benchmark.
    d_n = 1 - max(0, 1 - T_n/T*_n). -/
def sectorAllocationDistortion (e : NSectorEconomy N) (n : Fin N) : ℝ :=
  allocationDistortion (e.T n) (sectorCriticalFriction e n)

/-- Per-sector allocation distortion is non-negative. -/
theorem sectorAllocationDistortion_nonneg (e : NSectorEconomy N) (n : Fin N) :
    0 ≤ sectorAllocationDistortion e n := by
  unfold sectorAllocationDistortion
  exact allocationDistortion_nonneg (e.hT n) (sectorCriticalFriction_pos e n)

/-- **Multi-sector stagflation.** For each sector, rising friction
    simultaneously reduces effective curvature (output falls) and
    increases allocation distortion (prices rise from misallocation).

    The CES potential provides a single-mechanism explanation: both
    effects are driven by rising information friction degrading K_eff. -/
theorem multisector_stagflation (e : NSectorEconomy N) (n : Fin N)
    {T2 : ℝ} (hT2 : e.T n ≤ T2) :
    -- (a) Effective curvature decreases (output falls)
    effectiveCurvatureKeff (e.J n) (e.ρ n) T2 (sectorCriticalFriction e n) ≤
      sectorEffectiveCurvature e n ∧
    -- (b) Allocation distortion increases (prices rise)
    sectorAllocationDistortion e n ≤
      allocationDistortion T2 (sectorCriticalFriction e n) := by
  simp only [sectorEffectiveCurvature, sectorAllocationDistortion]
  exact ⟨bilateral_Keff_decreasing (e.hJ n) (e.hρ n)
           (sectorCriticalFriction_pos e n) hT2,
         allocationDistortion_monotone (sectorCriticalFriction_pos e n) hT2⟩

-- ============================================================
-- Section 6: Cross-Sector Shock Amplification
-- ============================================================

/-- **Cross-sector shock amplification**: the product K_eff_n · K_eff_m
    measures how strongly shocks in sector n amplify through sector m.
    Proportional to the product of effective curvatures. -/
def shockAmplification (e : NSectorEconomy N) (n m : Fin N) : ℝ :=
  sectorEffectiveCurvature e n * sectorEffectiveCurvature e m

/-- Shock amplification is symmetric: the amplification from n to m
    equals the amplification from m to n. -/
theorem shockAmplification_symm (e : NSectorEconomy N) (n m : Fin N) :
    shockAmplification e n m = shockAmplification e m n := by
  simp only [shockAmplification]; ring

/-- Shock amplification is non-negative. -/
theorem shockAmplification_nonneg (e : NSectorEconomy N) (n m : Fin N) :
    0 ≤ shockAmplification e n m := by
  unfold shockAmplification
  exact mul_nonneg (sectorEffectiveCurvature_nonneg e n)
                   (sectorEffectiveCurvature_nonneg e m)

-- ============================================================
-- Section 7: Crisis Propagation
-- ============================================================

/-- **Weakest-sector crisis.** When a sector reaches its critical friction
    (T_n ≥ T*_n), its effective curvature collapses to zero. -/
theorem weakest_sector_crisis (e : NSectorEconomy N) (n : Fin N)
    (hT : sectorCriticalFriction e n ≤ e.T n) :
    sectorEffectiveCurvature e n = 0 := by
  simp only [sectorEffectiveCurvature]
  exact effectiveCurvatureKeff_above_critical _ _ _ _
    (sectorCriticalFriction_pos e n) hT

/-- **Crisis destroys cross-sector amplification.** When one sector is in
    crisis (at or above its critical friction), all shock amplification
    channels through that sector vanish. -/
theorem crisis_destroys_amplification (e : NSectorEconomy N) {n : Fin N}
    (hT : sectorCriticalFriction e n ≤ e.T n) (m : Fin N) :
    shockAmplification e n m = 0 := by
  simp only [shockAmplification]
  rw [weakest_sector_crisis e n hT, zero_mul]

/-- **Crisis zeroes the sector multiplier.** When a sector reaches its
    critical friction, its effective multiplier vanishes. -/
theorem crisis_zeroes_multiplier (e : NSectorEconomy N) (n : Fin N)
    (hT : sectorCriticalFriction e n ≤ e.T n) :
    effectiveSectorMultiplier e n = 0 := by
  simp only [effectiveSectorMultiplier]
  rw [weakest_sector_crisis e n hT, zero_mul]

-- ============================================================
-- Section 8: Underdamped Oscillation Criterion
-- ============================================================

/-- **Underdamped oscillations.** The economy oscillates (underdamped)
    when the damping ratio ζ = r/ω is below 1, equivalently when
    the friction rate r is below the natural frequency ω.

    In the CES framework, ω is determined by the geometric mean of
    sector relaxation rates (Result 50), while r is the dissipation
    rate from the symmetric part of the coupling matrix. -/
theorem underdamped_iff {r ω : ℝ} (hω : 0 < ω) :
    dampingRatio r ω < 1 ↔ r < ω := by
  simp only [dampingRatio]
  exact div_lt_one hω

/-- At critical damping (r = ω), the damping ratio equals 1. -/
theorem critical_damping {ω : ℝ} (hω : 0 < ω) :
    dampingRatio ω ω = 1 := by
  simp only [dampingRatio]
  exact div_self (ne_of_gt hω)

-- ============================================================
-- Section 9: Aggregate Oscillation Energy
-- ============================================================

/-- **Aggregate oscillation energy** using sector effective curvatures
    as Hessian weights: E = (1/2) Σ_n K_eff_n · ξ_n².

    This is the total kinetic + potential energy in the business cycle
    oscillations across all sectors. -/
def aggregateOscillationEnergy (e : NSectorEconomy N) (ξ : Fin N → ℝ) : ℝ :=
  oscillationEnergy (fun n => sectorEffectiveCurvature e n) ξ

/-- Aggregate oscillation energy is non-negative. -/
theorem aggregateOscillationEnergy_nonneg (e : NSectorEconomy N)
    (ξ : Fin N → ℝ) :
    0 ≤ aggregateOscillationEnergy e ξ := by
  unfold aggregateOscillationEnergy
  exact oscillationEnergy_nonneg (fun n => sectorEffectiveCurvature_nonneg e n) ξ

end
