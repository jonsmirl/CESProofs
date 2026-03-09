/-
  Superadditivity of CES (Paper 1, Section 6):
  - Theorem 5 (thm:superadd): Superadditivity from concavity + homogeneity
  - Quantitative bound: gap ≥ (C/2) · min(F(x),F(y)) · d²_w(x̂,ŷ)
  - Gap #3 resolved: false axiom replaced with correct weighted bound
-/

import CESProofs.Foundations.Hessian
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Distance Measures
-- ============================================================

/-- The share distance between two allocation vectors,
    normalizing by component sum. -/
def geodesicDistSq (J : ℕ) (x y : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J, ((x j / ∑ i, x i) - (y j / ∑ i, y i)) ^ 2

/-- L² distance between isoquant-normalized vectors:
    d²(x,y) = Σ(x_j/Fx - y_j/Fy)² where Fx, Fy are the aggregate values.
    Measures distance between projections onto the unit isoquant F = 1. -/
def isoquantDistSq (J : ℕ) (x y : Fin J → ℝ) (Fx Fy : ℝ) : ℝ :=
  ∑ j : Fin J, (x j / Fx - y j / Fy) ^ 2

/-- Weighted L² distance on the unit isoquant. The weight max(x'_j, y'_j)^{ρ-2}
    accounts for the position-dependent curvature of the CES isoquant.
    At the symmetric point all weights are 1, recovering the unweighted distance. -/
def weightedIsoquantDistSq (J : ℕ) (ρ : ℝ) (x' y' : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J, max (x' j) (y' j) ^ (ρ - 2) * (x' j - y' j) ^ 2

-- ============================================================
-- Theorem 5: Qualitative Superadditivity (thm:superadd)
-- ============================================================

/-- **Qualitative superadditivity**: For concave, homogeneous-of-degree-one F,
    F(x + y) ≥ F(x) + F(y), with equality iff x ∝ y.

    **Proof.** Normalize $x' = x/F(x)$ and $y' = y/F(y)$ so that $F(x') = F(y') = 1$ by homogeneity of degree one. Setting $t = F(x)/(F(x)+F(y))$, the sum $x + y = s \cdot (t x' + (1-t) y')$ where $s = F(x) + F(y)$. Concavity gives $F(t x' + (1-t) y') \geq 1$, and homogeneity scales the result back to $F(x+y) \geq s$. -/
theorem superadditivity_qualitative
    (F : AggFun J) (hhom : IsHomogDegOne J F)
    (hconcave : ∀ (x y : Fin J → ℝ) (t : ℝ),
      (∀ j, 0 < x j) → (∀ j, 0 < y j) → 0 ≤ t → t ≤ 1 →
      F (fun j => t * x j + (1 - t) * y j) ≥ t * F x + (1 - t) * F y)
    (x y : Fin J → ℝ) (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (hFx : 0 < F x) (hFy : 0 < F y) :
    F (fun j => x j + y j) ≥ F x + F y := by
  set s := F x + F y with hs_def
  have hs_pos : 0 < s := by linarith
  set t := F x / s with ht_def
  have ht_ge : 0 ≤ t := div_nonneg (le_of_lt hFx) (le_of_lt hs_pos)
  have ht_le : t ≤ 1 := by rw [ht_def, div_le_one₀ hs_pos]; linarith
  have h1t : 1 - t = F y / s := by
    rw [ht_def]; field_simp; linarith
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
  have hconc := hconcave x' y' t hx' hy' ht_ge ht_le
  rw [hFx', hFy'] at hconc
  have hge1 : F (fun j => t * x' j + (1 - t) * y' j) ≥ 1 := by linarith
  have := hhom (fun j => t * x' j + (1 - t) * y' j) s hs_pos
  rw [show (fun j => s * (t * x' j + (1 - t) * y' j)) = (fun j => x j + y j) from by
    ext j; rw [mix_eq]] at this
  rw [this]
  calc s * F (fun j => t * x' j + (1 - t) * y' j)
      ≥ s * 1 := by apply mul_le_mul_of_nonneg_left hge1 (le_of_lt hs_pos)
    _ = s := mul_one s

-- ============================================================
-- Helper: Harmonic Mean Bound
-- ============================================================

private lemma harmonic_mean_ge_half_min {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    min a b / 2 ≤ a * b / (a + b) := by
  rw [div_le_div_iff₀ two_pos (by linarith : 0 < a + b)]
  by_cases h : a ≤ b
  · rw [min_eq_left h]
    nlinarith [mul_le_mul_of_nonneg_left h ha.le]
  · push_neg at h
    rw [min_eq_right h.le]
    nlinarith [mul_le_mul_of_nonneg_left h.le hb.le]

-- ============================================================
-- Helper: Concave function non-negative at endpoints is non-negative
-- ============================================================

/-- A concave function on [0,1] that is non-negative at both endpoints
    is non-negative everywhere on [0,1]. -/
private lemma concaveOn_nonneg_of_endpoints {f : ℝ → ℝ}
    (hc : ConcaveOn ℝ (Set.Icc 0 1) f)
    (h0 : 0 ≤ f 0) (h1 : 0 ≤ f 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ f t := by
  have h1_mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hc2 := hc.2 h1_mem h0_mem ht0 (by linarith : 0 ≤ 1 - t) (by linarith : t + (1 - t) = 1)
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at hc2
  linarith [mul_nonneg ht0 h1, mul_nonneg (by linarith : 0 ≤ 1 - t) h0]

-- ============================================================
-- Scalar Strong Concavity of u^ρ (key analysis lemma)
-- ============================================================

/-- **Scalar strong concavity deficit of $u^\rho$**.

    For $0 < \rho < 1$, $a, b > 0$, $t \in [0,1]$:

    $$(ta + (1-t)b)^\rho - t\,a^\rho - (1-t)\,b^\rho \;\ge\; \frac{\rho(1-\rho)}{2}\,(\max(a,b))^{\rho-2}\,t(1-t)\,(a-b)^2$$

    **Proof.** Define the residual
    $h(t) = \text{deficit} - \tfrac{m}{2}\,t(1-t)(a-b)^2$
    where $m = \rho(1-\rho)\,(\max(a,b))^{\rho-2}$.
    Boundary conditions: $h(0) = h(1) = 0$.
    The second derivative is
    $h''(t) = (a-b)^2 \cdot \rho(\rho-1)\bigl[u(t)^{\rho-2} - (\max)^{\rho-2}\bigr]$
    where $u(t) = ta + (1-t)b$. Since $\rho - 2 < 0$ and $u(t) \le \max(a,b)$,
    the bracket is $\ge 0$, but $\rho(\rho-1) < 0$, so $h''(t) \le 0$.
    A concave function with zero endpoints satisfies $h(t) \ge 0$. -/
lemma rpow_concavity_deficit (ρ a b t : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ha : 0 < a) (hb : 0 < b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (t * a + (1 - t) * b) ^ ρ - t * a ^ ρ - (1 - t) * b ^ ρ ≥
      ρ * (1 - ρ) / 2 * (max a b) ^ (ρ - 2) * t * (1 - t) * (a - b) ^ 2 := by
  -- Define the mixing function u(s) = sa + (1-s)b and the modulus
  set u : ℝ → ℝ := fun s => s * a + (1 - s) * b with hu_def
  set m := ρ * (1 - ρ) / 2 * max a b ^ (ρ - 2) with hm_def
  -- Define the residual h(s) = u(s)^ρ - s·a^ρ - (1-s)·b^ρ - m·s·(1-s)·(a-b)²
  set h : ℝ → ℝ := fun s =>
    (u s) ^ ρ - s * a ^ ρ - (1 - s) * b ^ ρ - m * s * (1 - s) * (a - b) ^ 2 with hh_def
  -- Suffices: h(t) ≥ 0
  suffices hsuff : 0 ≤ h t by simp only [hh_def, hu_def] at hsuff; linarith
  -- u(s) > 0 for s ∈ [0,1]
  have hu_pos : ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 < u s := by
    intro s ⟨hs0, hs1⟩; simp only [hu_def]
    nlinarith [mul_nonneg hs0 ha.le, mul_nonneg (show 0 ≤ 1 - s by linarith) hb.le]
  have hmax_pos : 0 < max a b := lt_max_of_lt_left ha
  -- h(0) = 0, h(1) = 0
  have hh0 : h 0 = 0 := by simp [hh_def, hu_def]
  have hh1 : h 1 = 0 := by simp [hh_def, hu_def]
  -- u has derivative a - b everywhere
  have hu_hasderiv : ∀ s, HasDerivAt u (a - b) s := by
    intro s; show HasDerivAt (fun s => s * a + (1 - s) * b) (a - b) s
    have h1 : HasDerivAt (fun s => s * a) (1 * a) s := hasDerivAt_id s |>.mul_const a
    have h2 : HasDerivAt (fun s => (1 - s) * b) ((0 - 1) * b) s :=
      (hasDerivAt_const s 1 |>.sub (hasDerivAt_id s)).mul_const b
    exact (h1.add h2).congr_deriv (by ring)
  -- Define h', h'' for the second derivative test
  set h' : ℝ → ℝ := fun s =>
    ρ * (a - b) * (u s) ^ (ρ - 1) - (a ^ ρ - b ^ ρ) -
    m * (1 - 2 * s) * (a - b) ^ 2 with hh'_def
  set h'' : ℝ → ℝ := fun s =>
    ρ * (ρ - 1) * (a - b) ^ 2 * (u s) ^ (ρ - 2) +
    2 * m * (a - b) ^ 2 with hh''_def
  -- h is continuous on [0,1]
  have hh_cont : ContinuousOn h (Set.Icc 0 1) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · apply ContinuousOn.sub
        · apply ContinuousOn.rpow_const
          · exact (continuous_id.mul continuous_const |>.add
              ((continuous_const.sub continuous_id).mul continuous_const)).continuousOn
          · intro s hs; left; exact ne_of_gt (hu_pos s hs)
        · exact continuousOn_id.mul continuousOn_const
      · exact (continuousOn_const.sub continuousOn_id).mul continuousOn_const
    · exact ((continuousOn_const.mul continuousOn_id).mul
        (continuousOn_const.sub continuousOn_id)).mul continuousOn_const
  -- h has first derivative h' on interior
  have hh_deriv : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt h (h' s) (interior (Set.Icc 0 1)) s := by
    intro s hs; rw [interior_Icc] at hs ⊢
    obtain ⟨hs0, hs1⟩ := hs
    have hus_pos := hu_pos s ⟨hs0.le, hs1.le⟩
    have h1 : HasDerivWithinAt (fun s => (u s) ^ ρ)
        ((a - b) * ρ * (u s) ^ (ρ - 1)) (Set.Ioo 0 1) s :=
      (hu_hasderiv s).hasDerivWithinAt.rpow_const (Or.inl (ne_of_gt hus_pos))
    have h2 : HasDerivWithinAt (fun s => s * a ^ ρ) (1 * a ^ ρ) (Set.Ioo 0 1) s :=
      (hasDerivWithinAt_id s _).mul_const _
    have h3 : HasDerivWithinAt (fun s => (1 - s) * b ^ ρ) ((0 - 1) * b ^ ρ) (Set.Ioo 0 1) s :=
      ((hasDerivWithinAt_const s _ 1).sub (hasDerivWithinAt_id s _)).mul_const _
    have h4 : HasDerivWithinAt (fun s => m * s * (1 - s) * (a - b) ^ 2)
        (m * (1 - 2 * s) * (a - b) ^ 2) (Set.Ioo 0 1) s := by
      -- Compute as polynomial: m*(a-b)²*(s - s²), derivative m*(a-b)²*(1 - 2s)
      set C := m * (a - b) ^ 2
      have h_id : HasDerivAt (fun s : ℝ => C * s) (C * 1) s :=
        (hasDerivAt_id s).const_mul C
      have h_sq : HasDerivAt (fun s : ℝ => C * s ^ 2) (C * (2 * s)) s := by
        have h := (hasDerivAt_pow 2 s).const_mul C
        simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h; exact h
      have h_poly : HasDerivAt (fun s : ℝ => C * s - C * s ^ 2)
          (C * 1 - C * (2 * s)) s := h_id.sub h_sq
      have h_eq_fun : (fun s : ℝ => C * s - C * s ^ 2) =
          (fun s => m * s * (1 - s) * (a - b) ^ 2) := by ext s; simp [C]; ring
      have h_eq_deriv : C * 1 - C * (2 * s) = m * (1 - 2 * s) * (a - b) ^ 2 := by
        simp [C]; ring
      exact (h_eq_fun ▸ h_eq_deriv ▸ h_poly).hasDerivWithinAt
    exact ((h1.sub h2).sub h3).sub h4 |>.congr_deriv (by ring)
  -- h has second derivative h'' on interior
  have hh'_deriv : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1),
      HasDerivWithinAt h' (h'' s) (interior (Set.Icc 0 1)) s := by
    intro s hs; rw [interior_Icc] at hs ⊢
    obtain ⟨hs0, hs1⟩ := hs
    have hus_pos := hu_pos s ⟨hs0.le, hs1.le⟩
    -- d/ds [ρ(a-b) · u(s)^{ρ-1}] = ρ(a-b) · (a-b)(ρ-1) · u(s)^{ρ-2}
    have h1 : HasDerivWithinAt (fun s => ρ * (a - b) * (u s) ^ (ρ - 1))
        (ρ * (a - b) * ((a - b) * (ρ - 1) * (u s) ^ (ρ - 1 - 1))) (Set.Ioo 0 1) s :=
      ((hu_hasderiv s).hasDerivWithinAt.rpow_const
        (Or.inl (ne_of_gt hus_pos))).const_mul _
    -- d/ds [-(a^ρ - b^ρ)] = 0; d/ds [-m(1-2s)(a-b)²] = 2m(a-b)²
    have h2 : HasDerivWithinAt (fun s => -(m * (1 - 2 * s) * (a - b) ^ 2))
        (2 * m * (a - b) ^ 2) (Set.Ioo 0 1) s := by
      -- Rewrite as linear polynomial: 2*D*s - D where D = m*(a-b)²
      set D := m * (a - b) ^ 2
      have h_lin : HasDerivAt (fun s : ℝ => 2 * D * s) (2 * D) s := by
        have h := (hasDerivAt_id s).const_mul (2 * D)
        simp only [id, mul_one] at h; exact h
      have h_const : HasDerivAt (fun s : ℝ => D) (0 : ℝ) s := hasDerivAt_const s D
      have h_poly : HasDerivAt (fun s : ℝ => 2 * D * s - D) (2 * D - 0) s :=
        h_lin.sub h_const
      have h_eq_fun : (fun s : ℝ => 2 * D * s - D) =
          (fun s => -(m * (1 - 2 * s) * (a - b) ^ 2)) := by ext s; simp [D]; ring
      have h_eq_deriv : 2 * D - 0 = 2 * m * (a - b) ^ 2 := by simp [D]; ring
      exact (h_eq_fun ▸ h_eq_deriv ▸ h_poly).hasDerivWithinAt
    -- h' = term1 - const - quad, so h'' combines term1_deriv + 0 + quad_deriv
    have h3 := (h1.sub (hasDerivWithinAt_const s (Set.Ioo 0 1) (a ^ ρ - b ^ ρ))).add h2
    exact h3.congr_deriv (by show _ = h'' s; simp only [hh''_def]; ring)
  -- h'' ≤ 0 on interior: h''(s) = (a-b)² · ρ(ρ-1) · [u(s)^{ρ-2} - max^{ρ-2}]
  have hh''_nonpos : ∀ s ∈ interior (Set.Icc (0 : ℝ) 1), h'' s ≤ 0 := by
    intro s hs; rw [interior_Icc] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have hus_pos := hu_pos s ⟨hs0.le, hs1.le⟩
    -- u(s) ≤ max(a,b)
    have hus_le : u s ≤ max a b := by
      simp only [hu_def]
      calc s * a + (1 - s) * b
          ≤ s * max a b + (1 - s) * max a b := by
            gcongr; exact le_max_left a b; linarith; exact le_max_right a b
        _ = max a b := by ring
    -- ρ - 2 < 0, so u^{ρ-2} ≥ max^{ρ-2}
    have hus_rpow : max a b ^ (ρ - 2) ≤ (u s) ^ (ρ - 2) :=
      rpow_le_rpow_of_nonpos hus_pos hus_le (by linarith : ρ - 2 ≤ 0)
    -- Factor h''(s) = (a-b)² · ρ(ρ-1) · [u^{ρ-2} - max^{ρ-2}]
    show h'' s ≤ 0
    simp only [hh''_def, hm_def]
    have hfactor :
        ρ * (ρ - 1) * (a - b) ^ 2 * (u s) ^ (ρ - 2) +
        2 * (ρ * (1 - ρ) / 2 * max a b ^ (ρ - 2)) * (a - b) ^ 2 =
        ρ * (ρ - 1) * ((u s) ^ (ρ - 2) - max a b ^ (ρ - 2)) * (a - b) ^ 2 := by ring
    rw [hfactor]
    -- ρ(ρ-1) < 0, diff ≥ 0, (a-b)² ≥ 0, so product ≤ 0
    have hρρ1_neg : ρ * (ρ - 1) < 0 := by nlinarith
    have hdiff_nn : 0 ≤ (u s) ^ (ρ - 2) - max a b ^ (ρ - 2) := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hρρ1_neg.le hdiff_nn) (sq_nonneg _)
  -- h is concave on [0,1]
  have hh_concave : ConcaveOn ℝ (Set.Icc 0 1) h :=
    concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1) hh_cont hh_deriv hh'_deriv hh''_nonpos
  -- h(t) ≥ 0 from concavity + zero endpoints
  exact concaveOn_nonneg_of_endpoints hh_concave (le_of_eq hh0.symm) (le_of_eq hh1.symm) ht0 ht1

-- ============================================================
-- Bernoulli Inequality for rpow
-- ============================================================

/-- Bernoulli inequality: S^{1/ρ} ≥ 1 + (1/ρ)(S-1) for S ≥ 1 and 0 < ρ < 1. -/
private lemma bernoulli_rpow_ge_linear {ρ S : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hS : 1 ≤ S) :
    S ^ (1 / ρ) ≥ 1 + 1 / ρ * (S - 1) := by
  have hs_ge : -1 ≤ S - 1 := by linarith
  have hp_ge : 1 ≤ 1 / ρ := by rw [le_div_iff₀ hρ0]; linarith
  have := one_add_mul_self_le_rpow_one_add hs_ge hp_ge
  rwa [show 1 + (S - 1) = S from by ring] at this

-- ============================================================
-- CES Isoquant Strong Concavity (weighted, correct bound)
-- ============================================================

/-- **Strong concavity of CES on the unit isoquant** (weighted version).

    For x', y' on the unit isoquant (F = 1) of the power mean M_ρ with ρ ∈ (0,1):

      F(t·x' + (1-t)·y') - 1 ≥ ((1-ρ)/(2J)) · t(1-t) · weightedIsoquantDistSq

    Proof chain: Bernoulli + scalar concavity deficit summed componentwise. -/
theorem powerMean_isoquant_strong_concavity_weighted (J : ℕ) (hJ : 2 ≤ J)
    (ρ : ℝ) (hρ : ρ < 1) (hρ0 : 0 < ρ)
    (x' y' : Fin J → ℝ) (hx' : ∀ j, 0 < x' j) (hy' : ∀ j, 0 < y' j)
    (hFx : powerMean J ρ (ne_of_gt hρ0) x' = 1)
    (hFy : powerMean J ρ (ne_of_gt hρ0) y' = 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hmix : ∀ j, 0 < t * x' j + (1 - t) * y' j) :
    powerMean J ρ (ne_of_gt hρ0) (fun j => t * x' j + (1 - t) * y' j) - 1 ≥
      (1 - ρ) / (2 * ↑J) * t * (1 - t) *
        weightedIsoquantDistSq J ρ x' y' := by
  set hρne := ne_of_gt hρ0
  set mix := fun j => t * x' j + (1 - t) * y' j with hmix_def
  have hJpos : (0 : ℝ) < (↑J : ℝ) := Nat.cast_pos.mpr (by omega)
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  -- Extract inner sums from isoquant conditions
  -- powerMean = ((1/J) * Σ x'^ρ)^{1/ρ} = 1 means (1/J) * Σ x'^ρ = 1
  have hsum_x_pos : 0 < (1 : ℝ) / ↑J * ∑ j : Fin J, (x' j) ^ ρ := by
    apply mul_pos (div_pos one_pos hJpos)
    exact Finset.sum_pos (fun j _ => rpow_pos_of_pos (hx' j) ρ)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  -- If z > 0 and z^{1/ρ} = 1, then z = (z^{1/ρ})^ρ = 1^ρ = 1
  have rpow_eq_one_iff {z : ℝ} (hz : 0 < z) (h : z ^ (1 / ρ) = 1) : z = 1 := by
    have := congr_arg (· ^ ρ) h
    simp only [one_rpow] at this
    rwa [← rpow_mul hz.le, one_div, inv_mul_cancel₀ hρne, rpow_one] at this
  have hFx_inner : (1 : ℝ) / ↑J * ∑ j : Fin J, (x' j) ^ ρ = 1 := by
    have h := hFx; simp only [powerMean] at h
    exact rpow_eq_one_iff hsum_x_pos h
  have hsum_y_pos : 0 < (1 : ℝ) / ↑J * ∑ j : Fin J, (y' j) ^ ρ := by
    apply mul_pos (div_pos one_pos hJpos)
    exact Finset.sum_pos (fun j _ => rpow_pos_of_pos (hy' j) ρ)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hFy_inner : (1 : ℝ) / ↑J * ∑ j : Fin J, (y' j) ^ ρ = 1 := by
    have h := hFy; simp only [powerMean] at h
    exact rpow_eq_one_iff hsum_y_pos h
  -- S = (1/J)Σ (mix_j)^ρ
  set S := (1 : ℝ) / ↑J * ∑ j : Fin J, (mix j) ^ ρ with hS_def
  -- F(mix) = S^{1/ρ}
  have hFmix : powerMean J ρ hρne mix = S ^ (1 / ρ) := by
    simp only [powerMean, hS_def, hmix_def]
  -- Each component gives a concavity deficit via rpow_concavity_deficit
  have hcomp : ∀ j : Fin J,
      (mix j) ^ ρ - t * (x' j) ^ ρ - (1 - t) * (y' j) ^ ρ ≥
      ρ * (1 - ρ) / 2 * max (x' j) (y' j) ^ (ρ - 2) * t * (1 - t) *
        (x' j - y' j) ^ 2 :=
    fun j => rpow_concavity_deficit ρ (x' j) (y' j) t hρ0 hρ (hx' j) (hy' j) ht0 ht1
  -- Sum over components
  have hsum_deficit :
      (∑ j : Fin J, (mix j) ^ ρ) - t * (∑ j : Fin J, (x' j) ^ ρ) -
        (1 - t) * (∑ j : Fin J, (y' j) ^ ρ) ≥
      ρ * (1 - ρ) / 2 * t * (1 - t) *
        ∑ j : Fin J, max (x' j) (y' j) ^ (ρ - 2) * (x' j - y' j) ^ 2 := by
    have h1 : (∑ j : Fin J, (mix j) ^ ρ) - t * ∑ j : Fin J, (x' j) ^ ρ -
        (1 - t) * ∑ j : Fin J, (y' j) ^ ρ =
        ∑ j : Fin J, ((mix j) ^ ρ - t * (x' j) ^ ρ - (1 - t) * (y' j) ^ ρ) := by
      simp [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have h2 : ρ * (1 - ρ) / 2 * t * (1 - t) *
        ∑ j : Fin J, max (x' j) (y' j) ^ (ρ - 2) * (x' j - y' j) ^ 2 =
        ∑ j : Fin J, (ρ * (1 - ρ) / 2 * max (x' j) (y' j) ^ (ρ - 2) * t * (1 - t) *
          (x' j - y' j) ^ 2) := by
      simp [Finset.mul_sum]; congr 1; ext j; ring
    rw [h1, h2]
    exact Finset.sum_le_sum fun j _ => hcomp j
  -- S - 1 ≥ (ρ(1-ρ)/(2J)) · t(1-t) · wdist
  have hS_deficit :
      S - 1 ≥ ρ * (1 - ρ) / (2 * ↑J) * t * (1 - t) *
        weightedIsoquantDistSq J ρ x' y' := by
    simp only [weightedIsoquantDistSq, hS_def]
    -- S - 1 = (1/J)(Σ mix^ρ - t·Σx'^ρ - (1-t)·Σy'^ρ)
    set wsum := ∑ j : Fin J, max (x' j) (y' j) ^ (ρ - 2) * (x' j - y' j) ^ 2
    have h_invJ : (0 : ℝ) < 1 / ↑J := div_pos one_pos hJpos
    -- Express 1 in terms of the sums
    have h_lhs : 1 / ↑J * ∑ j : Fin J, (mix j) ^ ρ - 1 =
        1 / ↑J * ((∑ j : Fin J, (mix j) ^ ρ) - t * ∑ j : Fin J, (x' j) ^ ρ -
          (1 - t) * ∑ j : Fin J, (y' j) ^ ρ) := by
      nlinarith [hFx_inner, hFy_inner]
    have h_rhs : ρ * (1 - ρ) / (2 * ↑J) * t * (1 - t) * wsum =
        1 / ↑J * (ρ * (1 - ρ) / 2 * t * (1 - t) * wsum) := by
      field_simp
    rw [h_lhs, h_rhs]
    exact mul_le_mul_of_nonneg_left hsum_deficit h_invJ.le
  -- S ≥ 1
  have wdist_nn : 0 ≤ weightedIsoquantDistSq J ρ x' y' := by
    apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (rpow_nonneg (le_max_of_le_left (hx' j).le) _) (sq_nonneg _)
  have hS_ge1 : 1 ≤ S := by
    have h1 : (0 : ℝ) ≤ ρ * (1 - ρ) / (2 * ↑J) := by
      apply div_nonneg (mul_nonneg hρ0.le (by linarith : 0 ≤ 1 - ρ))
      exact mul_nonneg two_pos.le hJpos.le
    nlinarith [mul_nonneg h1 (mul_nonneg (mul_nonneg ht0 (by linarith : 0 ≤ 1 - t)) wdist_nn)]
  -- S^{1/ρ} - 1 ≥ (1/ρ)(S-1) by Bernoulli
  have hBern : S ^ (1 / ρ) ≥ 1 + 1 / ρ * (S - 1) :=
    bernoulli_rpow_ge_linear hρ0 hρ hS_ge1
  -- Chain the bounds
  rw [hFmix]
  calc S ^ (1 / ρ) - 1
      ≥ 1 / ρ * (S - 1) := by linarith
    _ ≥ 1 / ρ * (ρ * (1 - ρ) / (2 * ↑J) * t * (1 - t) *
        weightedIsoquantDistSq J ρ x' y') := by
        exact mul_le_mul_of_nonneg_left hS_deficit (by positivity : (0 : ℝ) ≤ 1 / ρ)
    _ = (1 - ρ) / (2 * ↑J) * t * (1 - t) *
        weightedIsoquantDistSq J ρ x' y' := by
      field_simp

-- ============================================================
-- Quantitative Superadditivity Bound (resolves Gap #3)
-- ============================================================

/-- **Quantitative superadditivity bound** (Proposition 5.3 in the paper).

    For any aggregation function F that is homogeneous of degree one
    and satisfies a strong concavity bound with coefficient C on the
    unit isoquant (using a weighted distance measure):

      F(x + y) - F(x) - F(y) ≥ (C/2) · min(F(x), F(y)) · d²_w(x̂, ŷ) -/
theorem superadditivity_quantitative_bound
    (F : AggFun J) (hhom : IsHomogDegOne J F)
    (x y : Fin J → ℝ) (hx : ∀ j, 0 < x j) (hy : ∀ j, 0 < y j)
    (hFx : 0 < F x) (hFy : 0 < F y)
    (C : ℝ) (hC : 0 ≤ C)
    (dist : (Fin J → ℝ) → (Fin J → ℝ) → ℝ)
    (hdist_nn : ∀ x' y', 0 ≤ dist x' y')
    (hstrong : ∀ (x' y' : Fin J → ℝ) (t : ℝ),
      (∀ j, 0 < x' j) → (∀ j, 0 < y' j) →
      F x' = 1 → F y' = 1 →
      0 ≤ t → t ≤ 1 →
      (∀ j, 0 < t * x' j + (1 - t) * y' j) →
      F (fun j => t * x' j + (1 - t) * y' j) - 1 ≥
        C * t * (1 - t) * dist x' y') :
    F (fun j => x j + y j) - F x - F y ≥
      C / 2 * min (F x) (F y) * dist (fun j => x j / F x) (fun j => y j / F y) := by
  set s := F x + F y with hs_def
  have hs_pos : 0 < s := by linarith
  have hsne : s ≠ 0 := ne_of_gt hs_pos
  set t := F x / s with ht_def
  have ht_ge : 0 ≤ t := div_nonneg hFx.le hs_pos.le
  have ht_le : t ≤ 1 := by rw [ht_def, div_le_one₀ hs_pos]; linarith
  have h1t : 1 - t = F y / s := by rw [ht_def]; field_simp; linarith
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
  have hmix : ∀ j, 0 < t * x' j + (1 - t) * y' j := by
    intro j
    by_cases h0 : t = 0
    · simp only [h0, zero_mul, zero_add, one_mul, sub_zero]; exact hy' j
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne ht_ge (Ne.symm h0)) (hx' j))
        (mul_nonneg (by linarith) (hy' j).le)
  have mix_eq : ∀ j, x j + y j = s * (t * x' j + (1 - t) * y' j) := by
    intro j; simp only [x', y', ht_def]; field_simp; ring
  have hFxy := hhom (fun j => t * x' j + (1 - t) * y' j) s hs_pos
  rw [show (fun j => s * (t * x' j + (1 - t) * y' j)) = (fun j => x j + y j) from by
    ext j; rw [mix_eq]] at hFxy
  set dsq := dist x' y'
  have hdeficit := hstrong x' y' t hx' hy' hFx' hFy' ht_ge ht_le hmix
  have hgap : F (fun j => x j + y j) - F x - F y =
      s * (F (fun j => t * x' j + (1 - t) * y' j) - 1) := by
    rw [hFxy]; ring
  have hdsq_nn : 0 ≤ dsq := hdist_nn x' y'
  rw [hgap]
  have hstep1 : s * (F (fun j => t * x' j + (1 - t) * y' j) - 1) ≥
      s * (C * t * (1 - t) * dsq) :=
    mul_le_mul_of_nonneg_left hdeficit hs_pos.le
  have hstep2 : s * (C * t * (1 - t) * dsq) =
      C * (F x * F y / s) * dsq := by
    rw [ht_def, h1t]; field_simp
  have hHM : min (F x) (F y) / 2 ≤ F x * F y / s :=
    harmonic_mean_ge_half_min hFx hFy
  calc s * (F (fun j => t * x' j + (1 - t) * y' j) - 1)
      ≥ s * (C * t * (1 - t) * dsq) := hstep1
    _ = C * (F x * F y / s) * dsq := hstep2
    _ ≥ C * (min (F x) (F y) / 2) * dsq :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHM hC) hdsq_nn
    _ = C / 2 * min (F x) (F y) * dsq := by ring

end
