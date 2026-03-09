/-
  Correlation Convergence at the Regime Boundary

  At T → T*, effective curvature K_eff = K·(1-T/T*)⁺ → 0 linearly.
  Combined with compound symmetry (CES at symmetric equilibrium) and
  curvature conservation (|λ_F|·|λ_C| = const from FurtherProperties),
  this implies a dual prediction:

  PRICES:     cor → 1         at rate 1 - cor ~ (1 - T/T*)       [β = 1]
  QUANTITIES: cor → -1/(J-1)  at rate cor + 1/(J-1) ~ (1 - T/T*) [β = 1]

  Mechanism: as production curvature K_eff vanishes, curvature conservation
  forces cost curvature → ∞. Price fluctuations are squeezed into the
  aggregate (1) direction → cor_price → 1. Production fluctuations
  spread freely across 1-perp → cor_qty → -1/(J-1).

  The linear rate β = 1 discriminates from GARCH/DCC (exponential).

  Combined with the cumulant tower (CumulantTower.lean): near T*,
  κ_n → 0 for all n ≥ 2 AND cor_price → 1. The economy simultaneously
  loses information capacity and cross-sectional diversity, controlled
  by the same K_eff → 0. This is the "total information blackout."

  All results are pure algebra on the compound symmetry correlation
  formula. No ODE theory or Riemannian geometry is needed.
-/

import CESProofs.Foundations.Defs

open Real

noncomputable section

-- ============================================================
-- Section 1: Compound Symmetry Correlation Formula
-- ============================================================

/-- Compound symmetry correlation between distinct variables.

    In a J-dimensional system with covariance Sigma = T·(Hess Phi)^{-1}
    at the symmetric CES equilibrium, the Hessian has compound symmetry:
    eigenvalue lambda_1 along 1 (multiplicity 1) and lambda_perp along
    1-perp (multiplicity J-1).

    The variance ratio r = sigma^2_perp / sigma^2_1 = lambda_1 / lambda_perp
    determines the pairwise correlation:

    cor(i,j) = (1 - r) / (1 + (J-1)r)

    Boundary behavior:
    - r = 0: cor = 1  (all variance along common factor)
    - r = 1: cor = 0  (uncorrelated)
    - r -> infinity: cor -> -1/(J-1) (equicorrelation floor) -/
def compoundSymmetryCorr (r : ℝ) (J : ℕ) : ℝ :=
  (1 - r) / (1 + (↑J - 1) * r)

-- ============================================================
-- Section 2: Boundary Values
-- ============================================================

/-- At r = 0, correlation is 1 (all variance along the common factor).
    This is the PRICE limit near T*: curvature conservation forces
    cost curvature to infinity, squeezing price fluctuations into
    the aggregate direction. -/
theorem compoundSymmetryCorr_zero (J : ℕ) :
    compoundSymmetryCorr 0 J = 1 := by
  simp [compoundSymmetryCorr]

/-- At r = 1, correlation is 0 (equal variance in all directions). -/
theorem compoundSymmetryCorr_one (J : ℕ) :
    compoundSymmetryCorr 1 J = 0 := by
  simp [compoundSymmetryCorr]

-- ============================================================
-- Section 3: Gap-from-One Identity (Price Convergence Rate)
-- ============================================================

private lemma hJ_sub_one_pos {J : ℕ} (hJ : 2 ≤ J) : (0 : ℝ) < ↑J - 1 := by
  have : (2 : ℝ) ≤ ↑J := Nat.ofNat_le_cast.mpr hJ; linarith

private lemma den_pos {r : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hr : 0 ≤ r) :
    (0 : ℝ) < 1 + (↑J - 1) * r := by
  have := hJ_sub_one_pos hJ
  positivity

/-- **Gap-from-one identity**: 1 - cor = Jr / (1 + (J-1)r).

    For PRICES near the regime boundary:
    - r_price is proportional to lambda_{F,perp} is proportional to K_eff
      is proportional to (1-T/T*) via curvature conservation
    - 1 - cor_price = J r_price / (1+(J-1) r_price)
    - For small r: 1 - cor_price is approximately J r_price
      which is proportional to (1-T/T*)

    The convergence exponent beta = 1 is LINEAR. -/
theorem gap_from_one {r : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hr : 0 ≤ r) :
    1 - compoundSymmetryCorr r J =
    ↑J * r / (1 + (↑J - 1) * r) := by
  unfold compoundSymmetryCorr
  have hne : (1 + (↑J - 1) * r) ≠ 0 := ne_of_gt (den_pos hJ hr)
  rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne]
  ring

-- ============================================================
-- Section 4: Floor Identity (Quantity Correlation Bound)
-- ============================================================

/-- **Floor identity**: cor + 1/(J-1) = J / ((J-1)(1+(J-1)r)).

    For QUANTITIES near the regime boundary:
    - r_qty is proportional to 1/K_eff is proportional to 1/(1-T/T*)
      and diverges as T approaches T*
    - cor_qty + 1/(J-1) approaches 0 at rate (1-T/T*)

    With J = 10 sectors, the floor is -0.111. -/
theorem correlation_floor_identity {r : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hr : 0 ≤ r) :
    compoundSymmetryCorr r J + 1 / (↑J - 1) =
    ↑J / ((↑J - 1) * (1 + (↑J - 1) * r)) := by
  unfold compoundSymmetryCorr
  have hJ1 := hJ_sub_one_pos hJ
  have hden : (1 + (↑J - 1) * r) ≠ 0 := ne_of_gt (den_pos hJ hr)
  have hJ1ne : (↑J - 1 : ℝ) ≠ 0 := ne_of_gt hJ1
  field_simp
  ring

-- ============================================================
-- Section 5: Inequalities
-- ============================================================

/-- Correlation is bounded below by -1/(J-1). -/
theorem correlation_above_floor {r : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hr : 0 ≤ r) :
    -1 / (↑J - 1) < compoundSymmetryCorr r J := by
  have h := correlation_floor_identity hJ hr
  have hJ1 := hJ_sub_one_pos hJ
  have hden := den_pos hJ hr
  have hJp : (0 : ℝ) < ↑J := Nat.cast_pos.mpr (by omega)
  have key : 0 < compoundSymmetryCorr r J + 1 / (↑J - 1) := by
    rw [h]; exact div_pos hJp (mul_pos hJ1 hden)
  have neg_cancel : (-1 : ℝ) / (↑J - 1) + 1 / (↑J - 1) = 0 := by
    rw [← add_div]; simp
  linarith

/-- Correlation is bounded above by 1. -/
theorem correlation_le_one {r : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hr : 0 ≤ r) :
    compoundSymmetryCorr r J ≤ 1 := by
  have h := gap_from_one hJ hr
  have hJ_pos : (0 : ℝ) < ↑J := by linarith [hJ_sub_one_pos hJ]
  have hden := den_pos hJ hr
  linarith [div_nonneg (mul_nonneg (le_of_lt hJ_pos) hr) (le_of_lt hden)]

/-- **Linear bound**: 1 - cor is at most J r.

    Since r_price is proportional to (1-T/T*), the gap from perfect
    correlation is at most linear in the distance from T*. -/
theorem gap_from_one_le {r : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hr : 0 ≤ r) :
    1 - compoundSymmetryCorr r J ≤ ↑J * r := by
  rw [gap_from_one hJ hr]
  have hd : 1 ≤ 1 + (↑J - 1) * r := by nlinarith [hJ_sub_one_pos hJ]
  exact div_le_self (mul_nonneg (Nat.cast_nonneg J) hr) hd

/-- The gap from 1 is nonneg (equivalently, cor is at most 1). -/
theorem gap_from_one_nonneg {r : ℝ} {J : ℕ} (hJ : 2 ≤ J) (hr : 0 ≤ r) :
    0 ≤ 1 - compoundSymmetryCorr r J := by
  rw [gap_from_one hJ hr]
  have hJ_pos : (0 : ℝ) < ↑J := by linarith [hJ_sub_one_pos hJ]
  exact div_nonneg (mul_nonneg (le_of_lt hJ_pos) hr) (le_of_lt (den_pos hJ hr))

-- ============================================================
-- Section 6: Crisis Correlation Convergence
-- ============================================================

/-- **Price correlation convergence (beta = 1).**

    When the price variance ratio r = a*delta is proportional to a
    small parameter delta = 1-T/T*, the gap from perfect correlation
    is at most J*a*delta.

    Curvature conservation (FurtherProperties.curvature_conservation)
    forces r_price to be proportional to K_eff = K(1-T/T*). -/
theorem price_convergence_linear {a δ : ℝ} {J : ℕ}
    (hJ : 2 ≤ J) (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    1 - compoundSymmetryCorr (a * δ) J ≤ ↑J * a * δ := by
  have h := gap_from_one_le hJ (mul_nonneg ha hδ)
  linarith [mul_assoc (↑J : ℝ) a δ]

/-- **Quantity correlation floor approach.**

    When the quantity variance ratio r = a/delta diverges as delta -> 0,
    the distance from the equicorrelation floor -1/(J-1) is given by
    the floor identity with r = a/delta. -/
theorem quantity_correlation_to_floor {a δ : ℝ} {J : ℕ}
    (hJ : 2 ≤ J) (ha : 0 < a) (hδ : 0 < δ) :
    compoundSymmetryCorr (a / δ) J + 1 / (↑J - 1) =
    ↑J / ((↑J - 1) * (1 + (↑J - 1) * (a / δ))) :=
  correlation_floor_identity hJ (le_of_lt (div_pos ha hδ))

-- ============================================================
-- Section 7: The Dual Prediction Summary
-- ============================================================

/-- **Crisis Correlation Dual Prediction.**

    At the regime boundary T -> T*, compound symmetry + curvature
    conservation produce opposite behavior for prices and quantities:

    1. PRICES: r_price -> 0 (cost curvature diverges)
       -> cor_price -> 1 at rate O(1-T/T*) with beta = 1

    2. QUANTITIES: r_qty -> infinity (production curvature vanishes)
       -> cor_qty -> -1/(J-1) at rate O(1-T/T*) with beta = 1

    Both rates are LINEAR (beta = 1), discriminating from GARCH/DCC
    models (exponential convergence).

    Combined with the cumulant tower: near T*, the escort cumulants
    kappa_n -> 0 for all n >= 2 (generalized estimation paradox) AND
    cor_price -> 1 (prices lock together). The economy loses both
    information capacity and cross-sectional diversity. This is the
    total information blackout at the regime boundary.

    **Proof.** Assembles three algebraic identities on the compound symmetry formula $\mathrm{cor} = (1-r)/(1+(J-1)r)$: (i) substituting $r=0$ gives $\mathrm{cor}=1$; (ii) the floor identity shows $\mathrm{cor} + 1/(J-1) = J/((J-1)(1+(J-1)r)) > 0$ for all finite $r \geq 0$, so $\mathrm{cor} > -1/(J-1)$; (iii) the gap-from-one identity $1 - \mathrm{cor} = Jr/(1+(J-1)r) \leq Jr$ gives the linear bound $\beta = 1$. -/
theorem crisis_correlation_dual {J : ℕ} (hJ : 2 ≤ J) :
    -- (i) Price limit: r = 0 gives cor = 1
    compoundSymmetryCorr 0 J = 1 ∧
    -- (ii) Quantity floor: cor > -1/(J-1) for all finite r
    (∀ r : ℝ, 0 ≤ r → -1 / (↑J - 1) < compoundSymmetryCorr r J) ∧
    -- (iii) Linear bound: beta = 1
    (∀ r : ℝ, 0 ≤ r → 1 - compoundSymmetryCorr r J ≤ ↑J * r) :=
  ⟨compoundSymmetryCorr_zero J,
   fun _ hr => correlation_above_floor hJ hr,
   fun _ hr => gap_from_one_le hJ hr⟩

end
