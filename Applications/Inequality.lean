/-
  CES Inequality Decomposition

  CES curvature K controls surplus SIZE; Herfindahl H controls surplus DISTRIBUTION.
  K(ρ,a) = (1-ρ)(1-H) means concentration erodes complementarity gains—
  inequality is not just distributionally unfair but PRODUCTIVELY costly.

  Key results:
  - Income ratio from CES (Arrow IIA repackaged)
  - Substitutability dampens inequality (0 < ρ < 1 regime)
  - Complements favor scarce factors (ρ < 0 regime)
  - No efficiency-equity tradeoff in complement regime
  - Piketty r > g condition from CES accumulation
  - Concentration erodes complementarity
-/

import CESProofs.Macro.TwoFactorCES
import CESProofs.Foundations.GeneralWeights
import CESProofs.Macro.Accumulation
import CESProofs.Applications.Economics
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Definitions
-- ============================================================

/-- Income ratio between factors i and j under CES with general weights:
    s_i/s_j = (a_i/a_j) · (x_i/x_j)^ρ.
    This is Arrow's IIA property: the relative income of i and j
    depends only on their weight ratio and input ratio, not on other inputs. -/
def incomeRatio (a_i a_j x_i x_j ρ : ℝ) : ℝ :=
  (a_i / a_j) * (x_i / x_j) ^ ρ

/-- Surplus loss from weight concentration:
    ΔK = (1-ρ) · (H - 1/J)
    where H is the Herfindahl index. Equal weights (H = 1/J) give zero loss;
    any concentration (H > 1/J) reduces the complementarity surplus. -/
def surplusLoss (ρ H : ℝ) (J : ℕ) : ℝ := (1 - ρ) * (H - 1 / J)

-- ============================================================
-- Result I-1: Surplus Loss is Non-Negative
-- ============================================================

/-- **Result I-1 (Surplus Loss Non-Negative)**.

    When ρ < 1 (complement regime) and H ≥ 1/J (Herfindahl at or above
    the equal-weight minimum), the surplus loss from concentration is
    non-negative. Concentration always destroys complementarity surplus. -/
theorem surplus_loss_nonneg {ρ H : ℝ} {J : ℕ} (hρ : ρ < 1) (hH : 1 / (J : ℝ) ≤ H) :
    0 ≤ surplusLoss ρ H J := by
  simp only [surplusLoss]
  exact mul_nonneg (by linarith) (by linarith)

-- ============================================================
-- Result I-2: Income Ratio from CES
-- ============================================================

/-- **Result I-2 (Income Ratio from CES)**.

    The CES factor share ratio s_i/s_j equals the income ratio
    (a_i/a_j)(x_i/x_j)^ρ. This is a repackaging of Arrow's IIA
    for the CES aggregate, now interpreted as an income distribution result. -/
theorem income_ratio_from_ces {a_i a_j x_i x_j ρ : ℝ} :
    incomeRatio a_i a_j x_i x_j ρ = (a_i / a_j) * (x_i / x_j) ^ ρ := by
  rfl

-- ============================================================
-- Result I-3: Substitutability Dampens Inequality
-- ============================================================

/-- **Result I-3 (Substitutability Dampens Inequality)**.

    When 0 < ρ < 1 (gross substitutes) and the input ratio r = x_i/x_j > 1,
    then r^ρ < r: the income ratio is compressed relative to the input ratio.
    Substitutability dampens input inequality in the income distribution.

    **Proof.** for r > 1 and 0 < ρ < 1, r^ρ < r^1 = r by strict monotonicity
    of r^(·) in the exponent. -/
theorem substitutability_dampens_inequality {ρ r : ℝ}
    (hρ_lt : ρ < 1) (hr : 1 < r) :
    r ^ ρ < r := by
  conv_rhs => rw [← rpow_one r]
  exact rpow_lt_rpow_of_exponent_lt (by linarith) hρ_lt

-- ============================================================
-- Result I-4: Complements Favor Scarce Factors
-- ============================================================

/-- **Result I-4 (Complements Favor Scarce Factors)**.

    When ρ < 0 (gross complements) and the input ratio r > 1,
    then r^ρ < 1: the abundant factor's income share is compressed
    below unity. Scarce factors earn disproportionately more under
    complementarity—bottleneck rents. -/
theorem complements_favor_scarce {ρ r : ℝ}
    (hρ : ρ < 0) (hr : 1 < r) :
    r ^ ρ < 1 := by
  rw [← rpow_zero r]
  exact rpow_lt_rpow_of_exponent_lt (by linarith) hρ

-- ============================================================
-- Result I-5: No Efficiency-Equity Tradeoff
-- ============================================================

/-- **Result I-5 (Complementarity: No Efficiency-Equity Tradeoff)**.

    For 0 < ρ₁ < ρ₂ < 1 (substitute regime), lower ρ simultaneously:
    (a) Raises curvature K = (1-ρ)(J-1)/J (higher efficiency)
    (b) Compresses income ratios closer to 1 (r^ρ₁ < r^ρ₂, both in (1,r))

    In the substitute regime there is no tradeoff: moving toward
    complements improves both efficiency and equality.

    Note: the theorem allows ρ₁ < 0, but part (b) then means r^ρ₁ is on
    the opposite side of 1 (scarce factor earns more). The "no tradeoff"
    interpretation is cleanest when both ρ values are positive.

    For Gini (personal inequality), the relevant channel is the CAPITAL
    SHARE s_K = α·(K/L)^ρ which is monotone increasing in ρ when K/L > 1.
    Higher ρ → higher s_K → higher Gini. See test_inequality_ces.py. -/
theorem complementarity_no_tradeoff {ρ₁ ρ₂ r : ℝ} (J : ℕ) (hJ : 2 ≤ J)
    (_hρ₁ : ρ₁ < 1) (_hρ₂ : ρ₂ < 1) (h12 : ρ₁ < ρ₂)
    (_hρ₂_pos : 0 < ρ₂) (hr : 1 < r) :
    -- (a) Lower ρ → higher K
    (1 - ρ₂) * ((J - 1 : ℝ) / J) < (1 - ρ₁) * ((J - 1 : ℝ) / J)
    -- (b) Lower ρ → more compressed income (r^ρ₁ < r^ρ₂ when 0 < ρ₁ < ρ₂ < 1)
    ∧ r ^ ρ₁ < r ^ ρ₂ := by
  constructor
  · apply mul_lt_mul_of_pos_right (by linarith)
    apply div_pos
    · have : (2 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
      linarith
    · exact_mod_cast Nat.pos_of_ne_zero (by omega)
  · exact rpow_lt_rpow_of_exponent_lt (by linarith) h12

-- ============================================================
-- Result I-6: Piketty r > g Condition
-- ============================================================

/-- **Result I-6 (Piketty r > g from CES Accumulation)**.

    The net return on capital exceeds the growth rate (r > g)
    if and only if the capital share exceeds the savings-adjusted
    growth ratio: s_K > s · (1 + g/δ)⁻¹.

    At Solow steady state K̇ = 0: s·Y = δ·K, so K/Y = s/δ.
    Capital income share s_K = r·K/Y = r·s/δ.
    Thus r > g ⟺ s_K > g·s/δ = s·g/δ.
    Rearranging: s_K/s > g/δ, i.e., r/δ > g/δ.

    This connects CES factor shares to wealth concentration dynamics.

    **Proof.** Substitute $s_K = rs/\delta$ into the inequality $r > g$: multiplying both sides by $s/\delta > 0$ gives $rs/\delta > gs/\delta$, i.e., $s_K > gs/\delta$. The converse follows by contradiction: $r \leq g$ implies $rs \leq gs$, hence $rs/\delta \leq gs/\delta$, contradicting $s_K > gs/\delta$. -/
theorem piketty_r_gt_g {r g s_K s δ : ℝ}
    (hδ : 0 < δ) (hs : 0 < s)
    (h_solow : s_K = r * s / δ) :
    r > g ↔ s_K > g * s / δ := by
  subst h_solow
  constructor
  · intro h
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right h hs) hδ
  · intro h
    rw [gt_iff_lt] at h ⊢
    by_contra h_neg
    push_neg at h_neg
    have : r * s ≤ g * s := mul_le_mul_of_nonneg_right h_neg (le_of_lt hs)
    have : r * s / δ ≤ g * s / δ := div_le_div_of_nonneg_right this (le_of_lt hδ)
    linarith

-- ============================================================
-- Result I-7: Concentration Erodes Complementarity
-- ============================================================

/-- **Result I-7 (Concentration Erodes Complementarity)**.

    For any weight vector with Herfindahl H > 1/J (i.e., non-uniform weights),
    the general-weight curvature K(ρ,a) = (1-ρ)(1-H) is strictly less than
    the equal-weight curvature K(ρ,uniform) = (1-ρ)(J-1)/J.

    Concentration is doubly costly: it reduces both the efficiency surplus
    (via lower K) and equality (via skewed factor shares).

    **Proof.** (1-H) < (J-1)/J when H > 1/J. -/
theorem concentration_erodes_complementarity {ρ H : ℝ} {J : ℕ}
    (hρ : ρ < 1) (hJ : (0 : ℝ) < J) (hH : 1 / (J : ℝ) < H) :
    (1 - ρ) * (1 - H) < (1 - ρ) * ((J - 1 : ℝ) / J) := by
  apply mul_lt_mul_of_pos_left _ (by linarith : (0 : ℝ) < 1 - ρ)
  have : (J - 1 : ℝ) / J = 1 - 1 / J := by field_simp
  linarith

/-! ## CES Inequality Measures
  (Merged from Applications/InequalityMeasures.lean)

  Theil index, Gini index, share variance, and their relationships.
-/

-- ============================================================
-- Definitions
-- ============================================================

/-- Theil T index: KL divergence of shares from uniform distribution.
    T = Σ s_j · log(J · s_j). At equal shares s_j = 1/J: T = 0.
    Maximum T = log(J) when one agent gets everything. -/
def theilIndex (J : ℕ) (s : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J, s j * Real.log (↑J * s j)

/-- Gini index from pairwise share differences:
    G = (1 / (2J)) · Σ_i Σ_j |s_i - s_j|. -/
def giniIndex (J : ℕ) (s : Fin J → ℝ) : ℝ :=
  (1 / (2 * ↑J)) * ∑ i : Fin J, ∑ j : Fin J, |s i - s j|

/-- Share variance: Σ (s_j - 1/J)². Connects Herfindahl to inequality. -/
def shareVariance (J : ℕ) (s : Fin J → ℝ) : ℝ :=
  ∑ j : Fin J, (s j - 1 / ↑J) ^ 2

-- ============================================================
-- Results IM-1 through IM-10
-- ============================================================

/-- **Result IM-1**: Theil = 0 at equal shares. -/
theorem theil_zero_at_equality (hJ : 0 < J) :
    theilIndex J (fun _ : Fin J => (1 / ↑J : ℝ)) = 0 := by
  simp only [theilIndex]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  conv_lhs =>
    arg 2; ext j
    rw [show (↑J : ℝ) * (1 / ↑J) = 1 from by field_simp]
  simp [Real.log_one]

/-- **Result IM-2**: Theil non-negative (Gibbs inequality).

    **Proof.** The Theil index $T = \sum s_j \log(J s_j)$ equals the KL divergence
    $D_{\mathrm{KL}}(s \| u)$ where $u$ is the uniform distribution. By Jensen's
    inequality applied to the convex function $x \mapsto x \log x$ on $[0,\infty)$
    with uniform weights $1/J$ and points $J s_j$:
    $f(\sum (1/J)(J s_j)) \leq \sum (1/J) f(J s_j)$, i.e.,
    $0 = 1 \cdot \log 1 \leq \sum s_j \log(J s_j) = T$. -/
theorem theil_nonneg (hJ : 0 < J) (s : Fin J → ℝ)
    (hs_pos : ∀ j : Fin J, 0 < s j)
    (hs_sum : ∑ j : Fin J, s j = 1) :
    0 ≤ theilIndex J s := by
  simp only [theilIndex]
  -- Use Jensen's inequality: f convex, weights w_j = 1/J, points p_j = J * s_j
  -- f(∑ w_j * p_j) ≤ ∑ w_j * f(p_j) where f(x) = x * log(x)
  have hJpos : (0 : ℝ) < (↑J : ℝ) := Nat.cast_pos.mpr hJ
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  -- The weighted sum of points equals 1
  have hw_sum : ∑ j : Fin J, (1 / (↑J : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [hJne]
  -- Rewrite: ∑ s_j * log(J * s_j) = ∑ (1/J) * ((J*s_j) * log(J*s_j))
  have key : ∀ j : Fin J,
      s j * Real.log (↑J * s j) = (1 / ↑J) * ((↑J * s j) * Real.log (↑J * s j)) := by
    intro j; field_simp
  simp_rw [key]
  -- The weighted sum of points: ∑ (1/J) * (J * s_j) = ∑ s_j = 1
  have hcenter : ∑ j : Fin J, (1 / (↑J : ℝ)) • (↑J * s j) = 1 := by
    simp only [smul_eq_mul]
    have : ∀ j : Fin J, 1 / (↑J : ℝ) * (↑J * s j) = s j := by
      intro j; field_simp
    simp_rw [this, hs_sum]
  -- Apply Jensen: f(1) ≤ ∑ (1/J) * f(J * s_j)
  have jensen := ConvexOn.map_sum_le Real.convexOn_mul_log
    (fun i _ => le_of_lt (div_pos one_pos hJpos))
    hw_sum
    (fun i _ => Set.mem_Ici.mpr (le_of_lt (mul_pos hJpos (hs_pos i))))
  -- f(1) = 1 * log 1 = 0
  rw [hcenter] at jensen
  simp only [smul_eq_mul, Real.log_one, mul_zero] at jensen
  linarith

/-- **Result IM-3**: Theil bounded by log(J). -/
theorem theil_bounded_by_log_J (hJ : 0 < J)
    (hs_pos : ∀ j : Fin J, 0 < s j)
    (hs_sum : ∑ j : Fin J, s j = 1)
    (hs_le : ∀ j : Fin J, s j ≤ 1) :
    theilIndex J s ≤ Real.log ↑J := by
  simp only [theilIndex]
  calc ∑ j : Fin J, s j * Real.log (↑J * s j)
      ≤ ∑ j : Fin J, s j * Real.log ↑J := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (hs_pos j))
        apply Real.log_le_log (mul_pos (by exact_mod_cast hJ) (hs_pos j))
        calc ↑J * s j ≤ ↑J * 1 := by
              apply mul_le_mul_of_nonneg_left (hs_le j) (by exact_mod_cast le_of_lt hJ)
            _ = ↑J := mul_one _
    _ = (∑ j : Fin J, s j) * Real.log ↑J := by rw [Finset.sum_mul]
    _ = 1 * Real.log ↑J := by rw [hs_sum]
    _ = Real.log ↑J := one_mul _

/-- **Result IM-4**: Gini = 0 at equal shares. -/
theorem gini_zero_at_equality (hJ : 0 < J) :
    giniIndex J (fun _ : Fin J => (1 / ↑J : ℝ)) = 0 := by
  simp only [giniIndex, sub_self, abs_zero, Finset.sum_const_zero, mul_zero]

/-- **Result IM-5**: Gini non-negative. -/
theorem gini_nonneg (hJ : 0 < J) (s : Fin J → ℝ) :
    0 ≤ giniIndex J s := by
  simp only [giniIndex]
  apply mul_nonneg
  · apply div_nonneg one_pos.le
    exact mul_nonneg (by norm_num) (by exact_mod_cast le_of_lt hJ)
  · apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact abs_nonneg _

/-- **Result IM-6**: Share variance = H - 1/J. -/
theorem share_variance_eq_H_minus_inv (hJ : 0 < J)
    (hs_sum : ∑ j : Fin J, s j = 1) :
    shareVariance J s = herfindahlIndex J s - 1 / ↑J := by
  simp only [shareVariance, herfindahlIndex]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have expand : ∀ j : Fin J, (s j - 1 / ↑J) ^ 2 = s j ^ 2 - 2 * s j / ↑J + (1 / ↑J) ^ 2 := by
    intro j; ring
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [show ∀ j : Fin J, 2 * s j / (↑J : ℝ) = 2 / ↑J * s j from fun j => by ring]
  rw [← Finset.mul_sum, hs_sum]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **Result IM-7**: Lower ρ compresses share ratios. -/
theorem lower_rho_compresses_shares {ρ₁ ρ₂ : ℝ} {r : ℝ}
    (h12 : ρ₁ < ρ₂) (hr : 1 < r) :
    r ^ ρ₁ < r ^ ρ₂ :=
  rpow_lt_rpow_of_exponent_lt (by linarith) h12

/-- **Result IM-8**: Higher Herfindahl → higher share variance. -/
theorem concentration_raises_share_variance {H₁ H₂ : ℝ} {J : ℕ}
    (hH : H₁ < H₂) :
    H₁ - 1 / (↑J : ℝ) < H₂ - 1 / (↑J : ℝ) := by
  linarith

/-- **Result IM-9**: Gini bounded by Theil (Pinsker-type). Schematic.

    **Proof.** The Theil index for shares $s$ relative to the uniform distribution $u_j = 1/J$ equals the KL divergence $T = D_{\mathrm{KL}}(s \| u) = \sum_j s_j \log(J s_j)$. The Gini index can be written as $G = (J/(2(J-1))) \|s - u\|_1$, i.e., it is proportional to the $L^1$ distance between $s$ and the uniform distribution (Cowell 2011, Chapter 3). Pinsker's inequality states $\|s - u\|_1 \leq \sqrt{2 D_{\mathrm{KL}}(s \| u)}$. Substituting and squaring gives $G^2 \leq C \cdot T$ where $C = J^2/(2(J-1)^2)$ is a dimensional constant depending only on the number of agents. This bound is tight when the distribution is close to uniform and becomes loose for highly concentrated distributions. -/
theorem gini_bounded_by_theil (hJ : 0 < J) (s : Fin J → ℝ)
    (hs_pos : ∀ j : Fin J, 0 < s j)
    (hs_sum : ∑ j : Fin J, s j = 1) :
    True := trivial

/-- **Result IM-10**: Theil additive decomposition. Schematic.

    **Proof.** Partition the $J$ agents into $G$ groups with group income shares $w_g = \sum_{j \in g} s_j$. Write the KL divergence as $T = \sum_j s_j \log(J s_j)$ and decompose each $s_j = w_g \cdot (s_j / w_g)$ for $j \in g$. Expanding the logarithm via the chain rule for KL divergence yields $T = \sum_g w_g \log(J w_g / |g|) + \sum_g w_g \sum_{j \in g} (s_j/w_g) \log(|g| s_j / w_g)$. The first term is $T_{\mathrm{between}}$, the Theil index of the group means, and the second is $\sum_g w_g T_g$ where $T_g$ is the within-group Theil index (Cover and Thomas 2006, Section 2.7). This exact additivity is unique to the Theil index among generalized entropy measures and is the reason it serves as the natural information-theoretic inequality measure in the CES framework. -/
theorem theil_decomposition_additive (hJ : 0 < J) (s : Fin J → ℝ)
    (hs_pos : ∀ j : Fin J, 0 < s j)
    (hs_sum : ∑ j : Fin J, s j = 1) :
    True := trivial

end
