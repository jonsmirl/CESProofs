/-
  Economics extensions for CES formalization:
  Twelve economics connections to the existing CES framework.

  Tier 1 (algebraic):
  1. Elasticity of substitution (sigma = 1/(1-rho))
  2. Factor/cost shares
  3. Gains from variety (Krugman 1980)
  4. ACR gains from trade (Arkolakis-Costinot-Rodriguez-Clare 2012)
  5. CES as Lp norm

  Tier 2 (Mathlib mean inequality / concavity / Hölder infrastructure):
  6. Power mean ordering (Hardy-Littlewood-Pólya)
  7. CES price index (Dixit-Stiglitz 1977)
  8. Jensen gap for CES
  9. Hölder duality

  Tier 3 (calculus / HasDerivAt):
  10. Euler's theorem for homogeneous functions + CES gradient derivative
  11. CES → Cobb-Douglas limit (ρ → 0)
  12. Shephard's lemma and CES demand

  No custom axioms. 1 soft axiom (True := trivial) for cost minimization
  duality (requires constrained optimization / Lagrange multipliers).
-/

import CESProofs.Foundations.Defs
import CESProofs.Foundations.FurtherProperties
import CESProofs.CurvatureRoles.NetworkCES
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Extension 1: Elasticity of Substitution
-- ============================================================

/-- The elasticity of substitution: sigma = 1/(1 - rho).
    Standard economics parameterization of CES.
    sigma > 1 means gross substitutes, sigma < 1 means gross complements.
    sigma = 1 is Cobb-Douglas. -/
def elasticityOfSubstitution (ρ : ℝ) : ℝ := 1 / (1 - ρ)

/-- sigma > 0 when rho < 1 (the empirically relevant complementary regime). -/
theorem sigma_pos {ρ : ℝ} (hρ : ρ < 1) :
    0 < elasticityOfSubstitution ρ := by
  simp only [elasticityOfSubstitution]
  exact div_pos one_pos (by linarith)

/-- sigma > 1 when 0 < rho < 1 (gross substitutes). -/
theorem sigma_gt_one {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    1 < elasticityOfSubstitution ρ := by
  simp only [elasticityOfSubstitution]
  rw [one_lt_div (by linarith : (0 : ℝ) < 1 - ρ)]
  linarith

/-- sigma = 1/(1-rho) by definition. -/
theorem sigma_eq_one_div (ρ : ℝ) :
    elasticityOfSubstitution ρ = 1 / (1 - ρ) := rfl

/-- Inverse relation: rho = 1 - 1/sigma.

    **Proof.** From $\sigma = 1/(1-\rho)$, invert to get $1/\sigma = 1-\rho$, hence $\rho = 1 - 1/\sigma$. The proof clears fractions via `field_simp` using the hypothesis $\rho \neq 1$ (equivalently $1-\rho \neq 0$). -/
theorem sigma_rho_inverse {ρ : ℝ} (hρ : ρ ≠ 1) :
    ρ = 1 - 1 / elasticityOfSubstitution ρ := by
  simp only [elasticityOfSubstitution]
  have h : (1 : ℝ) - ρ ≠ 0 := by intro h; apply hρ; linarith
  field_simp
  linarith

/-- Curvature K expressed via sigma: K = (1/sigma)(J-1)/J.
    Since 1-rho = 1/sigma, this is immediate. -/
theorem curvatureK_eq_sigma (ρ : ℝ) :
    curvatureK J ρ = (1 / elasticityOfSubstitution ρ) * (↑J - 1) / ↑J := by
  simp only [curvatureK, elasticityOfSubstitution]
  rw [one_div, one_div, inv_inv]

/-- The dual exponent equals 1 - sigma. -/
theorem dualExponent_eq_sigma {ρ : ℝ} (hρ : ρ ≠ 1) :
    dualExponent ρ = 1 - elasticityOfSubstitution ρ := by
  simp only [dualExponent, elasticityOfSubstitution]
  have h : (1 : ℝ) - ρ ≠ 0 := by intro h; apply hρ; linarith
  have h' : ρ - (1 : ℝ) ≠ 0 := by intro h'; apply hρ; linarith
  field_simp
  ring

/-- sigma > 1 iff goods are gross substitutes (alias for economics clarity). -/
theorem sigma_substitutes {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    1 < elasticityOfSubstitution ρ :=
  sigma_gt_one hρ hρ1

-- ============================================================
-- Extension 2: Factor/Cost Shares
-- ============================================================

/-- Factor (cost) share of input j in CES production:
    s_j = a_j x_j^rho / Sum_i a_i x_i^rho

    At symmetric equilibrium with equal weights, s_j = 1/J.
    These are the Tsallis escort probabilities when a_j = p_j. -/
def factorShare (J : ℕ) (a : Fin J → ℝ) (ρ : ℝ) (x : Fin J → ℝ) (j : Fin J) : ℝ :=
  a j * (x j) ^ ρ / ∑ i : Fin J, a i * (x i) ^ ρ

/-- Factor shares are non-negative when weights and inputs are non-negative. -/
theorem factorShare_nonneg {a : Fin J → ℝ} {ρ : ℝ} {x : Fin J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hx : ∀ j, 0 ≤ x j)
    (hden : 0 ≤ ∑ i : Fin J, a i * (x i) ^ ρ) (j : Fin J) :
    0 ≤ factorShare J a ρ x j := by
  simp only [factorShare]
  apply div_nonneg
  · exact mul_nonneg (ha j) (rpow_nonneg (hx j) ρ)
  · exact hden

/-- Factor shares sum to one when the denominator is positive.

    **Proof.** Write each share as $s_j = (a_j x_j^\rho) \cdot (\sum_k a_k x_k^\rho)^{-1}$, factor out the common inverse, and apply $\sum_j a_j x_j^\rho \cdot (\sum_k a_k x_k^\rho)^{-1} = 1$ via `mul_inv_cancel`. -/
theorem factorShare_sum_eq_one {a : Fin J → ℝ} {ρ : ℝ} {x : Fin J → ℝ}
    (hden : 0 < ∑ i : Fin J, a i * (x i) ^ ρ) :
    ∑ j : Fin J, factorShare J a ρ x j = 1 := by
  simp only [factorShare]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt hden)

/-- At the symmetric point with equal weights, factor shares are uniform: s_j = 1/J. -/
theorem factorShare_symmetric_uniform {J : ℕ} (hJ : 0 < J) {ρ : ℝ} {c : ℝ} (hc : 0 < c) :
    ∀ j : Fin J, factorShare J (fun _ => (1 : ℝ) / ↑J) ρ (symmetricPoint J c) j = 1 / ↑J := by
  intro j
  simp only [factorShare, symmetricPoint]
  have hJpos : (0 : ℝ) < ↑J := Nat.cast_pos.mpr hJ
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJpos
  have hcρ : (0 : ℝ) < c ^ ρ := rpow_pos_of_pos hc ρ
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Each factor share is at most 1 (when denominator is positive and shares are non-negative). -/
theorem factorShare_le_one {a : Fin J → ℝ} {ρ : ℝ} {x : Fin J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hx : ∀ j, 0 ≤ x j)
    (hden : 0 < ∑ i : Fin J, a i * (x i) ^ ρ) (j : Fin J) :
    factorShare J a ρ x j ≤ 1 := by
  have hsum := factorShare_sum_eq_one hden
  have hnneg : ∀ k, 0 ≤ factorShare J a ρ x k :=
    factorShare_nonneg ha hx (le_of_lt hden)
  calc factorShare J a ρ x j
      ≤ ∑ k : Fin J, factorShare J a ρ x k :=
        Finset.single_le_sum (fun k _ => hnneg k) (Finset.mem_univ j)
    _ = 1 := hsum

-- ============================================================
-- Extension 2b: Escort Distributions — the q = ρ Bridge
-- ============================================================

/-- The Tsallis escort distribution of a vector x with parameter q:
    P_j^(q) = x_j^q / Σ_k x_k^q

    Reweights the base vector by its q-th power.  The name "escort"
    comes from Tsallis statistics: the escort P^(q) of a distribution p
    is the distribution that appears in q-generalized expectations.

    For q < 1 (complements, ρ < 1): escort is more uniform than base —
    rare inputs receive relatively more weight.
    For q > 1 (substitutes, ρ > 1): escort is more concentrated than base.
    For q = 1: escort equals the base (Shannon / logit case).

    The central result below: CES factor shares = escort of x with q = ρ.
    This is why q = ρ is forced by the production technology (Paper 2). -/
def escortDistribution (J : ℕ) (q : ℝ) (x : Fin J → ℝ) (j : Fin J) : ℝ :=
  (x j) ^ q / ∑ k : Fin J, (x k) ^ q

/-- **Escort = Factor Shares (q = ρ Bridge)**.

    For unit weights (a_j = 1 for all j), the CES factor share of input j
    equals the Tsallis escort distribution of the input vector x with
    parameter q = ρ:

        s_j = x_j^ρ / Σ_k x_k^ρ  =  P_j^(ρ)(x)

    This is the algebraic identity behind Paper 2's q = ρ locking:
    factor shares (observable from cost data) are exactly escort probabilities
    (the natural weighting in q-generalized statistics).

    Lean verifies this by unfolding both definitions, which share the
    identical formula x_j^ρ / Σ x_k^ρ. -/
theorem factorShare_eq_escort {J : ℕ} (ρ : ℝ) (x : Fin J → ℝ) (j : Fin J) :
    factorShare J (fun _ => (1 : ℝ)) ρ x j = escortDistribution J ρ x j := by
  simp [factorShare, escortDistribution]

/-- At the symmetric allocation (x_j = c for all j), the escort distribution
    is uniform: P_j^(ρ)(c, …, c) = 1/J, independent of ρ and c > 0.

    This matches the factor share at symmetric equilibrium: all inputs
    receive equal cost shares 1/J when deployed in equal quantities.
    The uniform distribution maximizes both Tsallis entropy S_ρ and
    CES output F, confirming that the symmetric equilibrium is
    simultaneously the entropy-maximum and the output-maximum. -/
theorem escort_symmetric_eq_uniform {J : ℕ} (hJ : 0 < J) (ρ : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ j : Fin J, escortDistribution J ρ (symmetricPoint J c) j = 1 / ↑J := by
  intro j
  simp only [escortDistribution, symmetricPoint]
  have hcρ : (0 : ℝ) < c ^ ρ := rpow_pos_of_pos hc ρ
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The q-expectation of payoffs ε under the escort distribution equals
    the factor-share-weighted average of ε.

    For unit weights:  Σ_j P_j^(ρ)(x) · ε_j  =  Σ_j s_j · ε_j

    This connects Paper 2's q-average cost U_q = ⟨ε⟩_q to the standard
    economics concept of cost-share-weighted average payoff.
    The CES potential Φ_q = U_q − T·S_q can therefore be read as
    "cost-share-weighted payoff minus information friction times Tsallis
    entropy", with factor shares providing the natural weighting. -/
theorem qExpectation_eq_factorShare_weighted {J : ℕ} (ρ : ℝ) (x ε : Fin J → ℝ) :
    ∑ j : Fin J, escortDistribution J ρ x j * ε j =
    ∑ j : Fin J, factorShare J (fun _ => (1 : ℝ)) ρ x j * ε j := by
  simp [factorShare_eq_escort]

-- ============================================================
-- Extension 3: Gains from Variety (Krugman 1980)
-- ============================================================

/-- Gains from variety: the factor by which output exceeds the per-input level.
    G(J)/G(1) = J^{1/rho - 1} for the unnormalized CES.
    This is the Krugman (1980) "love of variety" effect. -/
def gainsFromVariety (J : ℕ) (ρ : ℝ) : ℝ :=
  (↑J : ℝ) ^ (1 / ρ - 1)

/-- Gains from variety equal the network scaling factor divided by J
    (per-unit normalization of the unnormalized CES scaling). -/
theorem gainsFromVariety_eq_scaling_ratio (hJ : 0 < J) {ρ : ℝ} (hρ : ρ ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    unnormCES J ρ (symmetricPoint J c) / (↑J * c) = gainsFromVariety J ρ := by
  rw [network_scaling hJ hρ hc]
  simp only [gainsFromVariety]
  have hJpos : (0 : ℝ) < ↑J := Nat.cast_pos.mpr hJ
  have hcne : c ≠ 0 := ne_of_gt hc
  rw [mul_div_mul_right _ _ hcne]
  -- Goal: (↑J)^(1/ρ) / ↑J = (↑J)^(1/ρ - 1)
  rw [rpow_sub hJpos, rpow_one]

/-- Gains from variety exceed 1 when J >= 2 and 0 < rho < 1.

    **Proof.** The gains from variety equal $J^{1/\rho - 1}$. When $0 < \rho < 1$ the exponent $1/\rho - 1 > 0$, so $J^{1/\rho - 1} > 1^{1/\rho - 1} = 1$ since $J \geq 2 > 1$ and $t \mapsto t^a$ is strictly increasing for $a > 0$. -/
theorem gainsFromVariety_gt_one (hJ : 2 ≤ J) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    1 < gainsFromVariety J ρ := by
  simp only [gainsFromVariety]
  have hJpos : (1 : ℝ) < ↑J := by exact_mod_cast (by omega : 1 < J)
  have hexp : 0 < 1 / ρ - 1 := by
    rw [sub_pos, lt_div_iff₀ hρ, one_mul]
    exact hρ1
  calc (1 : ℝ) = 1 ^ (1 / ρ - 1) := (one_rpow _).symm
    _ < (↑J : ℝ) ^ (1 / ρ - 1) := by
        exact rpow_lt_rpow zero_le_one hJpos hexp

-- ============================================================
-- Extension 3b: Network Scaling = Gains from Variety (Trade–Network Bridge)
-- ============================================================

/-- **Network Scaling = Krugman (1980) Gains from Variety**.

    The per-agent network scaling factor G(J)/G(1) = J^{1/ρ − 1} (Paper 1, Theorem 8)
    is identical to the Krugman (1980) gains-from-variety exponent J^{1/(σ−1)}
    in international trade theory.

    The two exponents are equal because σ = 1/(1−ρ) gives:
        1/(σ − 1)  =  (1−ρ)/ρ  =  1/ρ − 1.

    This is proved as `trade_elasticity_eq_variety_exponent` above.

    Economic significance: network economists (measuring gains from adding
    agents to a CES network) and trade economists (measuring gains from
    expanding product variety in a Dixit–Stiglitz economy) compute the
    same structural elasticity from different perspectives.

    Lean proof: unfold `gainsFromVariety`, then `congr 1` reduces to the
    exponent identity, which follows from `trade_elasticity_eq_variety_exponent`. -/
theorem gainsFromVariety_eq_trade_gains {J : ℕ} {ρ : ℝ}
    (hρ : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    gainsFromVariety J ρ = (↑J : ℝ) ^ (1 / (elasticityOfSubstitution ρ - 1)) := by
  simp only [gainsFromVariety, elasticityOfSubstitution]
  congr 1
  have h : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  field_simp [hρ, h]
  ring

-- ============================================================
-- Extension 4: ACR Gains from Trade (Arkolakis-Costinot-Rodriguez-Clare 2012)
-- ============================================================

/-- ACR gains from trade: welfare gain from trade openness.
    W_trade / W_autarky = lam^{-1/(sigma-1)} = lam^{-(1/rho - 1)}
    where lam is the domestic expenditure share (0 < lam <= 1).
    Under autarky lam = 1 and gains = 1.
    With trade lam < 1 and gains > 1.

    The trade elasticity theta = sigma - 1 = 1/rho - 1 (for rho in (0,1))
    is exactly the exponent controlling gains from variety. -/
def acrGainsFromTrade (lam ρ : ℝ) : ℝ :=
  lam ^ (-(1 / ρ - 1))

/-- ACR gains exceed 1 when there is actual trade (lam < 1). -/
theorem acr_gains_gt_one {lam ρ : ℝ}
    (hlam : 0 < lam) (hlam1 : lam < 1) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    1 < acrGainsFromTrade lam ρ := by
  simp only [acrGainsFromTrade]
  have hexp_neg : -(1 / ρ - 1) < 0 := by
    rw [neg_lt_zero, sub_pos, lt_div_iff₀ hρ, one_mul]
    exact hρ1
  calc (1 : ℝ) = lam ^ (0 : ℝ) := (rpow_zero lam).symm
    _ < lam ^ (-(1 / ρ - 1)) := by
        exact rpow_lt_rpow_of_exponent_gt hlam hlam1 hexp_neg

/-- Under autarky (lam = 1), gains from trade equal 1. -/
theorem acr_gains_autarky (ρ : ℝ) :
    acrGainsFromTrade 1 ρ = 1 := by
  simp only [acrGainsFromTrade]
  exact one_rpow _

/-- The trade elasticity 1/(sigma-1) equals the variety exponent 1/rho - 1.
    This connects the ACR sufficient statistic to CES curvature. -/
theorem trade_elasticity_eq_variety_exponent {ρ : ℝ} (hρ : ρ ≠ 0) (hρ1 : ρ ≠ 1) :
    1 / (elasticityOfSubstitution ρ - 1) = 1 / ρ - 1 := by
  simp only [elasticityOfSubstitution]
  have h : (1 : ℝ) - ρ ≠ 0 := by intro h; apply hρ1; linarith
  field_simp
  have : 1 - (1 - ρ) = ρ := by ring
  rw [this]
  exact div_self hρ

/-- **K encodes the ACR trade elasticity**: K · σ = (J−1)/J.

    Since σ = 1/(1−ρ) and K = (1−ρ)(J−1)/J, we have:
        K · σ  =  (1−ρ)(J−1)/J · 1/(1−ρ)  =  (J−1)/J.

    Equivalently, K = (J−1)/(J·σ): curvature is the variety-weighted
    inverse trade elasticity, falling with market concentration (J→1, K→0)
    and with substitutability (σ→∞, K→0).

    This identity is the algebraic bridge between the CES complementarity
    parameter and the ACR (Arkolakis-Costinot-Rodríguez-Clare 2012) sufficient
    statistic: since the ACR welfare gain λ^{−1/(σ−1)} depends on σ through
    the trade elasticity 1/(σ−1), and K · σ = (J−1)/J relates K to σ,
    curvature K is the sole structural determinant of trade gains after
    conditioning on the variety count J. -/
theorem curvatureK_mul_sigma {J : ℕ} {ρ : ℝ} (hρ1 : ρ ≠ 1) (hJ : 0 < J) :
    curvatureK J ρ * elasticityOfSubstitution ρ = (↑J - 1) / ↑J := by
  simp only [curvatureK, elasticityOfSubstitution]
  have h : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hJ)
  field_simp [h, hJne]

/-- K expressed via the trade elasticity σ: K = (J−1)/(J·σ).
    Follows directly from `curvatureK_mul_sigma` by dividing through by σ. -/
theorem curvatureK_eq_via_sigma {J : ℕ} {ρ : ℝ} (hρ1 : ρ ≠ 1) (hJ : 0 < J) :
    curvatureK J ρ = (↑J - 1) / (↑J * elasticityOfSubstitution ρ) := by
  simp only [curvatureK, elasticityOfSubstitution]
  have h : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hJ)
  field_simp [h, hJne]

/-- **Marginal entrant curvature gain**: K(J+1) − K(J) = (1−ρ) / (J·(J+1)).

    The exact curvature gain from adding the (J+1)th variety is:
        ΔK_J  =  (1−ρ)(J/(J+1)) − (1−ρ)(J−1)/J  =  (1−ρ) / (J(J+1)).

    For large J this is approximately (1−ρ)/J², so curvature gains from
    diversity decrease at rate 1/J²—faster than the harmonic series—with
    the first entrant (J=1→2) delivering the largest marginal gain:
        ΔK_1  =  (1−ρ)/2   (half the maximum possible K under CRS).

    This is the mathematical basis for the semi-endogenous growth result:
    each new variety's contribution to complementarity falls with J,
    imposing a natural ceiling on the growth rate of K. -/
theorem curvatureK_increment {J : ℕ} {ρ : ℝ} (hJ : 0 < J) :
    curvatureK (J + 1) ρ - curvatureK J ρ = (1 - ρ) / (↑J * (↑J + 1)) := by
  simp only [curvatureK]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hJ)
  have hJ1ne : (↑J : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp [hJne, hJ1ne]
  ring

-- ============================================================
-- Extension 5: CES as Lp Norm
-- ============================================================

/-- The Lp norm (p-norm) on Fin J:
    norm_p(x) = (Sum |x_j|^p)^{1/p}.
    For non-negative inputs, |x_j| = x_j and this equals the unnormalized CES. -/
def lpNorm (J : ℕ) (p : ℝ) (x : Fin J → ℝ) : ℝ :=
  (∑ j : Fin J, |x j| ^ p) ^ (1 / p)

/-- For non-negative inputs, unnormCES equals the Lp norm with p = rho. -/
theorem unnormCES_eq_lpNorm {ρ : ℝ} {x : Fin J → ℝ}
    (hx : ∀ j, 0 ≤ x j) :
    unnormCES J ρ x = lpNorm J ρ x := by
  simp only [unnormCES, lpNorm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_of_nonneg (hx j)]

/-- Power mean equals a scaled Lp norm:
    M_rho(x) = (1/J)^{1/rho} * norm_rho(x) for non-negative inputs. -/
theorem powerMean_eq_scaled_lpNorm {ρ : ℝ} (hρ : ρ ≠ 0) {x : Fin J → ℝ}
    (hx : ∀ j, 0 ≤ x j) :
    powerMean J ρ hρ x = (1 / ↑J : ℝ) ^ (1 / ρ) * lpNorm J ρ x := by
  simp only [powerMean, lpNorm]
  have habsrw : ∀ j, |x j| ^ ρ = (x j) ^ ρ := fun j => by rw [abs_of_nonneg (hx j)]
  simp_rw [habsrw]
  rw [mul_rpow (by positivity : (0 : ℝ) ≤ 1 / ↑J)
               (Finset.sum_nonneg (fun j _ => rpow_nonneg (hx j) ρ))]

-- ============================================================
-- Extension 6: Power Mean Ordering (Hardy-Littlewood-Pólya)
-- ============================================================

/-- **Power mean ordering**: For 0 < rho1 le rho2, M_{rho1} le M_{rho2}.
    Higher substitutability (higher rho) produces a weakly higher aggregate.
    This is the Hardy-Littlewood-Polya inequality applied to CES.

    **Proof.** Apply `arith_mean_le_rpow_mean` with z_i = x_i^{rho1}, p = rho2/rho1 ge 1
    to get (1/J) Sum x_i^{rho1} le ((1/J) Sum x_i^{rho2})^{rho1/rho2},
    then raise to 1/rho1. -/
theorem powerMean_mono {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂)
    (hle : ρ₁ ≤ ρ₂) (hρ₁ne : ρ₁ ≠ 0) (hρ₂ne : ρ₂ ≠ 0)
    {x : Fin J → ℝ} (hx : ∀ j, 0 < x j)
    (hJ : 0 < J) :
    powerMean J ρ₁ hρ₁ne x ≤ powerMean J ρ₂ hρ₂ne x := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq; exact le_refl _
  have hJr : (0 : ℝ) < ↑J := Nat.cast_pos.mpr hJ
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJr
  -- Weights w_i = 1/J summing to 1
  set w : Fin J → ℝ := fun _ => (1 : ℝ) / ↑J with hw_def
  have hw_nn : ∀ i ∈ Finset.univ, 0 ≤ w i := fun _ _ => by positivity
  have hw_sum : ∑ i ∈ Finset.univ, w i = 1 := by
    simp [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact div_self hJne
  have hp : 1 ≤ ρ₂ / ρ₁ := by rwa [le_div_iff₀ hρ₁, one_mul]
  -- Apply arith_mean_le_rpow_mean with z_i = x_i^{rho1}, p = rho2/rho1
  have step := Real.arith_mean_le_rpow_mean Finset.univ w (fun j => (x j) ^ ρ₁)
    hw_nn hw_sum (fun i _ => rpow_nonneg (le_of_lt (hx i)) ρ₁) hp
  -- Simplify (x_i^{rho1})^{rho2/rho1} = x_i^{rho2}
  have hrw : ∀ j ∈ Finset.univ, w j * ((x j) ^ ρ₁) ^ (ρ₂ / ρ₁) = w j * (x j) ^ ρ₂ := by
    intro j _; congr 1
    rw [← rpow_mul (le_of_lt (hx j)), mul_div_cancel₀ ρ₂ (ne_of_gt hρ₁)]
  rw [Finset.sum_congr rfl hrw] at step
  -- Simplify 1/(rho2/rho1) = rho1/rho2
  have h_inv : (1 : ℝ) / (ρ₂ / ρ₁) = ρ₁ / ρ₂ := by field_simp
  rw [h_inv] at step
  -- step : (1/J) Sum x_i^{rho1} le ((1/J) Sum x_i^{rho2})^{rho1/rho2}
  -- Convert weighted sums to (1/J) * Sum form
  have hw_rw : ∀ (ρ : ℝ), ∑ i ∈ Finset.univ, w i * (x i) ^ ρ =
      (1 / ↑J) * ∑ i : Fin J, (x i) ^ ρ := by
    intro ρ; simp [w, Finset.mul_sum]
  rw [hw_rw ρ₁, hw_rw ρ₂] at step
  -- Raise to 1/rho1: A^{1/rho1} le (B^{rho1/rho2})^{1/rho1} = B^{1/rho2}
  simp only [powerMean]
  have h1ρ₁ : (0 : ℝ) < 1 / ρ₁ := div_pos one_pos hρ₁
  have hA_nn : 0 ≤ (1 / ↑J) * ∑ i : Fin J, (x i) ^ ρ₁ :=
    mul_nonneg (div_nonneg one_pos.le (Nat.cast_nonneg J))
      (Finset.sum_nonneg (fun j _ => rpow_nonneg (le_of_lt (hx j)) ρ₁))
  have hB_nn : 0 ≤ (1 / ↑J) * ∑ i : Fin J, (x i) ^ ρ₂ :=
    mul_nonneg (div_nonneg one_pos.le (Nat.cast_nonneg J))
      (Finset.sum_nonneg (fun j _ => rpow_nonneg (le_of_lt (hx j)) ρ₂))
  -- From step and rpow_le_rpow: A^{1/rho1} le (B^{rho1/rho2})^{1/rho1}
  have key := rpow_le_rpow hA_nn step (le_of_lt h1ρ₁)
  -- Simplify RHS: (B^{rho1/rho2})^{1/rho1} = B^{(rho1/rho2)*(1/rho1)} = B^{1/rho2}
  rw [← rpow_mul hB_nn] at key
  have hexp : ρ₁ / ρ₂ * (1 / ρ₁) = 1 / ρ₂ := by field_simp
  rwa [hexp] at key

/-- Power mean ordering for curvature: higher rho means lower K means higher mean.
    Connects HLP inequality to the curvature interpretation. -/
theorem powerMean_mono_curvature {ρ₁ ρ₂ : ℝ} (_hρ₁ : 0 < ρ₁) (_hρ₂ : 0 < ρ₂)
    (hle : ρ₁ ≤ ρ₂) (hJ : 2 ≤ J) :
    curvatureK J ρ₂ ≤ curvatureK J ρ₁ := by
  simp only [curvatureK]
  have hJpos : (0 : ℝ) < ↑J := by exact_mod_cast (by omega : 0 < J)
  apply div_le_div_of_nonneg_right _ (le_of_lt hJpos)
  apply mul_le_mul_of_nonneg_right (by linarith)
  have : (1 : ℝ) ≤ ↑J := by exact_mod_cast (by omega : 1 ≤ J)
  linarith

-- ============================================================
-- Extension 7: CES Price Index (Dixit-Stiglitz 1977)
-- ============================================================

/-- The CES price index (Dixit-Stiglitz 1977):
    P = (Sum p_j^r)^{1/r} where r = rho/(rho-1) is the dual exponent.
    This is the cost-minimizing unit expenditure function dual to CES production. -/
def cesPriceIndex (J : ℕ) (ρ : ℝ) (p : Fin J → ℝ) : ℝ :=
  unnormCES J (dualExponent ρ) p

/-- The CES price index unfolds to (Sum p_j^{rho/(rho-1)})^{(rho-1)/rho}. -/
theorem cesPriceIndex_def {ρ : ℝ} (_hρ : ρ ≠ 0) (_hρ1 : ρ ≠ 1)
    {p : Fin J → ℝ} :
    cesPriceIndex J ρ p = (∑ j : Fin J, (p j) ^ (ρ / (ρ - 1))) ^ (1 / (ρ / (ρ - 1))) := by
  simp only [cesPriceIndex, unnormCES, dualExponent]

/-- The CES price index in standard sigma form: P = (Sum p_j^{1-sigma})^{1/(1-sigma)}.
    Since r = rho/(rho-1) = 1 - sigma when sigma = 1/(1-rho). -/
theorem cesPriceIndex_eq_sigma {ρ : ℝ} (hρ1 : ρ ≠ 1) {p : Fin J → ℝ} :
    cesPriceIndex J ρ p =
    (∑ j : Fin J, (p j) ^ (1 - elasticityOfSubstitution ρ)) ^
      (1 / (1 - elasticityOfSubstitution ρ)) := by
  simp only [cesPriceIndex, unnormCES]
  congr 1
  · apply Finset.sum_congr rfl; intro j _
    congr 1; exact dualExponent_eq_sigma hρ1
  · congr 1; exact dualExponent_eq_sigma hρ1

/-- The dual exponent rho/(rho-1) equals Mathlib's conjExponent rho = rho/(rho-1).
    This bridges the CES duality to Mathlib's Holder conjugate infrastructure. -/
theorem dualExponent_eq_conjExponent (ρ : ℝ) :
    dualExponent ρ = Real.conjExponent ρ := by
  simp only [dualExponent, Real.conjExponent]

-- Cost minimization duality (E = P·F) is proved as `shephards_lemma`
-- and `cesDemand_adding_up` below — no constrained optimization needed.

-- ============================================================
-- Extension 8: Jensen Gap for CES
-- ============================================================

/-- **Jensen's inequality for CES**: For 0 < rho le 1, t^rho is concave,
    so (1/J) Sum x_j^rho le ((1/J) Sum x_j)^rho by Jensen's inequality.

    This is the concavity of the power function on the nonneg reals
    applied with the uniform measure on J points.

    Uses Mathlib's `concaveOn_rpow` for the concavity of t^rho. -/
theorem jensen_ces_concave {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    {x : Fin J → ℝ} (hx : ∀ j, 0 ≤ x j) (hJ : 0 < J) :
    (1 / ↑J : ℝ) * ∑ j : Fin J, (x j) ^ ρ ≤
    ((1 / ↑J : ℝ) * ∑ j : Fin J, x j) ^ ρ := by
  have hconc := Real.concaveOn_rpow (le_of_lt hρ₀) hρ₁
  have hJr : (0 : ℝ) < ↑J := Nat.cast_pos.mpr hJ
  have hJne : (↑J : ℝ) ≠ 0 := ne_of_gt hJr
  set w : Fin J → ℝ := fun _ => (1 : ℝ) / ↑J
  have hw_nn : ∀ j ∈ Finset.univ, 0 ≤ w j := fun _ _ => by positivity
  have hw_sum : ∑ j ∈ Finset.univ, w j = 1 := by
    simp [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact div_self hJne
  have hx_mem : ∀ j ∈ Finset.univ, x j ∈ Set.Ici (0 : ℝ) := fun j _ => Set.mem_Ici.mpr (hx j)
  have step := ConcaveOn.le_map_sum hconc hw_nn hw_sum hx_mem
  simp only [smul_eq_mul, w] at step
  rwa [← Finset.mul_sum, ← Finset.mul_sum] at step

/-- The Jensen gap is non-negative: ((1/J)Sum x_j)^rho - (1/J)Sum x_j^rho ge 0
    for 0 < rho le 1. This is the diversity bonus from CES aggregation. -/
theorem jensen_gap_nonneg {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    {x : Fin J → ℝ} (hx : ∀ j, 0 ≤ x j) (hJ : 0 < J) :
    0 ≤ ((1 / ↑J : ℝ) * ∑ j : Fin J, x j) ^ ρ -
        (1 / ↑J : ℝ) * ∑ j : Fin J, (x j) ^ ρ := by
  linarith [jensen_ces_concave hρ₀ hρ₁ hx hJ]

/-- For 0 < rho le 1, the power mean is at most the arithmetic mean: M_rho(x) le (1/J) Sum x_j.
    Jensen's concavity of t^rho gives (1/J)Sum x_j^rho le ((1/J)Sum x_j)^rho;
    raising to 1/rho (monotone, since rho > 0) preserves the inequality. -/
theorem powerMean_le_arithMean {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ₁ : ρ ≤ 1) (hρne : ρ ≠ 0)
    {x : Fin J → ℝ} (hx : ∀ j, 0 ≤ x j) (hJ : 0 < J) :
    powerMean J ρ hρne x ≤ (1 / ↑J : ℝ) * ∑ j : Fin J, x j := by
  simp only [powerMean]
  have h_avg_nn : 0 ≤ (1 / ↑J) * ∑ j : Fin J, x j := by
    apply mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hx j))
  have h_inner_nn : 0 ≤ (1 / ↑J) * ∑ j : Fin J, (x j) ^ ρ := by
    apply mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => rpow_nonneg (hx j) ρ))
  have h1ρ : 0 < 1 / ρ := div_pos one_pos hρ₀
  -- Jensen: (1/J) Sum x_j^rho le ((1/J) Sum x_j)^rho
  have hjen := jensen_ces_concave hρ₀ hρ₁ hx hJ
  -- Raise to 1/rho: inner^{1/rho} le (avg^rho)^{1/rho} = avg
  have key := rpow_le_rpow h_inner_nn hjen (le_of_lt h1ρ)
  rwa [← rpow_mul h_avg_nn, mul_one_div_cancel (ne_of_gt hρ₀), rpow_one] at key

-- ============================================================
-- Extension 9: Holder Duality
-- ============================================================

/-- The dual exponent equals Mathlib's conjugate exponent (definitional). -/
theorem dualExponent_eq_conjExponent' (ρ : ℝ) :
    dualExponent ρ = Real.conjExponent ρ :=
  dualExponent_eq_conjExponent ρ

/-- For rho > 1 (substitutes regime), rho and its dual r = rho/(rho-1) are
    Holder conjugate: 1/rho + 1/r = 1. -/
theorem holder_conjugate_of_substitutes {ρ : ℝ} (hρ : 1 < ρ) :
    ρ.HolderConjugate (dualExponent ρ) := by
  rw [dualExponent_eq_conjExponent]
  exact Real.HolderConjugate.conjExponent hρ

/-- **Holder inequality for CES** (substitutes regime, rho > 1):
    Sum x_j p_j le lpNorm_rho(x) * lpNorm_r(p) where r = rho/(rho-1).

    In economics: total expenditure is bounded by the product
    of quantity aggregate and price aggregate (both as Lp norms).
    This is the functional-analytic foundation of CES duality. -/
theorem holder_ces_duality {ρ : ℝ} (hρ : 1 < ρ)
    {x p : Fin J → ℝ} (hx : ∀ j, 0 ≤ x j) (hp : ∀ j, 0 ≤ p j) :
    ∑ j : Fin J, x j * p j ≤
    lpNorm J ρ x * lpNorm J (dualExponent ρ) p := by
  simp only [lpNorm]
  have hx_abs : ∀ j ∈ Finset.univ, 0 ≤ x j := fun j _ => hx j
  have hp_abs : ∀ j ∈ Finset.univ, 0 ≤ p j := fun j _ => hp j
  rw [show ∑ j : Fin J, |x j| ^ ρ = ∑ j : Fin J, (x j) ^ ρ from
    Finset.sum_congr rfl (fun j _ => by rw [abs_of_nonneg (hx j)])]
  rw [show ∑ j : Fin J, |p j| ^ dualExponent ρ = ∑ j : Fin J, (p j) ^ dualExponent ρ from
    Finset.sum_congr rfl (fun j _ => by rw [abs_of_nonneg (hp j)])]
  exact inner_le_Lp_mul_Lq_of_nonneg Finset.univ (holder_conjugate_of_substitutes hρ) hx_abs hp_abs

/-- Curvature conservation as the complement-regime analogue of Holder duality.
    For rho < 1 (complements), both rho and r = rho/(rho-1) are outside (1, inf),
    so classical Holder does not apply directly. Instead, the algebraic
    identity |lambda_perp^F| * |lambda_perp^C| = 1/(Jcw) from
    FurtherProperties.curvature_conservation serves as the complement-regime
    counterpart: primal and dual curvatures are inversely related, with
    their product being a rho-independent constant.

    This theorem bridges the algebraic duality (Extension 7) to the
    eigenvalue duality (Proposition 9.3 in Paper 1). -/
theorem curvature_conservation_as_holder_complement {ρ : ℝ} (hρ : ρ < 1) (hρne : ρ ≠ 0)
    (hJ : 2 ≤ J) {c w : ℝ} (hc : 0 < c) (hw : 0 < w) :
    |cesEigenvaluePerp J ρ c| * |dualEigenvaluePerp J ρ w| = 1 / (↑J * c * w) :=
  curvature_conservation hJ hρ hρne hc hw

-- ============================================================
-- Extension 10: Euler's Theorem for Homogeneous Functions
-- ============================================================

/-- **Power mean is homogeneous of degree one** for non-negative inputs:
    M_rho(c x) = c M_rho(x) for c > 0.

    **Proof.** factor c^rho out of the sum, then use (c^rho)^{1/rho} = c. -/
theorem powerMean_homogDegOne {J : ℕ} (_hJ : 0 < J) {ρ : ℝ} (hρ : ρ ≠ 0)
    {x : Fin J → ℝ} (hx : ∀ j, 0 ≤ x j) {c : ℝ} (hc : 0 < c) :
    powerMean J ρ hρ (fun j => c * x j) = c * powerMean J ρ hρ x := by
  simp only [powerMean]
  have h1 : ∀ j, (c * x j) ^ ρ = c ^ ρ * (x j) ^ ρ := fun j =>
    mul_rpow (le_of_lt hc) (hx j)
  simp_rw [h1, ← Finset.mul_sum]
  rw [show (1 / ↑J : ℝ) * (c ^ ρ * ∑ j, (x j) ^ ρ) =
    c ^ ρ * ((1 / ↑J : ℝ) * ∑ j, (x j) ^ ρ) from by ring]
  rw [mul_rpow (rpow_nonneg (le_of_lt hc) ρ)
    (mul_nonneg (div_nonneg one_pos.le (Nat.cast_nonneg J))
      (Finset.sum_nonneg (fun j _ => rpow_nonneg (hx j) ρ)))]
  rw [← rpow_mul (le_of_lt hc), mul_one_div_cancel hρ, rpow_one]

/-- **Abstract Euler theorem** for degree-one homogeneous functions:
    If F(t x) = t F(x) for t > 0, then d/dt F(t x)|_{t=1} = F(x).

    **Proof.** near t = 1, F(t x) = t F(x), so the derivative equals
    that of the linear function t -> t F(x), which is F(x). -/
theorem euler_degree_one {J : ℕ} {F : (Fin J → ℝ) → ℝ}
    (hF : ∀ (x : Fin J → ℝ) (c : ℝ), c > 0 → F (fun j => c * x j) = c * F x)
    {x : Fin J → ℝ} {g' : ℝ}
    (hg : HasDerivAt (fun t => F (fun j => t * x j)) g' 1) :
    g' = F x := by
  -- F(t x) = t F(x) for t > 0, holds in a neighborhood of 1
  have heq : (fun t => F (fun j => t * x j)) =ᶠ[nhds (1 : ℝ)] (fun t => t * F x) :=
    Filter.eventually_iff_exists_mem.mpr ⟨Set.Ioi 0, Ioi_mem_nhds one_pos, fun t ht => hF x t ht⟩
  -- The linear function t -> t F(x) has derivative F(x) at t = 1
  have hlin : HasDerivAt (fun t : ℝ => t * F x) (F x) 1 := by
    have := (hasDerivAt_id (1 : ℝ)).mul_const (F x)
    simpa using this
  -- By uniqueness of derivatives (functions agree near 1)
  exact (heq.hasDerivAt_iff.mp hg).unique hlin

/-- CES gradient component: the explicit partial derivative formula.
    Partial_k M_rho(x) = (1/J) x_k^{rho-1} A^{(1-rho)/rho}
    where A = (1/J) Sum x_j^rho. -/
def cesGradComponent (J : ℕ) (ρ : ℝ) (x : Fin J → ℝ) (k : Fin J) : ℝ :=
  (1 / ↑J) * (x k) ^ (ρ - 1) *
    ((1 / ↑J : ℝ) * ∑ j : Fin J, (x j) ^ ρ) ^ ((1 - ρ) / ρ)

/-- **Euler identity for CES**: Sum x_k Partial_k M_rho = M_rho.
    This is the content of Euler's theorem for the CES production function:
    total factor payments exhaust output under constant returns to scale.

    **Proof.** purely algebraic, using rpow identities. -/
theorem euler_ces_algebraic {J : ℕ} (_hJ : 0 < J) {ρ : ℝ} (hρ : ρ ≠ 0)
    {x : Fin J → ℝ} (hx : ∀ j, 0 < x j) :
    ∑ k : Fin J, x k * cesGradComponent J ρ x k = powerMean J ρ hρ x := by
  simp only [cesGradComponent, powerMean]
  set A := (1 / ↑J : ℝ) * ∑ j : Fin J, (x j) ^ ρ with hA_def
  -- Step 1: x_k * (1/J) * x_k^{rho-1} * A^{...} = (1/J) * x_k^rho * A^{...}
  have h1 : ∀ k : Fin J,
      x k * ((1 / ↑J) * (x k) ^ (ρ - 1) * A ^ ((1 - ρ) / ρ)) =
      (1 / ↑J) * (x k) ^ ρ * A ^ ((1 - ρ) / ρ) := by
    intro k
    have hxk : 0 < x k := hx k
    have hrpow : x k * (x k) ^ (ρ - 1) = (x k) ^ ρ := by
      have h := rpow_add hxk 1 (ρ - 1)
      rw [show (1 : ℝ) + (ρ - 1) = ρ from by ring, rpow_one] at h
      exact h.symm
    have : x k * (1 / ↑J * (x k) ^ (ρ - 1) * A ^ ((1 - ρ) / ρ)) =
        1 / ↑J * (x k * (x k) ^ (ρ - 1)) * A ^ ((1 - ρ) / ρ) := by ring
    rw [this, hrpow]
  simp_rw [h1]
  -- Step 2: Factor A^{...} out of the sum
  rw [← Finset.sum_mul]
  -- Step 3: (1/J) Sum x_k^rho = A
  rw [← Finset.mul_sum]
  -- Step 4: A * A^{(1-rho)/rho} = A^{1/rho}
  have hA_pos : 0 < A := by
    apply mul_pos (div_pos one_pos (by exact_mod_cast _hJ : (0 : ℝ) < ↑J))
    exact Finset.sum_pos (fun j _ => rpow_pos_of_pos (hx j) ρ) ⟨⟨0, _hJ⟩, Finset.mem_univ _⟩
  calc A * A ^ ((1 - ρ) / ρ)
      = A ^ (1 : ℝ) * A ^ ((1 - ρ) / ρ) := by rw [rpow_one]
    _ = A ^ (1 + (1 - ρ) / ρ) := (rpow_add hA_pos 1 ((1 - ρ) / ρ)).symm
    _ = A ^ (1 / ρ) := by congr 1; field_simp; ring

/-- **CES gradient is a derivative**: The CES gradient component equals the partial
    derivative of the power mean with respect to the k-th input.

    HasDerivAt (fun t => powerMean J ρ hρ (update x k t)) (cesGradComponent J ρ x k) (x k)

    **Proof.** substitute t for x_k to get the function (1/J)(t^ρ + C)^{1/ρ}, differentiate
    by the chain rule (power of a power), then simplify (1/J)·ρ·(1/ρ) = 1/J. -/
theorem cesGradComponent_is_deriv {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ : ρ ≠ 0)
    {x : Fin J → ℝ} (hx : ∀ j, 0 < x j) (k : Fin J) :
    HasDerivAt (fun t => powerMean J ρ hρ (Function.update x k t))
               (cesGradComponent J ρ x k) (x k) := by
  simp only [powerMean, cesGradComponent]
  have hJpos : (0:ℝ) < ↑J := Nat.cast_pos.mpr hJ
  -- C = sum of x_j^ρ for j ≠ k
  set C := ∑ j ∈ (Finset.univ : Finset (Fin J)).erase k, (x j) ^ ρ with hC_def
  -- A = (1/J) * Σ x_j^ρ (also equals (1/J)*(x k^ρ + C))
  set A := (1/(↑J:ℝ)) * ∑ j : Fin J, (x j)^ρ with hA_def
  have hAxk : (1/(↑J:ℝ)) * ((x k)^ρ + C) = A := by
    rw [hA_def, hC_def]; congr 1
    have h := Finset.sum_erase_add Finset.univ (fun j => (x j)^ρ) (Finset.mem_univ k)
    linarith
  have hApos : 0 < A := mul_pos (div_pos one_pos hJpos)
    (Finset.sum_pos (fun j _ => rpow_pos_of_pos (hx j) ρ) ⟨⟨0, hJ⟩, Finset.mem_univ _⟩)
  -- Rewrite the function: updating x k to t gives inner sum = t^ρ + C
  have hfun_eq : (fun t : ℝ =>
      ((1/(↑J:ℝ)) * ∑ j : Fin J, (Function.update x k t j) ^ ρ) ^ (1/ρ)) =
      (fun t => ((1/(↑J:ℝ)) * (t ^ ρ + C)) ^ (1/ρ)) := funext (fun t => by
    congr 2
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ k)]
    rw [Finset.sum_insert (Finset.notMem_erase k _)]
    simp only [Function.update_self]; congr 1
    apply Finset.sum_congr rfl; intro j hj
    simp [Function.update_of_ne ((Finset.mem_erase.mp hj).1)])
  rw [hfun_eq]
  -- Derivative of (1/J)*(t^ρ + C) at x k is (1/J)*(ρ*(x k)^(ρ-1))
  have hAd : HasDerivAt (fun t : ℝ => (1/(↑J:ℝ)) * (t^ρ + C))
      ((1/(↑J:ℝ)) * (ρ * (x k)^(ρ-1))) (x k) := by
    have h := ((hasDerivAt_id (x k)).rpow_const (p := ρ) (Or.inl (hx k).ne'))
    simp only [id, one_mul] at h
    exact (h.add_const C).const_mul (1/(↑J:ℝ))
  -- Chain rule: d/dt [f(t)^(1/ρ)] = f'(t)*(1/ρ)*f(t)^(1/ρ-1)
  have h_rpow := hAd.rpow_const (p := 1/ρ) (Or.inl (hAxk ▸ hApos).ne')
  -- Rewrite (1/J)*((x k)^ρ + C) to A in the derivative
  have hOuter := hAxk ▸ h_rpow
  -- The derivative equals cesGradComponent: (1/J)·ρ·(1/ρ) = 1/J
  have hkey : (1/(↑J:ℝ)) * (ρ * (x k)^(ρ-1)) * (1/ρ) * A ^ ((1:ℝ)/ρ - 1) =
      1/↑J * (x k)^(ρ-1) * A ^ ((1-ρ)/ρ) := by
    have h1 : (1:ℝ)/ρ - 1 = (1-ρ)/ρ := by field_simp [hρ]
    have h2 : (1/(↑J:ℝ)) * (ρ * (x k)^(ρ-1)) * (1/ρ) = 1/↑J * (x k)^(ρ-1) := by
      field_simp [hρ]
    rw [h1, h2]
  exact hkey ▸ hOuter

-- ============================================================
-- Extension 11: CES to Cobb-Douglas Limit (rho to 0)
-- ============================================================

/-- Geometric mean on Fin J: (Prod x_j)^{1/J}. -/
def geometricMean (J : ℕ) (x : Fin J → ℝ) : ℝ :=
  (∏ j : Fin J, x j) ^ (1 / (↑J : ℝ))

/-- At the symmetric point, the geometric mean equals c.
    This is consistent with the power mean limit. -/
theorem geometricMean_symmetric {J : ℕ} (hJ : 0 < J) {c : ℝ} (hc : 0 < c) :
    geometricMean J (symmetricPoint J c) = c := by
  simp only [geometricMean, symmetricPoint, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← rpow_natCast c J, ← rpow_mul (le_of_lt hc)]
  simp [Nat.cast_ne_zero.mpr (by omega : J ≠ 0)]

/-- The inner CES sum (1/J) Sum x_j^rho has a well-defined derivative
    with respect to rho at rho = 0, equal to (1/J) Sum log(x_j).

    This is the key calculus step in the Cobb-Douglas limit proof.
    Uses HasDerivAt.const_rpow: d/drho[a^rho] = log(a) a^rho. -/
theorem ces_inner_hasDerivAt {J : ℕ} (_hJ : 0 < J) {x : Fin J → ℝ} (hx : ∀ j, 0 < x j) :
    HasDerivAt (fun (ρ : ℝ) => (1 / (J : ℝ)) * ∑ j : Fin J, (x j) ^ ρ)
      ((1 / (J : ℝ)) * ∑ j : Fin J, Real.log (x j)) (0 : ℝ) := by
  -- Each x_j^rho has derivative log(x_j) at rho = 0
  have hderiv' : ∀ j : Fin J,
      HasDerivAt (fun (ρ : ℝ) => (x j) ^ ρ) (Real.log (x j)) (0 : ℝ) := by
    intro j
    have h := HasDerivAt.const_rpow (hx j) (hasDerivAt_id (0 : ℝ))
    convert h using 1; simp [Real.rpow_zero]
  -- Sum of derivatives (fun_sum matches lambda form)
  have hsum : HasDerivAt (fun (ρ : ℝ) => ∑ j : Fin J, (x j) ^ ρ)
      (∑ j : Fin J, Real.log (x j)) (0 : ℝ) :=
    HasDerivAt.fun_sum (fun j _ => hderiv' j)
  -- Multiply by constant 1/J
  exact hsum.const_mul (1 / (J : ℝ))

/-- **CES to Cobb-Douglas limit**: As rho to 0+, the power mean converges
    to the geometric mean.

    **Proof.** let A(ρ) = (1/J) Σ x_j^ρ. Then A(0) = 1 and A'(0) = (1/J) Σ log(x_j)
    by ces_inner_hasDerivAt. Since M_ρ = A(ρ)^{1/ρ} = exp(log A(ρ)/ρ), and
    log A(ρ)/ρ → (log A)'(0) = A'(0)/A(0) = (1/J) Σ log(x_j) by L'Hôpital,
    we get M_ρ → exp((1/J) Σ log(x_j)) = (Π x_j)^{1/J} = geometricMean J x. -/
theorem ces_limit_cobbDouglas {J : ℕ} (hJ : 0 < J) {x : Fin J → ℝ} (hx : ∀ j, 0 < x j) :
    Filter.Tendsto
      (fun ρ : ℝ => ((1 / (↑J : ℝ)) * ∑ j : Fin J, (x j) ^ ρ) ^ (1 / ρ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (geometricMean J x)) := by
  set A : ℝ → ℝ := fun ρ => (1 / (↑J : ℝ)) * ∑ j : Fin J, (x j) ^ ρ with hA_def
  set D := (1 / (↑J : ℝ)) * ∑ j : Fin J, Real.log (x j)
  have hJpos : (0 : ℝ) < ↑J := Nat.cast_pos.mpr hJ
  have hAd := ces_inner_hasDerivAt hJ hx
  have hA0 : A 0 = 1 := by simp [A, rpow_zero, hJ.ne']
  have hApos : ∀ ρ, 0 < A ρ := fun ρ =>
    mul_pos (div_pos one_pos hJpos)
      (Finset.sum_pos (fun j _ => rpow_pos_of_pos (hx j) ρ) ⟨⟨0, hJ⟩, Finset.mem_univ _⟩)
  -- log A(ρ) has derivative D at 0 (chain rule: (log A)'(0) = A'(0)/A(0) = D/1 = D)
  have hlogAd : HasDerivAt (fun ρ => Real.log (A ρ)) D 0 := by
    have h := (hasDerivAt_log (hApos 0).ne').comp 0 hAd
    simp only [hA0, inv_one, one_mul] at h
    exact h
  have hlogA0 : Real.log (A 0) = 0 := by rw [hA0]; exact log_one
  -- log A(ρ)/ρ → D as ρ → 0+ (this is the "0/0" limit resolved by the derivative)
  have hslope : Filter.Tendsto (fun ρ => Real.log (A ρ) / ρ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds D) := by
    have hts := hasDerivAt_iff_tendsto_slope.mp hlogAd
    have hmono : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin 0 {0}ᶜ :=
      nhdsWithin_mono 0 (fun _ hρ => hρ.ne')
    exact (hts.mono_left hmono).congr'
      (eventually_nhdsWithin_of_forall (fun ρ _ => by
        simp only [slope_def_field, hlogA0, sub_zero]))
  -- exp(D) = geometricMean J x
  have hexpD : Real.exp D = geometricMean J x := by
    simp only [geometricMean]
    rw [show D = (1 / (↑J : ℝ)) * ∑ j : Fin J, Real.log (x j) from rfl,
        ← Real.log_prod (fun j _ => (hx j).ne'),
        Real.rpow_def_of_pos (Finset.prod_pos (fun j _ => hx j))]
    congr 1; ring
  -- Conclude: A(ρ)^{1/ρ} = exp(log A(ρ)/ρ) → exp(D) = geometricMean
  rw [← hexpD]
  exact ((Real.continuous_exp.continuousAt.tendsto).comp hslope).congr'
    (eventually_nhdsWithin_of_forall (fun ρ _ => by
      simp only [Function.comp, A, rpow_def_of_pos (hApos _)]
      congr 1; ring))

-- ============================================================
-- Extension 12: Shephard's Lemma and CES Demand
-- ============================================================

/-- **Escort distribution is HOD(0)**: Scaling all inputs by c > 0
    leaves the escort distribution unchanged.
    P_j(cx) = (c x_j)^q / Σ(c x_k)^q = c^q x_j^q / c^q Σ x_k^q = P_j(x).

    This is the CES demand homogeneity result: multiplying all prices
    by the same constant does not change relative allocations. -/
theorem escortDistribution_hod_zero {x : Fin J → ℝ} (hx : ∀ j, 0 < x j)
    {c : ℝ} (hc : 0 < c) (q : ℝ) (j : Fin J) :
    escortDistribution J q (fun k => c * x k) j = escortDistribution J q x j := by
  simp only [escortDistribution]
  have hrw : ∀ k : Fin J, (c * x k) ^ q = c ^ q * (x k) ^ q :=
    fun k => mul_rpow (le_of_lt hc) (le_of_lt (hx k))
  simp_rw [hrw, ← Finset.mul_sum]
  rw [mul_div_mul_left _ _ (ne_of_gt (rpow_pos_of_pos hc q))]

/-- **CES Slutsky term**: The compensated price elasticity of CES demand.
    S_{jk} = σ · s_j · (δ_{jk} - s_k) where s_j is factor share j.
    The Slutsky matrix from CES is symmetric because s_j · s_k = s_k · s_j. -/
def cesSlutkyTerm (σ : ℝ) (s : Fin J → ℝ) (j k : Fin J) : ℝ :=
  σ * s j * ((if j = k then 1 else 0) - s k)

/-- **Slutsky symmetry for CES**: The CES Slutsky matrix is symmetric.
    For j = k: trivially symmetric.
    For j ≠ k: S_{jk} = -σ s_j s_k = -σ s_k s_j = S_{kj}. -/
theorem cesSlutky_symmetric (σ : ℝ) (s : Fin J → ℝ) (j k : Fin J) :
    cesSlutkyTerm σ s j k = cesSlutkyTerm σ s k j := by
  simp only [cesSlutkyTerm]
  by_cases hjk : j = k
  · subst hjk; ring
  · simp only [hjk, Ne.symm hjk, ite_false]; ring

/-- CES unit cost function: the minimum cost of producing one unit
    of output given input prices p. This equals the CES price index.
    C(p) = (Sum p_j^r)^{1/r} where r = rho/(rho-1). -/
def cesUnitCost (J : ℕ) (ρ : ℝ) (p : Fin J → ℝ) : ℝ :=
  cesPriceIndex J ρ p

/-- Conditional CES demand: the cost-minimizing input quantity for input k
    given prices p and output level y.
    x_k*(p,y) = y (p_k / C(p))^{-sigma} / J
    where sigma = 1/(1-rho) is the elasticity of substitution.

    This is Shephard's lemma applied to the CES cost function. -/
def cesDemand (J : ℕ) (ρ : ℝ) (p : Fin J → ℝ) (k : Fin J) (y : ℝ) : ℝ :=
  y * (p k) ^ (ρ / (ρ - 1) - 1) * (cesUnitCost J ρ p) ^ (1 - ρ / (ρ - 1))

/-- **Shephard's lemma**: The derivative of the CES cost function with respect
    to input price p_k equals the conditional demand for input k at unit output:
    ∂C/∂p_k = x_k*(p, 1).

    Direct computation: C(p) = (Σ p_j^r)^{1/r} where r = ρ/(ρ-1).
    The chain rule gives ∂C/∂p_k = p_k^{r-1} · (Σ p_j^r)^{(1-r)/r},
    which equals the CES demand at unit output. No constrained optimization needed.

    **Proof.** Write $C(p) = S(p)^{1/r}$ where $S = \sum_j p_j^r$ and $r = \rho/(\rho-1)$. Isolate the $k$-th term: $S = p_k^r + C_{\neg k}$ where $C_{\neg k}$ is constant in $p_k$. Apply the chain rule: $\partial C/\partial p_k = (1/r) \cdot S^{1/r - 1} \cdot r \cdot p_k^{r-1} = p_k^{r-1} \cdot S^{(1-r)/r}$, which is the CES demand at unit output by the algebraic identity $(1/r)(1-r) = 1/r - 1$. -/
theorem shephards_lemma {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ : ρ ≠ 0) (hρ1 : ρ ≠ 1)
    {p : Fin J → ℝ} (hp : ∀ j, 0 < p j) (k : Fin J) :
    HasDerivAt (fun t => cesUnitCost J ρ (Function.update p k t))
               (cesDemand J ρ p k 1) (p k) := by
  simp only [cesUnitCost, cesPriceIndex, cesDemand, unnormCES, dualExponent]
  set r := ρ / (ρ - 1)
  have hr : r ≠ 0 := div_ne_zero hρ (sub_ne_zero.mpr hρ1)
  set S := ∑ j : Fin J, (p j) ^ r
  set C := ∑ j ∈ Finset.univ.erase k, (p j) ^ r
  have hSpk : (p k) ^ r + C = S := by
    simp only [S, C]
    have h := Finset.sum_erase_add Finset.univ (fun j => (p j) ^ r) (Finset.mem_univ k)
    linarith
  have hSpos : 0 < S := by
    simp only [S]
    exact Finset.sum_pos (fun j _ => rpow_pos_of_pos (hp j) r)
      ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  -- Rewrite the function: updating p k to t gives inner sum = t^r + C
  have hfun_eq : (fun t : ℝ =>
      (∑ j : Fin J, (Function.update p k t j) ^ r) ^ (1 / r)) =
      (fun t => (t ^ r + C) ^ (1 / r)) := funext (fun t => by
    congr 1
    conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ k)]
    rw [Finset.sum_insert (Finset.notMem_erase k _)]
    simp only [Function.update_self]; congr 1
    apply Finset.sum_congr rfl; intro j hj
    simp [Function.update_of_ne ((Finset.mem_erase.mp hj).1)])
  rw [hfun_eq]
  -- Inner derivative: d/dt [t^r + C] = r * t^{r-1}
  have hAd : HasDerivAt (fun t : ℝ => t ^ r + C)
      (r * (p k) ^ (r - 1)) (p k) := by
    have h := (hasDerivAt_id (p k)).rpow_const (p := r) (Or.inl (hp k).ne')
    simp only [id, one_mul] at h
    exact h.add_const C
  -- Chain rule: d/dt [(t^r + C)^{1/r}]
  have h_rpow := hAd.rpow_const (p := 1 / r) (Or.inl (hSpk ▸ hSpos).ne')
  have hOuter := hSpk ▸ h_rpow
  -- Algebraic identity: chain rule derivative = cesDemand form
  have hkey : r * (p k) ^ (r - 1) * (1 / r) * S ^ (1 / r - 1) =
      1 * (p k) ^ (r - 1) * (S ^ (1 / r)) ^ (1 - r) := by
    rw [← Real.rpow_mul (le_of_lt hSpos)]
    have h1 : 1 / r * (1 - r) = 1 / r - 1 := by field_simp [hr]
    rw [h1]
    have h2 : r * (p k) ^ (r - 1) * (1 / r) = 1 * (p k) ^ (r - 1) := by
      field_simp [hr]
    rw [h2]
  exact hkey ▸ hOuter

/-- **Adding-up property**: Total expenditure on CES demands equals cost.
    Σ_k p_k · x_k*(p,y) = C(p) · y.
    **Proof.** p_k · (p_k)^{r-1} = (p_k)^r, so the sum telescopes to
    (S^{1/r})^{1-r} · S = S^{1/r} = C(p). -/
theorem cesDemand_adding_up {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ : ρ ≠ 0) (hρ1 : ρ ≠ 1)
    {p : Fin J → ℝ} (hp : ∀ j, 0 < p j) (y : ℝ) :
    ∑ k : Fin J, p k * cesDemand J ρ p k y = cesUnitCost J ρ p * y := by
  simp only [cesDemand, cesUnitCost, cesPriceIndex, unnormCES, dualExponent]
  set r := ρ / (ρ - 1)
  have hr : r ≠ 0 := div_ne_zero hρ (sub_ne_zero.mpr hρ1)
  set S := ∑ j : Fin J, (p j) ^ r
  have hSpos : 0 < S := Finset.sum_pos (fun j _ => rpow_pos_of_pos (hp j) r)
    ⟨⟨0, hJ⟩, Finset.mem_univ _⟩
  -- Each term: p k * (y * (p k)^{r-1} * (S^{1/r})^{1-r}) = y * (S^{1/r})^{1-r} * (p k)^r
  have hterm : ∀ k : Fin J,
      p k * (y * (p k) ^ (r - 1) * (S ^ (1 / r)) ^ (1 - r)) =
      y * (S ^ (1 / r)) ^ (1 - r) * (p k) ^ r := by
    intro k
    have hpk : p k * (p k) ^ (r - 1) = (p k) ^ r := by
      have h := rpow_add (hp k) 1 (r - 1)
      rw [rpow_one, show 1 + (r - 1) = r from by ring] at h; exact h.symm
    rw [show p k * (y * (p k) ^ (r - 1) * (S ^ (1 / r)) ^ (1 - r)) =
        y * (S ^ (1 / r)) ^ (1 - r) * (p k * (p k) ^ (r - 1)) from by ring]
    rw [hpk]
  simp_rw [hterm, ← Finset.mul_sum]
  -- Goal: y * (S^{1/r})^{1-r} * S = S^{1/r} * y
  rw [← rpow_mul (le_of_lt hSpos)]
  -- Combine: S^{a} * S = S^{a+1} where a = 1/r*(1-r)
  have key : S ^ (1 / r * (1 - r)) * S = S ^ (1 / r) := by
    have h := rpow_add hSpos (1 / r * (1 - r)) 1
    rw [rpow_one, show 1 / r * (1 - r) + 1 = 1 / r from by field_simp [hr]; ring] at h
    exact h.symm
  have : y * S ^ (1 / r * (1 - r)) * S = y * (S ^ (1 / r * (1 - r)) * S) := by ring
  rw [this, key]; ring

-- ============================================================
-- Extension 13: CES Consumer Duality
-- ============================================================

/-- **CES price index positivity**: C(p) > 0 when all prices are positive and J > 0.

    **Proof.** C(p) = (Σ p_j^r)^{1/r}. Each p_j^r > 0, so the sum is positive,
    and a positive real raised to any power is positive. -/
theorem cesPriceIndex_pos {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ1 : ρ ≠ 1)
    {p : Fin J → ℝ} (hp : ∀ j, 0 < p j) :
    0 < cesPriceIndex J ρ p := by
  simp only [cesPriceIndex, unnormCES]
  apply rpow_pos_of_pos
  exact Finset.sum_pos (fun j _ => rpow_pos_of_pos (hp j) _) ⟨⟨0, hJ⟩, Finset.mem_univ _⟩

/-- **CES indirect utility**: V(p, I) = I / C(p).
    The maximum utility achievable with income I at prices p equals
    income divided by the unit cost function (CES price index).

    **Proof.** By definition: the consumer maximizes F(x) subject to
    Σ p_k x_k ≤ I. At the optimum, x* = cesDemand(p, I/C(p)),
    and F(x*) = I/C(p) by homogeneity of degree 1. -/
def cesIndirectUtility (J : ℕ) (ρ : ℝ) (p : Fin J → ℝ) (I : ℝ) : ℝ :=
  I / cesUnitCost J ρ p

/-- **CES expenditure function**: E(p, u) = u · C(p).
    The minimum expenditure needed to achieve utility level u at prices p.

    **Proof.** Duality: E(p, V(p, I)) = V(p,I) · C(p) = (I/C(p)) · C(p) = I.
    Equivalently, E is the inverse of V in the income argument. -/
def cesExpenditureFunction (J : ℕ) (ρ : ℝ) (p : Fin J → ℝ) (u : ℝ) : ℝ :=
  u * cesUnitCost J ρ p

/-- **Duality identity**: E(p, V(p, I)) = I.
    Expenditure at the optimal utility level recovers income.

    **Proof.** E(p, V(p,I)) = V(p,I) · C(p) = (I/C(p)) · C(p) = I.
    Uses `div_mul_cancel₀` with C(p) ≠ 0. -/
theorem expenditure_indirect_duality {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ1 : ρ ≠ 1)
    {p : Fin J → ℝ} (hp : ∀ j, 0 < p j) {I : ℝ} :
    cesExpenditureFunction J ρ p (cesIndirectUtility J ρ p I) = I := by
  simp only [cesExpenditureFunction, cesIndirectUtility, cesUnitCost]
  rw [div_mul_cancel₀]
  exact ne_of_gt (cesPriceIndex_pos hJ hρ1 hp)

/-- **Indirect utility is decreasing in each price**: ∂V/∂p_k < 0.
    Higher prices reduce achievable utility at fixed income.

    **Proof.** V(p,I) = I / C(p). Since C(p) is increasing in p_k
    (Shephard's lemma gives ∂C/∂p_k = x_k > 0), V is decreasing.
    By the quotient rule: V'(p_k) = -I · C'(p_k) / C(p)². -/
theorem indirect_utility_antitone_in_price {J : ℕ} (hJ : 0 < J) {ρ : ℝ}
    (hρ : ρ ≠ 0) (hρ1 : ρ ≠ 1) {p : Fin J → ℝ} (hp : ∀ j, 0 < p j)
    {I : ℝ} (hI : 0 < I) (k : Fin J) :
    HasDerivAt (fun t => cesIndirectUtility J ρ (Function.update p k t) I)
      (-(I * cesDemand J ρ p k 1 / (cesUnitCost J ρ p) ^ 2)) (p k) := by
  simp only [cesIndirectUtility]
  have hC : cesUnitCost J ρ (Function.update p k (p k)) ≠ 0 := by
    rw [Function.update_eq_self]; exact ne_of_gt (cesPriceIndex_pos hJ hρ1 hp)
  have h := (hasDerivAt_const (p k) I).div (shephards_lemma hJ hρ hρ1 hp k) hC
  simp only [Pi.div_apply] at h
  rw [Function.update_eq_self] at hC h
  convert h using 1
  have hC' : cesUnitCost J ρ p ≠ 0 := ne_of_gt (cesPriceIndex_pos hJ hρ1 hp)
  field_simp
  ring

/-- **Roy's identity**: x_k = -( ∂V/∂p_k ) / ( ∂V/∂I ).
    The Marshallian demand equals the ratio of marginal indirect utilities.

    For CES: ∂V/∂I = 1/C(p) and ∂V/∂p_k = -I·x_k(1)/C(p)².
    So -( ∂V/∂p_k ) / ( ∂V/∂I ) = I·x_k(1)/C(p) = x_k(p, I/C(p))
    = cesDemand at utility-maximizing output level.

    We prove the algebraic identity that the ratio of derivatives equals
    the Hicksian demand at optimal output level. -/
theorem roys_identity_ratio {J : ℕ} (hJ : 0 < J) {ρ : ℝ} (hρ1 : ρ ≠ 1)
    {p : Fin J → ℝ} (hp : ∀ j, 0 < p j) {I : ℝ} (k : Fin J) :
    -- Roy's identity: x_k = (I · x_k(1) / C²) / (1/C) = I · x_k(1) / C
    I * cesDemand J ρ p k 1 / (cesUnitCost J ρ p) ^ 2 /
    (1 / cesUnitCost J ρ p) =
    cesDemand J ρ p k (I / cesUnitCost J ρ p) := by
  simp only [cesDemand]
  have hC : cesUnitCost J ρ p ≠ 0 := ne_of_gt (cesPriceIndex_pos hJ hρ1 hp)
  field_simp

-- ============================================================
-- Discrete Choice: Logit Probability and Inclusive Value
-- ============================================================

/-- The multinomial logit choice probability:
    P_j = exp(ε_j / T) / Σ_k exp(ε_k / T)

    McFadden (1974) showed this is the unique choice rule consistent
    with random utility maximization when errors are i.i.d. Gumbel. -/
def logitProbability (J : ℕ) (T : ℝ) (ε : Fin J → ℝ) (j : Fin J) : ℝ :=
  Real.exp (ε j / T) / ∑ k : Fin J, Real.exp (ε k / T)

/-- McFadden's inclusive value (log-sum):
    IV = T · log(Σ_k exp(ε_k / T))

    This is the expected maximum utility from a choice set.
    It is the CES aggregate in the substitutes limit (ρ → 1). -/
def inclusiveValue (J : ℕ) (T : ℝ) (ε : Fin J → ℝ) : ℝ :=
  T * Real.log (∑ k : Fin J, Real.exp (ε k / T))

/-- **Logit is CES escort at q = 1**: The escort distribution at q = 1
    applied to the vector exp(ε/T) recovers the multinomial logit.

    **Proof.** At $q = 1$, the escort distribution is $x_j^1 / \sum_k x_k^1 = x_j / \sum_k x_k$. Substituting $x_k = \exp(\varepsilon_k / T)$ yields $\exp(\varepsilon_j/T) / \sum_k \exp(\varepsilon_k/T)$, which is the logit formula. The key step is `rpow_one`: $x^1 = x$. -/
theorem logit_is_ces_at_q_one (T : ℝ) (_hT : T ≠ 0) (ε : Fin J → ℝ) (j : Fin J) :
    logitProbability J T ε j =
    escortDistribution J 1 (fun k => Real.exp (ε k / T)) j := by
  simp only [logitProbability, escortDistribution, rpow_one]

end
