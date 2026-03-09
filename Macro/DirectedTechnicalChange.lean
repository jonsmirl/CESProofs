/-
  Directed Technical Change Extension (Acemoglu 2002)

  Connects the CES substitution parameter ρ to the direction of innovation.
  Factor-augmenting technical change Y = [α(A_K·K)^ρ + (1-α)(A_L·L)^ρ]^{1/ρ}
  is just TwoFactorCES with rescaled inputs. The direction of innovation in
  equilibrium depends on σ = 1/(1-ρ), with a critical threshold at σ = 2
  that determines whether the skill premium rises or falls with factor supply.

  Key result: Under directed technical change equilibrium (A_K/A_L = (K/L)^{σ-1}),
  the relative factor price simplifies to MPK/MPL = (α/(1-α)) · (K/L)^{σ-2}.
  When σ < 2 (our empirical estimate σ̂ ≈ 0.83), increasing relative supply
  of a factor *decreases* its relative price even after innovation responds.

  All proofs are algebraic — no axioms, no sorry.
-/

import CESProofs.Macro.TwoFactorCES

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Section 1: Core Definitions
-- ============================================================

/-- The CES inner aggregate with factor-augmenting technology:
    α · (A_K · K)^ρ + (1-α) · (A_L · L)^ρ.
    This is cesInner applied to effective inputs A_K·K and A_L·L. -/
def factorAugmentedInner (α ρ A_K K A_L L : ℝ) : ℝ :=
  α * (A_K * K) ^ ρ + (1 - α) * (A_L * L) ^ ρ

/-- Factor-augmented CES production function (TFP = 1, absorbed into A_K, A_L):
    Y = [α · (A_K · K)^ρ + (1-α) · (A_L · L)^ρ]^{1/ρ}. -/
def factorAugmentedCES (α ρ A_K K A_L L : ℝ) : ℝ :=
  (factorAugmentedInner α ρ A_K K A_L L) ^ (1 / ρ)

/-- Marginal product of capital under factor augmentation:
    ∂Y/∂K = A_K · ∂Y/∂(A_K·K) via the chain rule. -/
def mpkFactorAugmented (α ρ A_K K A_L L : ℝ) : ℝ :=
  A_K * marginalProductK 1 α ρ (A_K * K) (A_L * L)

/-- Marginal product of labor under factor augmentation:
    ∂Y/∂L = A_L · ∂Y/∂(A_L·L) via the chain rule. -/
def mplFactorAugmented (α ρ A_K K A_L L : ℝ) : ℝ :=
  A_L * marginalProductL 1 α ρ (A_K * K) (A_L * L)

/-- The relative factor price under factor-augmenting technical change:
    MPK/MPL = (α/(1-α)) · (A_K/A_L)^ρ · (K/L)^{ρ-1}.
    Decomposes into a technology component and a factor ratio component. -/
def relativeWageDTC (α ρ A_K K A_L L : ℝ) : ℝ :=
  (α / (1 - α)) * (A_K / A_L) ^ ρ * (K / L) ^ (ρ - 1)

/-- The equilibrium technology bias under directed technical change:
    A_K/A_L = (K/L)^{σ-1} from the free-entry condition in R&D.
    When σ > 1: innovation directed toward abundant factor.
    When σ < 1: innovation directed toward scarce factor. -/
def dtcEquilibriumBias (σ K_L_ratio : ℝ) : ℝ :=
  K_L_ratio ^ (σ - 1)

/-- The exponent controlling whether factor supply raises or lowers
    the relative wage after DTC substitution: σ - 2.
    Positive when σ > 2 (market size dominates), negative when σ < 2 (price dominates). -/
def skillPremiumExponent (σ : ℝ) : ℝ :=
  σ - 2

-- ============================================================
-- Section 2: Bridge to TwoFactorCES
-- ============================================================

/-- factorAugmentedInner is cesInner applied to effective inputs. -/
theorem factorAugmentedInner_eq_cesInner {α ρ A_K K A_L L : ℝ} :
    factorAugmentedInner α ρ A_K K A_L L = cesInner α ρ (A_K * K) (A_L * L) := rfl

/-- Factor-augmented CES is twoFactorCES with A=1 and effective inputs. -/
theorem factorAugmentedCES_eq_twoFactorCES {α ρ A_K K A_L L : ℝ} :
    factorAugmentedCES α ρ A_K K A_L L = twoFactorCES 1 α ρ (A_K * K) (A_L * L) := by
  simp only [factorAugmentedCES, twoFactorCES, factorAugmentedInner, cesInner, one_mul]

/-- The inner aggregate is positive under standard conditions. -/
theorem factorAugmentedInner_pos {α ρ A_K K A_L L : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (hAK : 0 < A_K) (hK : 0 < K) (hAL : 0 < A_L) (hL : 0 < L) :
    0 < factorAugmentedInner α ρ A_K K A_L L := by
  rw [factorAugmentedInner_eq_cesInner]
  exact cesInner_pos hα hα1 (mul_pos hAK hK) (mul_pos hAL hL)

-- ============================================================
-- Section 3: CRS and Exhaustion
-- ============================================================

/-- **CRS under factor augmentation**: Y(A_K, c·K, A_L, c·L) = c · Y(A_K, K, A_L, L).
    Scaling physical inputs (K, L) by c scales output by c, for fixed technology. -/
theorem factorAugmentedCES_crs {α ρ A_K K A_L L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0)
    (hAK : 0 < A_K) (hAL : 0 < A_L)
    (hK : 0 < K) (hL : 0 < L) {c : ℝ} (hc : 0 < c) :
    factorAugmentedCES α ρ A_K (c * K) A_L (c * L) =
    c * factorAugmentedCES α ρ A_K K A_L L := by
  rw [factorAugmentedCES_eq_twoFactorCES, factorAugmentedCES_eq_twoFactorCES]
  rw [show A_K * (c * K) = c * (A_K * K) from by ring,
      show A_L * (c * L) = c * (A_L * L) from by ring]
  exact twoFactorCES_homogDegOne one_pos hα hα1 hρ
    (mul_pos hAK hK) (mul_pos hAL hL) hc

/-- **Euler's theorem under factor augmentation**: MPK·K + MPL·L = Y.
    Factor payments exhaust output under CRS. -/
theorem euler_factorAugmented {α ρ A_K K A_L L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hρ : ρ ≠ 0)
    (hAK : 0 < A_K) (hAL : 0 < A_L)
    (hK : 0 < K) (hL : 0 < L) :
    mpkFactorAugmented α ρ A_K K A_L L * K +
    mplFactorAugmented α ρ A_K K A_L L * L =
    factorAugmentedCES α ρ A_K K A_L L := by
  simp only [mpkFactorAugmented, mplFactorAugmented]
  rw [factorAugmentedCES_eq_twoFactorCES]
  rw [show A_K * marginalProductK 1 α ρ (A_K * K) (A_L * L) * K =
      marginalProductK 1 α ρ (A_K * K) (A_L * L) * (A_K * K) from by ring,
      show A_L * marginalProductL 1 α ρ (A_K * K) (A_L * L) * L =
      marginalProductL 1 α ρ (A_K * K) (A_L * L) * (A_L * L) from by ring]
  exact euler_two_factor one_pos hα hα1 hρ (mul_pos hAK hK) (mul_pos hAL hL)

-- ============================================================
-- Section 4: Relative Wage Formula
-- ============================================================

/-- Helper: x · x^{ρ-1} = x^ρ for positive x. -/
private lemma rpow_succ_pred {x : ℝ} (hx : 0 < x) (ρ : ℝ) :
    x * x ^ (ρ - 1) = x ^ ρ := by
  have h := rpow_add hx 1 (ρ - 1)
  rw [rpow_one, show 1 + (ρ - 1) = ρ from by ring] at h
  exact h.symm

/-- **Relative wage formula**: The ratio of marginal products under factor
    augmentation decomposes into technology and factor ratio components:
    MPK/MPL = (α/(1-α)) · (A_K/A_L)^ρ · (K/L)^{ρ-1}.

    Proof strategy: Factor out A_K/A_L, apply mp_ratio for effective inputs,
    decompose the effective input ratio, combine A terms via rpow_succ_pred. -/
theorem relativeWage_formula {α ρ A_K K A_L L : ℝ}
    (hα : 0 < α) (hα1 : α < 1) {_hρ : ρ ≠ 0}
    (hAK : 0 < A_K) (hAL : 0 < A_L) (hK : 0 < K) (hL : 0 < L) :
    mpkFactorAugmented α ρ A_K K A_L L / mplFactorAugmented α ρ A_K K A_L L =
    relativeWageDTC α ρ A_K K A_L L := by
  simp only [mpkFactorAugmented, mplFactorAugmented]
  have hAKK := mul_pos hAK hK
  have hALL := mul_pos hAL hL
  -- Step 1: Factor a*b/(c*d) = (a/c)*(b/d)
  rw [mul_div_mul_comm]
  -- Step 2: Apply mp_ratio for effective inputs
  have h_mp := @mp_ratio 1 α ρ (A_K * K) (A_L * L) one_pos hα hα1 _hρ hAKK hALL
  rw [h_mp]
  -- Goal: A_K/A_L * ((α/(1-α)) * ((A_K*K)/(A_L*L))^{ρ-1}) = relativeWageDTC ...
  simp only [relativeWageDTC]
  -- Step 3: Decompose (A_K*K)/(A_L*L) = (A_K/A_L) * (K/L)
  rw [mul_div_mul_comm A_K K A_L L]
  -- Step 4: Distribute rpow over product
  rw [mul_rpow (le_of_lt (div_pos hAK hAL)) (le_of_lt (div_pos hK hL))]
  -- Step 5: Rearrange and combine A_K/A_L * (A_K/A_L)^{ρ-1} = (A_K/A_L)^ρ
  rw [show A_K / A_L * (α / (1 - α) * ((A_K / A_L) ^ (ρ - 1) * (K / L) ^ (ρ - 1))) =
      α / (1 - α) * (A_K / A_L * (A_K / A_L) ^ (ρ - 1)) * (K / L) ^ (ρ - 1) from by ring]
  rw [rpow_succ_pred (div_pos hAK hAL) ρ]

/-- The relative wage under DTC is positive. -/
theorem relativeWage_pos {α ρ A_K K A_L L : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (hAK : 0 < A_K) (hAL : 0 < A_L) (hK : 0 < K) (hL : 0 < L) :
    0 < relativeWageDTC α ρ A_K K A_L L := by
  simp only [relativeWageDTC]
  apply mul_pos
  · apply mul_pos
    · exact div_pos hα (by linarith)
    · exact rpow_pos_of_pos (div_pos hAK hAL) ρ
  · exact rpow_pos_of_pos (div_pos hK hL) (ρ - 1)

-- ============================================================
-- Section 5: DTC Equilibrium Results
-- ============================================================

/-- **DTC Premium Exponent (Acemoglu 2002, Proposition 1)**:
    Under the DTC equilibrium condition A_K/A_L = (K/L)^{σ-1},
    the relative factor price simplifies to:
    MPK/MPL = (α/(1-α)) · (K/L)^{σ-2}.

    The exponent (σ-1)ρ + (ρ-1) = σ-2 is the key algebraic identity.
    This means all technology terms cancel, and only the net effect
    of factor supply on relative prices remains. -/
theorem dtcPremium_exponent {α ρ σ A_K K A_L L : ℝ}
    (_hα : 0 < α) (_hα1 : α < 1) (hρ1 : ρ ≠ 1)
    (hK : 0 < K) (hL : 0 < L)
    (hσ : σ = 1 / (1 - ρ))
    (hbias : A_K / A_L = (K / L) ^ (σ - 1)) :
    relativeWageDTC α ρ A_K K A_L L = (α / (1 - α)) * (K / L) ^ (σ - 2) := by
  simp only [relativeWageDTC]
  -- Substitute the bias condition A_K/A_L = (K/L)^{σ-1}
  rw [hbias]
  -- Combine ((K/L)^{σ-1})^ρ into (K/L)^{(σ-1)·ρ}
  rw [← rpow_mul (le_of_lt (div_pos hK hL))]
  -- Reassociate to combine rpow terms
  rw [mul_assoc, ← rpow_add (div_pos hK hL)]
  -- Reduce exponent identity: (σ-1)·ρ + (ρ-1) = σ-2
  congr 1; congr 1
  subst hσ
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  field_simp
  ring

/-- **σ = 2 threshold**: At σ = 2 (ρ = 1/2), the relative wage equals
    α/(1-α), independent of factor supplies K/L.
    This is the knife-edge case where price and market size effects exactly cancel.

    **Proof.** Under directed technical change, $\mathrm{MPK}/\mathrm{MPL} = (\alpha/(1-\alpha))\cdot(K/L)^{\sigma-2}$. At $\sigma = 2$ the exponent $\sigma - 2 = 0$, so $(K/L)^0 = 1$ and the ratio reduces to $\alpha/(1-\alpha)$. -/
theorem dtcPremium_threshold_sigma_2 {α K L : ℝ}
    (_hK : 0 < K) (_hL : 0 < L) :
    (α / (1 - α)) * (K / L) ^ ((2 : ℝ) - 2) = α / (1 - α) := by
  rw [show (2 : ℝ) - 2 = 0 from by ring]
  simp [rpow_zero]

/-- **Complement regime (σ < 2)**: When the elasticity of substitution is
    below 2, increasing relative factor supply K/L *decreases* its
    relative price MPK/MPL (price effect dominates market size effect).
    This is the empirically relevant regime (σ̂ ≈ 1.27 for US). -/
theorem dtcPremium_complement_regime {α σ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hσ : σ < 2)
    {K₁ K₂ L : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hL : 0 < L)
    (hK : K₁ < K₂) :
    (α / (1 - α)) * (K₂ / L) ^ (σ - 2) <
    (α / (1 - α)) * (K₁ / L) ^ (σ - 2) := by
  have hα_rat : 0 < α / (1 - α) := div_pos hα (by linarith)
  apply mul_lt_mul_of_pos_left _ hα_rat
  have hσ2 : σ - 2 < 0 := by linarith
  exact (Real.rpow_lt_rpow_iff_of_neg (div_pos hK₂ hL) (div_pos hK₁ hL) hσ2).mpr
    (div_lt_div_of_pos_right hK hL)

/-- **Strong substitute regime (σ > 2)**: When σ > 2, increasing relative
    factor supply K/L *increases* its relative price MPK/MPL.
    The market size effect dominates: more K induces so much K-augmenting
    innovation that K's price actually rises. Paradoxical but empirically rare. -/
theorem dtcPremium_strong_substitute_regime {α σ : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hσ : 2 < σ)
    {K₁ K₂ L : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hL : 0 < L)
    (hK : K₁ < K₂) :
    (α / (1 - α)) * (K₁ / L) ^ (σ - 2) <
    (α / (1 - α)) * (K₂ / L) ^ (σ - 2) := by
  have hα_rat : 0 < α / (1 - α) := div_pos hα (by linarith)
  apply mul_lt_mul_of_pos_left _ hα_rat
  have hσ2 : 0 < σ - 2 := by linarith
  exact rpow_lt_rpow (le_of_lt (div_pos hK₁ hL))
    (div_lt_div_of_pos_right hK hL) hσ2

-- ============================================================
-- Section 6: Factor Shares under Factor Augmentation
-- ============================================================

/-- Capital share under factor augmentation equals capitalShare
    applied to effective inputs. -/
theorem capitalShare_factorAugmented {α ρ A_K K A_L L : ℝ} :
    capitalShare α ρ (A_K * K) (A_L * L) =
    α * (A_K * K) ^ ρ / factorAugmentedInner α ρ A_K K A_L L := rfl

/-- Labor share under factor augmentation equals laborShare
    applied to effective inputs. -/
theorem laborShare_factorAugmented {α ρ A_K K A_L L : ℝ} :
    laborShare α ρ (A_K * K) (A_L * L) =
    (1 - α) * (A_L * L) ^ ρ / factorAugmentedInner α ρ A_K K A_L L := rfl

/-- Factor shares sum to one under factor augmentation. -/
theorem shares_sum_one_factorAugmented {α ρ A_K K A_L L : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (hAK : 0 < A_K) (hK : 0 < K) (hAL : 0 < A_L) (hL : 0 < L) :
    capitalShare α ρ (A_K * K) (A_L * L) +
    laborShare α ρ (A_K * K) (A_L * L) = 1 :=
  capitalShare_plus_laborShare (ρ := ρ) hα hα1 (mul_pos hAK hK) (mul_pos hAL hL)

/-- **Factor share identity with technology terms**: The log ratio of
    factor shares equals ρ times the log ratio of effective inputs.

    log(s_L/s_K) = log((1-α)/α) + ρ · log(A_L·L / (A_K·K))

    This extends the standard factorShare_identity to include
    factor-augmenting technology terms. The key estimation equation
    when technology differences are observable. -/
theorem factorShare_identity_augmented {α ρ A_K K A_L L : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (hAK : 0 < A_K) (hK : 0 < K) (hAL : 0 < A_L) (hL : 0 < L) :
    Real.log (laborShare α ρ (A_K * K) (A_L * L) /
              capitalShare α ρ (A_K * K) (A_L * L)) =
    Real.log ((1 - α) / α) + ρ * Real.log (A_L * L / (A_K * K)) :=
  factorShare_identity hα hα1 (mul_pos hAK hK) (mul_pos hAL hL)

-- ============================================================
-- Section 7: Direction of Technical Change Bias
-- ============================================================

/-- When σ > 1 (substitutes), the equilibrium technology bias (K/L)^{σ-1}
    is *increasing* in K/L: innovation is directed toward the abundant factor.
    More capital → more capital-augmenting R&D. -/
theorem dtc_bias_increases_with_supply_substitute {σ : ℝ} (hσ : 1 < σ)
    {K₁ K₂ L : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hL : 0 < L)
    (hK : K₁ < K₂) :
    dtcEquilibriumBias σ (K₁ / L) < dtcEquilibriumBias σ (K₂ / L) := by
  simp only [dtcEquilibriumBias]
  exact rpow_lt_rpow (le_of_lt (div_pos hK₁ hL))
    (div_lt_div_of_pos_right hK hL) (by linarith)

/-- When σ < 1 (complements), the equilibrium technology bias (K/L)^{σ-1}
    is *decreasing* in K/L: innovation is directed toward the scarce factor.
    More capital → more labor-augmenting R&D. -/
theorem dtc_bias_decreases_with_supply_complement {σ : ℝ} (hσ : σ < 1)
    {K₁ K₂ L : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂) (hL : 0 < L)
    (hK : K₁ < K₂) :
    dtcEquilibriumBias σ (K₂ / L) < dtcEquilibriumBias σ (K₁ / L) := by
  simp only [dtcEquilibriumBias]
  exact (Real.rpow_lt_rpow_iff_of_neg (div_pos hK₂ hL) (div_pos hK₁ hL) (by linarith)).mpr
    (div_lt_div_of_pos_right hK hL)

/-- At σ = 1 (Cobb-Douglas), the technology bias is 1 regardless of K/L:
    innovation has no preferred direction.

    **Proof.** The equilibrium bias $(K/L)^{\sigma-1}$ has exponent $\sigma - 1 = 0$ when $\sigma = 1$, so $(K/L)^0 = 1$ for all positive $K/L$. -/
theorem dtc_bias_invariant_cobbDouglas {K L : ℝ} (_hK : 0 < K) (_hL : 0 < L) :
    dtcEquilibriumBias 1 (K / L) = 1 := by
  simp only [dtcEquilibriumBias]
  rw [show (1 : ℝ) - 1 = 0 from by ring]
  exact rpow_zero _

-- ============================================================
-- Section 8: Summary Statistics
-- ============================================================

-- Total count: 7 definitions, 18 theorems.
-- Fully proved: 18. Sorry: 0. Axioms: 0.
--
-- Definitions:
--   factorAugmentedInner, factorAugmentedCES, mpkFactorAugmented,
--   mplFactorAugmented, relativeWageDTC, dtcEquilibriumBias, skillPremiumExponent
--
-- Key results:
--   factorAugmentedCES_crs: CRS under factor augmentation
--   euler_factorAugmented: Euler's exhaustion theorem
--   relativeWage_formula: MPK/MPL = (α/(1-α))·(A_K/A_L)^ρ·(K/L)^{ρ-1}
--   dtcPremium_exponent: Under DTC, MPK/MPL = (α/(1-α))·(K/L)^{σ-2}
--   dtcPremium_threshold_sigma_2: At σ=2, relative wage independent of K/L
--   dtcPremium_complement_regime: σ<2 → price effect dominates
--   dtcPremium_strong_substitute_regime: σ>2 → market size dominates
--   factorShare_identity_augmented: log(s_L/s_K) with technology terms
--   dtc_bias_increases_with_supply_substitute: σ>1 → bias toward abundant factor
--   dtc_bias_decreases_with_supply_complement: σ<1 → bias toward scarce factor
--   dtc_bias_invariant_cobbDouglas: σ=1 → no bias

end
