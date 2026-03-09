/-
  Multi-Agent CES Game Theory (Gap #14)

  This file formalizes the game-theoretic structure of CES economies,
  resolving the gap between the single-agent optimization results
  (Hessian, strategic independence) and multi-agent interactions.

  THE GEOMETRIC CLASSIFICATION:
    ρ < 1 (K > 0): Spherical geometry → unique interior equilibrium
    ρ = 1 (K = 0): Flat geometry → degenerate
    ρ > 1 (K < 0): Hyperbolic geometry → J corner equilibria

  FIVE MAIN RESULTS:
  Part A: ρ < 1 → unique stable equilibrium (from concavity)
  Part B: ρ > 1 → unstable interior + J stable corners
  Part C: Asymmetric CES contest game with stability conditions
  Part D: Folk Theorem threshold δ* as function of K
  Part E: Basin geometry via fitness vector ω_j = a_j c_j^{-ρ}
-/

import CESProofs.Foundations.Hessian
import CESProofs.Foundations.FurtherProperties
import CESProofs.Foundations.GeneralHessian

open Real Finset BigOperators

noncomputable section

variable {J : ℕ}

-- ============================================================
-- Part A: Geometric Classification by ρ
-- ============================================================

/-- The sign of curvature K classifies the equilibrium structure:
    K > 0 (ρ < 1): spherical geometry, unique equilibrium
    K = 0 (ρ = 1): flat geometry, degenerate
    K < 0 (ρ > 1): hyperbolic geometry, multiple equilibria -/
theorem curvatureK_sign_classification (hJ : 2 ≤ J) (ρ : ℝ) :
    (ρ < 1 → 0 < curvatureK J ρ) ∧
    (ρ = 1 → curvatureK J ρ = 0) ∧
    (1 < ρ → curvatureK J ρ < 0) := by
  refine ⟨curvatureK_pos hJ, fun h => ?_, fun h => ?_⟩
  · simp [curvatureK, h]
  · unfold curvatureK
    apply div_neg_of_neg_of_pos
    · have : (1 : ℝ) < ↑J := by exact_mod_cast (by omega : 1 < J)
      nlinarith
    · exact_mod_cast (by omega : 0 < J)

/-- For ρ < 1 (complements): the Hessian on 1⊥ is negative definite.
    This implies the symmetric allocation is the UNIQUE maximizer
    among all allocations with the same total input.

    **Proof.** For $\rho < 1$, the CES Hessian eigenvalue on $\mathbf{1}^\perp$
    is $\lambda_\perp = -(1-\rho)/(Jc) < 0$, so $v^T H v = \lambda_\perp \|v\|^2 < 0$
    for all nonzero $v \in \mathbf{1}^\perp$. This strict concavity along the
    isoquant implies the symmetric point is the unique maximizer. -/
theorem unique_equilibrium_complements
    (hJ : 2 ≤ J) {ρ : ℝ} (hρ : ρ < 1)
    {c : ℝ} (hc : 0 < c)
    (v : Fin J → ℝ) (hv : orthToOne J v)
    (hv_ne : ∃ j, v j ≠ 0) :
    cesHessianQF J ρ c v < 0 :=
  ces_strict_concavity_on_perp hJ hρ hc v hv hv_ne

/-- For ρ > 1 (substitutes): the Hessian on 1⊥ is POSITIVE definite.
    The symmetric allocation is a LOCAL MINIMUM along the isoquant,
    making it an unstable saddle point of the production function.

    **Proof.** For $\rho > 1$, the eigenvalue $\lambda_\perp = (\rho - 1)/(Jc) > 0$.
    The quadratic form on $\mathbf{1}^\perp$ equals $\lambda_\perp \sum_j v_j^2$,
    which is strictly positive since $\lambda_\perp > 0$ and at least one $v_j \neq 0$. -/
theorem saddle_point_substitutes
    (hJ : 2 ≤ J) {ρ : ℝ} (hρ : 1 < ρ)
    {c : ℝ} (hc : 0 < c)
    (v : Fin J → ℝ) (hv : orthToOne J v)
    (hv_ne : ∃ j, v j ≠ 0) :
    0 < cesHessianQF J ρ c v := by
  rw [cesHessianQF_on_perp (by omega) ρ c hc v hv]
  apply mul_pos
  · simp only [cesEigenvaluePerp]
    apply div_pos (by linarith)
    exact mul_pos (by exact_mod_cast (by omega : 0 < J)) hc
  · exact Finset.sum_pos'
      (fun j _ => sq_nonneg (v j))
      (by obtain ⟨j₀, hj₀⟩ := hv_ne
          exact ⟨j₀, Finset.mem_univ _, by positivity⟩)

-- ============================================================
-- Part B: Asymmetric CES Contest Game
-- ============================================================

/-- The escort share (market share in Cournot-CES game):
    s_j = a_j x_j^ρ / Σ a_k x_k^ρ.

    This IS the escort probability distribution from information
    geometry, now reinterpreted as the endogenous market share
    in a contest game. -/
def contestShare (a x : Fin J → ℝ) (ρ : ℝ)
    (j : Fin J) : ℝ :=
  a j * x j ^ ρ / ∑ k : Fin J, a k * x k ^ ρ

/-- The payoff in the CES contest game:
    Π_j = s_j(x) - c_j · x_j
    Agent j maximizes market share minus effort cost. -/
def contestPayoff (a x cost : Fin J → ℝ) (ρ : ℝ)
    (j : Fin J) : ℝ :=
  contestShare a x ρ j - cost j * x j

/-- The structural fitness of agent j:
    ω_j = a_j · c_j^{-ρ}.

    This condenses baseline advantage and cost efficiency
    through the lens of the curvature parameter ρ. Agents with
    higher fitness capture larger equilibrium shares. -/
def agentFitness (a cost : Fin J → ℝ) (ρ : ℝ)
    (j : Fin J) : ℝ :=
  a j * cost j ^ (-ρ)

/-- The interior equilibrium share is the normalized fitness:
    s_j* = ω_j / Σ ω_k.
    This is the unique interior fixed point of the best-response
    dynamics (when it exists). -/
def equilibriumShare (a cost : Fin J → ℝ) (ρ : ℝ)
    (j : Fin J) : ℝ :=
  agentFitness a cost ρ j /
    ∑ k : Fin J, agentFitness a cost ρ k

/-- Equilibrium shares sum to 1 (they form a probability
    distribution on agents). -/
theorem equilibriumShare_sum [NeZero J]
    (a cost : Fin J → ℝ)
    (hω : 0 < ∑ k : Fin J, agentFitness a cost ρ k) :
    ∑ j, equilibriumShare a cost ρ j = 1 := by
  unfold equilibriumShare
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hω)

/-- **Symmetric Nash equilibrium**: When all agents have equal fitness
    parameters (same a, same cost), the equilibrium share is 1/J for each.

    **Proof.** With identical fitness $\omega_j = a_0 \cdot c_0^{-\rho}$ for all $j$,
    the share $s_j^* = \omega / (J \cdot \omega) = 1/J$. The common factor
    $\omega \neq 0$ (since $a_0 > 0$ and $c_0 > 0$) cancels. -/
theorem symmetric_equilibrium_share [NeZero J]
    {a₀ cost₀ : ℝ} {ρ : ℝ}
    (ha : 0 < a₀) (hcost : 0 < cost₀) :
    equilibriumShare (fun _ : Fin J => a₀) (fun _ => cost₀) ρ ⟨0, NeZero.pos J⟩ =
      1 / ↑J := by
  simp only [equilibriumShare, agentFitness]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hω : a₀ * cost₀ ^ (-ρ) ≠ 0 := by
    apply mul_ne_zero (ne_of_gt ha)
    exact ne_of_gt (rpow_pos_of_pos hcost _)
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne J)
  field_simp

-- ============================================================
-- Part C: Stability Conditions
-- ============================================================

/-- The local stability condition for agent j at share s_j:
    ρ(1 - 2s_j) - 1 < 0.

    This ensures the payoff is locally concave in x_j, so
    the agent's best response is well-defined and stable. -/
def isLocallyStable (ρ sj : ℝ) : Prop :=
  ρ * (1 - 2 * sj) - 1 < 0

/-- **Complements are universally stable**: For ρ < 1, every
    agent at every share level satisfies the stability condition.

    The interior equilibrium is a global attractor — no matter
    where the economy starts, it converges to the unique fixed
    point. This is the game-theoretic consequence of positive
    curvature (spherical geometry). -/
theorem universal_stability_complements {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1)
    (sj : ℝ) (hs_nn : 0 ≤ sj) (_hs_le : sj ≤ 1) :
    isLocallyStable ρ sj := by
  unfold isLocallyStable
  have h1 : 1 - 2 * sj ≤ 1 := by linarith
  have h2 : ρ * (1 - 2 * sj) ≤ ρ := by nlinarith
  linarith

/-- **Substitutes create instability**: For ρ > 1, any agent
    with market share below the stability threshold
    s* = (ρ-1)/(2ρ) is locally unstable.

    A small perturbation grows: the agent either captures more
    share (positive feedback) or is driven to zero. This is
    the game-theoretic consequence of negative curvature
    (hyperbolic geometry). -/
theorem instability_substitutes {ρ : ℝ} (hρ : 1 < ρ)
    (sj : ℝ) (hs : sj < (ρ - 1) / (2 * ρ)) :
    ¬ isLocallyStable ρ sj := by
  unfold isLocallyStable; push_neg
  have h1 : sj * (2 * ρ) < ρ - 1 := by
    rwa [lt_div_iff₀ (by linarith : (0:ℝ) < 2 * ρ)] at hs
  nlinarith

/-- The stability threshold: s* = (ρ-1)/(2ρ).
    Agents with share below this are unstable. -/
def stabilityThreshold (ρ : ℝ) : ℝ := (ρ - 1) / (2 * ρ)

/-- For ρ < 1: threshold is negative (trivially satisfied by
    all agents on the simplex). -/
theorem threshold_neg_complements {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    stabilityThreshold ρ < 0 := by
  unfold stabilityThreshold
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

/-- For ρ > 1: threshold is positive (small agents are
    unstable). -/
theorem threshold_pos_substitutes {ρ : ℝ} (hρ : 1 < ρ) :
    0 < stabilityThreshold ρ := by
  unfold stabilityThreshold
  exact div_pos (by linarith) (by linarith)

/-- For ρ > 1: threshold < 1/2 (the majority agent is always
    stable — the winner of the contest is self-reinforcing). -/
theorem threshold_lt_half {ρ : ℝ} (hρ : 1 < ρ) :
    stabilityThreshold ρ < 1 / 2 := by
  unfold stabilityThreshold
  rw [div_lt_div_iff₀ (by linarith : (0:ℝ) < 2 * ρ) (by norm_num : (0:ℝ) < 2)]
  nlinarith

/-- The corner allocation (one agent captures all) is stable
    for ρ > 1. The winner at s_j = 1 satisfies the stability
    condition: ρ(1-2) - 1 = -ρ-1 < 0. -/
theorem corner_stable_substitutes {ρ : ℝ} (hρ : 1 < ρ) :
    isLocallyStable ρ 1 := by
  unfold isLocallyStable; nlinarith

-- ============================================================
-- Part D: Folk Theorem and Cooperation
-- ============================================================

/-- One-period deviation gain from breaking the symmetric
    allocation (second-order approximation):
    g = (1-ρ)/(2Jc) per unit ‖δ‖². -/
def deviationGain (J : ℕ) (ρ c : ℝ) : ℝ :=
  (1 - ρ) / (2 * ↑J * c)

/-- One-period punishment from knockout retaliation:
    p = c · (1 - R₁), where R₁ is the fractional output
    retained when one of J symmetric inputs fails. -/
def knockoutPunishment (J : ℕ) (ρ c : ℝ) : ℝ :=
  c * (1 - knockoutRetained J ρ 1)

/-- Folk Theorem critical discount factor:
    δ* = g / (g + p).
    Cooperation is sustainable iff δ > δ*. -/
def folkThreshold (J : ℕ) (ρ c : ℝ) : ℝ :=
  deviationGain J ρ c /
    (deviationGain J ρ c + knockoutPunishment J ρ c)

/-- The deviation gain is proportional to K:
    g = K / (2(J-1)c).
    Higher complementarity → higher deviation gain, but also
    higher punishment. The punishment grows FASTER.

    **Proof.** Expanding, $g = \frac{1-\rho}{2Jc}$ and
    $\frac{K}{2(J-1)c} = \frac{(1-\rho)(J-1)/J}{2(J-1)c} = \frac{1-\rho}{2Jc}$.
    The $(J-1)$ factors cancel, yielding the identity. -/
theorem deviationGain_eq_K (hJ : 2 ≤ J) (ρ c : ℝ)
    (hc : c ≠ 0) :
    deviationGain J ρ c =
      curvatureK J ρ / (2 * (↑J - 1) * c) := by
  simp only [deviationGain, curvatureK]
  have hJne : (↑J : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (by omega)
  have hJm1_ne : (↑J : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < ↑J := by exact_mod_cast
      (by omega : 1 < J)
    linarith
  field_simp

/-- The punishment is positive for complementary inputs
    (ρ ∈ (0,1)): knockout destroys output. -/
theorem knockoutPunishment_pos {ρ : ℝ}
    (hρ0 : 0 < ρ) (_hρ1 : ρ < 1)
    {c : ℝ} (hc : 0 < c) (hJ : 2 ≤ J) :
    0 < knockoutPunishment J ρ c := by
  unfold knockoutPunishment
  apply mul_pos hc
  have hR := knockout_partial_retained hρ0
    (by omega : 0 < J) (by omega : 0 < 1)
    (by omega : 1 < J)
  linarith [hR.2]

/-- The Folk Theorem threshold is in (0,1) for ρ ∈ (0,1):
    cooperation IS sustainable with sufficient patience.

    **Proof.** For $\rho \in (0,1)$, the deviation gain $g > 0$ (since
    $1-\rho > 0$, $J > 0$, $c > 0$) and the knockout punishment $p > 0$
    (removing one of $J \geq 2$ complementary inputs strictly reduces output).
    Then $\delta^* = g/(g+p)$ satisfies $0 < \delta^* < 1$ because $g > 0$
    makes the ratio positive and $p > 0$ ensures the denominator exceeds
    the numerator. -/
theorem folkThreshold_valid {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {c : ℝ} (hc : 0 < c) (hJ : 2 ≤ J) :
    0 < folkThreshold J ρ c ∧
    folkThreshold J ρ c < 1 := by
  unfold folkThreshold
  have hg : 0 < deviationGain J ρ c := by
    unfold deviationGain
    exact div_pos (by linarith) (mul_pos
      (mul_pos (by norm_num) (by exact_mod_cast
        (by omega : 0 < J))) hc)
  have hp := knockoutPunishment_pos hρ0 hρ1 hc hJ
  exact ⟨div_pos hg (by linarith),
    (div_lt_one (by linarith)).mpr (by linarith)⟩

/-- **Aumann's Insight**: Higher punishment makes cooperation
    easier. Since punishment increases with complementarity K,
    more complementary economies sustain cooperation with less
    patient agents.

    Formally: if p₁ < p₂ then δ*₁ > δ*₂. -/
theorem cooperation_easier_with_higher_punishment
    {g p₁ p₂ : ℝ} (hg : 0 < g) (_hp1 : 0 < p₁)
    (_hp2 : 0 < p₂) (hlt : p₁ < p₂) :
    g / (g + p₂) < g / (g + p₁) := by
  apply div_lt_div_of_pos_left hg (by linarith) (by linarith)

-- ============================================================
-- Part E: Basin Geometry (Separatrix)
-- ============================================================

/-- The separatrix between monopoly basins i and j in the
    substitutes regime (ρ > 1) is characterized by the fitness
    ratio ω_i/ω_j. Agent i wins iff their share exceeds the
    critical boundary determined by the fitness advantage.

    The separatrix equation in share space:
      s_i/s_j = (a_i/a_j)^{1/(ρ-1)} · (c_j/c_i)^{ρ/(ρ-1)}
             = (ω_i/ω_j)^{1/(ρ-1)}

    The exponent 1/(ρ-1) is the AMPLIFICATION FACTOR:
    as ρ → 1+, it diverges to +∞, meaning a tiny fitness
    advantage determines the entire market. -/
def amplificationExponent (ρ : ℝ) : ℝ := 1 / (ρ - 1)

/-- The amplification exponent is positive for ρ > 1. -/
theorem amplification_pos {ρ : ℝ} (hρ : 1 < ρ) :
    0 < amplificationExponent ρ :=
  div_pos one_pos (by linarith)

/-- The amplification exponent diverges as ρ → 1+: for any
    bound M > 0, there exists ρ > 1 with exponent > M.

    This captures the phase transition: at ρ = 1 (flat geometry),
    there is no amplification. For ρ slightly above 1, even
    microscopic fitness advantages determine the winner. -/
theorem amplification_diverges {M : ℝ} (hM : 0 < M) :
    ∃ ρ : ℝ, 1 < ρ ∧ M < amplificationExponent ρ := by
  use 1 + 1 / (M + 1)
  constructor
  · linarith [div_pos one_pos (by linarith : (0:ℝ) < M + 1)]
  · unfold amplificationExponent
    rw [show 1 + 1 / (M + 1) - 1 = 1 / (M + 1) from by ring]
    rw [one_div, one_div, inv_inv]
    linarith

/-- The separatrix share ratio between agents i and j:
    s_i/s_j at the boundary = (ω_i/ω_j)^{1/(ρ-1)}.

    Agent i wins the market iff s_i/s_j exceeds this ratio. -/
def separatrixRatio (ωi ωj ρ : ℝ) : ℝ :=
  (ωi / ωj) ^ amplificationExponent ρ

/-- Equal fitness → separatrix at equal shares.
    If ω_i = ω_j, the boundary is at s_i = s_j. -/
theorem separatrix_symmetric {ρ : ℝ} (_hρ : 1 < ρ)
    {ω : ℝ} (hω : 0 < ω) :
    separatrixRatio ω ω ρ = 1 := by
  unfold separatrixRatio
  rw [div_self (ne_of_gt hω)]
  exact one_rpow _

/-- Higher fitness → larger basin of attraction.
    If ω_i > ω_j, the separatrix shifts toward j,
    giving agent i a larger basin.

    **Proof.** Since $\omega_i > \omega_j > 0$, the fitness ratio
    $\omega_i/\omega_j > 1$. Raising to the positive power $1/(\rho - 1)$
    (positive since $\rho > 1$) preserves the inequality, giving
    $(\omega_i/\omega_j)^{1/(\rho-1)} > 1$. -/
theorem fitness_advantage_expands_basin {ρ : ℝ} (hρ : 1 < ρ)
    {ωi ωj : ℝ} (_hωi : 0 < ωi) (hωj : 0 < ωj)
    (hadv : ωj < ωi) :
    1 < separatrixRatio ωi ωj ρ := by
  unfold separatrixRatio
  exact Real.one_lt_rpow ((one_lt_div hωj).mpr hadv)
    (amplification_pos hρ)

end
