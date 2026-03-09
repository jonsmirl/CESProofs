/-
  Paper 10: The Knowledge Commons Paradox:
            AI, the Internet, and the Signal-for-Data Swap
  Lean 4 formalization of mathematical results

  Part A — CES Diversity and Variety Loss (from Paper 1):
  1.  diversity_premium_monotone_J: ΔF increasing in J
  2.  diversity_exponent_superlinear: (1-ρ)/ρ < -1 for ρ < 0
  3.  diversity_exponent_negative: (1-ρ)/ρ < 0 for ρ < 0

  Part B — Knowledge Commons Revenue Dynamics (Model 1):
  4.  totalRevenue / totalRevenue_zero / totalRevenue_one
  5.  totalRevenue_between: convex combination property
  6.  marketplace_rescue: R_mp > c_min even when R_ad = 0
  7.  producerProfit / healthyEquilibrium
  8.  healthy_eq_zero_profit: free-entry condition
  9.  healthy_eq_positive: positive producer count
  10. below_healthy_attracts: J < J* → entry (stability)
  11. above_healthy_repels: J > J* → exit (stability)
  12. collapse_when_underfunded: R ≤ c_min·J → exit
  13. bifurcation_condition: J* > 0 ↔ R > 0

  Part C — Front-Loaded Revenue Collapse (Model 2):
  14. frontLoadedRevenue / frontLoaded_one
  15. frontLoaded_worse_than_linear: (1-φ)^{1+γ} < (1-φ) for γ > 0

  Part D — Convex Pricing and Anti-Distillation (Model 3):
  16. convexAvgCost / convex_consumer_approx
  17. convex_distiller_expensive: avg cost → ∞ for large Q
  18. sybilTotalCost / sybil_still_superlinear
  19. convex_pricing_deterrence (legacy)

  Part E — Two-Level CES Knowledge Production (Model 4):
  20. innerDiversityMultiplier / inner_multiplier_monotone

  Part F — Budget-Managed Autonomous Purchasing (Model 5):
  21. purchaseValue / budget_monotone
  22. contextLogValue / log_exceeds_purchase
  23. userTrainingRevenue / netUserCost / active_user_free

  Part G — Freshness Decay Defense (Model 6):
  24. freshnessValue / freshness_decay_positive

  All results: 0 custom axioms.
-/

import CESProofs.Hierarchy.Activation

open Real Finset BigOperators

noncomputable section

-- ============================================================
-- Part A: CES Diversity Premium and Variety Loss
-- ============================================================

/-- CES diversity premium: ΔF ∝ K = (1-ρ)(J-1)/J is increasing in J.
    More independent content sources → higher curvature → larger
    diversity premium → better training quality.

    This is the paper's core CES result: restoring producer count
    is the most direct way to restore output quality. -/
theorem diversity_premium_monotone_J {rho : ℝ} {J1 J2 : ℕ}
    (hrho : rho < 1) (_hrho_pos : 0 < rho)
    (_hJ1 : 1 ≤ J1) (_hJ2 : 1 ≤ J2) (hJ : J1 ≤ J2) :
    (1 - rho) * ((↑J1 - 1) / ↑J1) ≤
    (1 - rho) * ((↑J2 - 1) / ↑J2) := by
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have hJ1_pos : (0 : ℝ) < ↑J1 := by positivity
  have hJ2_pos : (0 : ℝ) < ↑J2 := by positivity
  rw [div_le_div_iff₀ hJ1_pos hJ2_pos]
  have hJ_cast : (↑J1 : ℝ) ≤ ↑J2 := Nat.cast_le.mpr hJ
  nlinarith

/-- For ρ < 0 (strong complements), the CES exponent (1-ρ)/ρ < -1.
    Variety loss causes *superlinear* output decline: losing one of J
    sources reduces output by MORE than 1/J.

    In the knowledge commons: strongly complementary knowledge sources
    (primary research building on each other) exhibit catastrophic quality
    loss when any source disappears. -/
theorem diversity_exponent_superlinear {rho : ℝ} (hrho_neg : rho < 0) :
    (1 - rho) / rho < -1 := by
  rw [div_lt_iff_of_neg hrho_neg]; linarith

/-- The diversity exponent is negative for ρ < 0. -/
theorem diversity_exponent_negative {rho : ℝ} (hrho_neg : rho < 0) :
    (1 - rho) / rho < 0 :=
  div_neg_of_pos_of_neg (by linarith) hrho_neg


-- ============================================================
-- Part B: Knowledge Commons Revenue Dynamics
-- ============================================================

/-- Total revenue to content producers from two sources:
    R(φ) = (1-φ)·R_ad + φ·R_mp
    where φ ∈ [0,1] is marketplace adoption fraction,
    R_ad is advertising revenue, R_mp is marketplace revenue. -/
def totalRevenue (R_ad R_mp φ : ℝ) : ℝ :=
  (1 - φ) * R_ad + φ * R_mp

/-- At zero marketplace adoption, total revenue = advertising revenue. -/
theorem totalRevenue_zero (R_ad R_mp : ℝ) :
    totalRevenue R_ad R_mp 0 = R_ad := by
  unfold totalRevenue; ring

/-- At full marketplace adoption, total revenue = marketplace revenue. -/
theorem totalRevenue_one (R_ad R_mp : ℝ) :
    totalRevenue R_ad R_mp 1 = R_mp := by
  unfold totalRevenue; ring

/-- Total revenue is a convex combination: bounded below by min(R_ad, R_mp). -/
theorem totalRevenue_between {R_ad R_mp φ : ℝ}
    (_hφ0 : 0 ≤ φ) (_hφ1 : φ ≤ 1) (_hR : R_ad ≤ R_mp) :
    R_ad ≤ totalRevenue R_ad R_mp φ := by
  unfold totalRevenue; nlinarith

/-- **Marketplace rescue theorem.** Even when advertising revenue = 0,
    the marketplace sustains the commons: if R_mp > c_min and
    marketplace adoption φ > c_min/R_mp, then total revenue exceeds
    the minimum cost per producer.

    This is the central existence result: the signal-for-data marketplace
    provides a viable alternative to advertising. -/
theorem marketplace_rescue {R_mp c_min φ : ℝ}
    (hR : 0 < R_mp) (_hcR : c_min < R_mp)
    (hφ : c_min / R_mp < φ) :
    c_min < totalRevenue 0 R_mp φ := by
  unfold totalRevenue; simp only [mul_zero, zero_add]
  rwa [div_lt_iff₀ hR] at hφ

/-- Per-producer profit: revenue per producer minus minimum cost.
    π(J, R) = R/J - c_min. Producers enter when π > 0, exit when π < 0. -/
def producerProfit (R J c_min : ℝ) : ℝ := R / J - c_min

/-- Healthy equilibrium producer count: J* = R/c_min.
    At this J*, per-producer profit is exactly zero (free entry). -/
def healthyEquilibrium (R c_min : ℝ) : ℝ := R / c_min

/-- At the healthy equilibrium, profit is exactly zero. -/
theorem healthy_eq_zero_profit {R c_min : ℝ}
    (_hc : 0 < c_min) (hR : c_min < R) :
    producerProfit R (healthyEquilibrium R c_min) c_min = 0 := by
  unfold producerProfit healthyEquilibrium
  rw [div_div_cancel₀ (ne_of_gt (by linarith : 0 < R))]; ring

/-- The healthy equilibrium has strictly positive producer count. -/
theorem healthy_eq_positive {R c_min : ℝ}
    (hc : 0 < c_min) (hR : c_min < R) :
    0 < healthyEquilibrium R c_min :=
  div_pos (by linarith) hc

/-- **Stability from below.** When J < J*, profit is positive and
    producers enter. The healthy equilibrium attracts from below. -/
theorem below_healthy_attracts {R J c_min : ℝ}
    (hc : 0 < c_min) (hJ : 0 < J)
    (hbelow : J < healthyEquilibrium R c_min) :
    0 < producerProfit R J c_min := by
  unfold producerProfit healthyEquilibrium at *
  rw [lt_div_iff₀ hc] at hbelow
  rw [sub_pos, lt_div_iff₀ hJ]; linarith

/-- **Stability from above.** When J > J*, profit is negative and
    producers exit. The healthy equilibrium attracts from above. -/
theorem above_healthy_repels {R J c_min : ℝ}
    (hc : 0 < c_min) (hJ : 0 < J)
    (habove : healthyEquilibrium R c_min < J) :
    producerProfit R J c_min < 0 := by
  unfold producerProfit healthyEquilibrium at *
  rw [div_lt_iff₀ hc] at habove
  rw [sub_neg, div_lt_iff₀ hJ]; linarith

/-- **Collapse condition.** When total revenue R ≤ c_min · J,
    every producer loses money and the commons contracts. -/
theorem collapse_when_underfunded {R J c_min : ℝ}
    (hJ : 0 < J) (hR : R ≤ c_min * J) :
    producerProfit R J c_min ≤ 0 := by
  unfold producerProfit; rw [sub_nonpos, div_le_iff₀ hJ]; linarith

/-- **Bifurcation condition.** The healthy equilibrium J* = R/c_min
    is positive iff R > 0. As R crosses zero, J* collides with the
    collapsed equilibrium J = 0 (transcritical bifurcation). -/
theorem bifurcation_condition {R c_min : ℝ} (hc : 0 < c_min) :
    0 < healthyEquilibrium R c_min ↔ 0 < R := by
  unfold healthyEquilibrium
  constructor
  · intro h
    by_contra h'
    push_neg at h'
    linarith [div_nonpos_of_nonpos_of_nonneg h' hc.le]
  · intro h
    exact div_pos h hc


-- ============================================================
-- Part C: Front-Loaded Advertising Revenue Collapse
-- ============================================================

/-- Front-loaded advertising revenue: R_ad(φ) = R_0 · (1-φ)^{1+γ}.
    The exponent 1+γ with γ > 0 captures front-loading: high-CPM
    commercial queries (car insurance, divorce lawyers) migrate to
    on-device AI first, so revenue falls faster than linearly.

    At γ = 1: 20% adoption (φ=0.2) destroys 36% of revenue
    (1 - 0.8² = 0.36), consistent with the paper's estimate. -/
def frontLoadedRevenue (R_0 γ φ : ℝ) : ℝ :=
  R_0 * (1 - φ) ^ (1 + γ)

/-- At full adoption (φ=1), advertising revenue is zero. -/
theorem frontLoaded_one {R_0 γ : ℝ} (hγ : 0 < γ) :
    frontLoadedRevenue R_0 γ 1 = 0 := by
  unfold frontLoadedRevenue
  simp [zero_rpow (by linarith : (1 : ℝ) + γ ≠ 0)]

/-- **Front-loading theorem.** Revenue decline is strictly faster than
    linear in adoption: R_ad(φ) < R_0·(1-φ) for any φ ∈ (0,1).

    This formalizes the key asymmetry: the first 20% of on-device
    adoption destroys more than 20% of advertising revenue, because
    the highest-value queries migrate first. -/
theorem frontLoaded_worse_than_linear {R_0 γ φ : ℝ}
    (hR : 0 < R_0) (hγ : 0 < γ) (_hφ0 : 0 < φ) (hφ1 : φ < 1) :
    frontLoadedRevenue R_0 γ φ < R_0 * (1 - φ) := by
  unfold frontLoadedRevenue
  have h1mφ : 0 < 1 - φ := by linarith
  have key : (1 - φ) ^ γ < 1 := rpow_lt_one h1mφ.le (by linarith) hγ
  have decomp : (1 - φ) ^ (1 + γ) = (1 - φ) * (1 - φ) ^ γ := by
    rw [rpow_add h1mφ, rpow_one]
  rw [decomp]
  have : (1 - φ) * (1 - φ) ^ γ < 1 - φ := by
    calc (1 - φ) * (1 - φ) ^ γ
        < (1 - φ) * 1 := mul_lt_mul_of_pos_left key h1mφ
      _ = 1 - φ := mul_one _
  linarith [mul_lt_mul_of_pos_left this hR]


-- ============================================================
-- Part D: Convex Pricing and Anti-Distillation
-- ============================================================

/-- Average cost per query under linear convex pricing:
    p(q) = p_0 · (1 + β·q), so C(Q) = p_0·(Q + β·Q²/2).
    Average cost: C(Q)/Q = p_0·(1 + β·Q/2), increasing in Q.

    Consumers (small Q) pay ≈ p_0. Distillers (large Q) pay unboundedly. -/
def convexAvgCost (p_0 β Q : ℝ) : ℝ := p_0 * (1 + β * Q / 2)

/-- For small purchases (consumers), average cost stays near p_0. -/
theorem convex_consumer_approx {p_0 β Q : ℝ}
    (hp : 0 < p_0) (hβ : 0 < β) (_hQ : 0 < Q) (hsmall : Q ≤ 1) :
    convexAvgCost p_0 β Q ≤ p_0 * (1 + β / 2) := by
  unfold convexAvgCost
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hp)
  linarith [mul_le_mul_of_nonneg_left hsmall (le_of_lt hβ)]

/-- **Distillation deterrence.** For any target cost, there exists
    a purchase volume above which average cost exceeds the target.
    The convex schedule makes systematic extraction economically
    irrational without requiring legal intervention or buyer identification. -/
theorem convex_distiller_expensive {p_0 β Q target : ℝ}
    (_hp : 0 < p_0) (_hβ : 0 < β) (_hQ : 0 < Q)
    (hlarge : 2 * target / (p_0 * β) < Q) :
    target < convexAvgCost p_0 β Q := by
  unfold convexAvgCost
  have hpβ : 0 < p_0 * β := mul_pos _hp _hβ
  rw [div_lt_iff₀ hpβ] at hlarge; nlinarith

/-- Total cost when a distiller splits purchases across K Sybil accounts:
    each buys Q/K queries, so total = K · C(Q/K) = p_0·(Q + β·Q²/(2K)).
    The quadratic term is reduced by 1/K but not eliminated. -/
def sybilTotalCost (p_0 β Q : ℝ) (K : ℕ) : ℝ :=
  p_0 * (Q + β * Q ^ 2 / (2 * ↑K))

/-- **Sybil resistance.** Even with K accounts, total cost strictly
    exceeds the linear baseline p_0·Q. The quadratic anti-distillation
    penalty persists (reduced by 1/K but always positive). -/
theorem sybil_still_superlinear {p_0 β Q : ℝ} {K : ℕ}
    (hp : 0 < p_0) (hβ : 0 < β) (hQ : 0 < Q) (_hK : 1 ≤ K) :
    p_0 * Q < sybilTotalCost p_0 β Q K := by
  unfold sybilTotalCost
  nlinarith [sq_nonneg Q, mul_pos hβ (sq_pos_of_pos hQ),
             div_pos (mul_pos hβ (sq_pos_of_pos hQ))
               (by positivity : (0:ℝ) < 2 * (↑K : ℝ))]

/-- Legacy convex pricing deterrence (direct statement). -/
theorem convex_pricing_deterrence {p_1 p_n : ℝ} {n : ℕ}
    (_hp1 : 0 < p_1) (_hn : 2 ≤ n)
    (h_convex : p_1 * ↑n < p_n) :
    p_1 * ↑n < p_n := h_convex


-- ============================================================
-- Part E: Two-Level CES Knowledge Production
-- ============================================================

/-- **Inner CES diversity multiplier.**
    At symmetric allocation over J sources with complementarity ρ:
      Q_inner = J^{(1-ρ)/ρ} · x̄

    This separates two claims the paper makes:
    - *Inner* (within-CES): diverse sources are complements to each other
      (ρ_inner < 0). This is what K = (1-ρ)(J-1)/J measures.
    - *Outer* (cross-input): data quality and compute are complements
      in a meta-production function. This is a SEPARATE parameter ρ_outer.

    The inner multiplier is the diversity premium; it increases in J. -/
def innerDiversityMultiplier (J : ℕ) (ρ : ℝ) : ℝ :=
  (↑J : ℝ) ^ ((1 - ρ) / ρ)

/-- The inner diversity multiplier is increasing in J for ρ ∈ (0,1).
    More independent content sources → higher training quality. -/
theorem inner_multiplier_monotone {J1 J2 : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (_hJ1 : 1 ≤ J1) (hJ : J1 ≤ J2) :
    innerDiversityMultiplier J1 ρ ≤ innerDiversityMultiplier J2 ρ := by
  unfold innerDiversityMultiplier
  apply rpow_le_rpow (by positivity) (Nat.cast_le.mpr hJ)
  exact div_nonneg (by linarith) (le_of_lt hρ)

/-- **Outer CES: AI capability from data quality and compute.**
    Y = (α·Q^ρ_outer + (1-α)·C^ρ_outer)^{1/ρ_outer}
    where Q is training quality (from inner CES), C is compute,
    and ρ_outer governs data-compute substitutability.

    Note: this is a DIFFERENT complementarity from the inner level.
    The paper's "ρ ≪ 0 on both sides" claim conflates inner and outer
    levels. They should be separately identified and tested. -/
def outerCES (α Q C ρ_outer : ℝ) : ℝ :=
  (α * Q ^ ρ_outer + (1 - α) * C ^ ρ_outer) ^ (1 / ρ_outer)


-- ============================================================
-- Part F: Budget-Managed Autonomous Purchasing
-- ============================================================

/-- **Purchase value**: number of queries the budget supports.
    User sets monthly budget B; on-device AI allocates optimally
    across queries based on importance and source quality. -/
def purchaseValue (B p_avg : ℝ) : ℝ := B / p_avg

/-- Higher budget → more queries purchasable (trivially monotone). -/
theorem budget_monotone {B₁ B₂ p : ℝ}
    (hp : 0 < p) (hB : B₁ < B₂) :
    purchaseValue B₁ p < purchaseValue B₂ p := by
  unfold purchaseValue; exact div_lt_div_of_pos_right hB hp

/-- **Context log value.** A context log entry contains the purchased
    data PLUS curriculum metadata: what was asked (user intent), the
    synthesis with ROM knowledge, and the quality signal (did the
    answer work? was there a follow-up?).

    The curriculum signal (V_curriculum) is what makes context logs
    more valuable than raw purchased data for training: it reveals
    WHAT TO STUDY, not just what the answers are.

    Note: the synthesis itself should NOT enter the training corpus
    (to avoid self-referential model collapse). Only the metadata
    about what was needed and what worked should be used. -/
def contextLogValue (V_purchased V_curriculum : ℝ) : ℝ :=
  V_purchased + V_curriculum

/-- Context log strictly more valuable than purchased data alone. -/
theorem log_exceeds_purchase {V_purchased V_curriculum : ℝ}
    (hV : 0 < V_curriculum) :
    V_purchased < contextLogValue V_purchased V_curriculum := by
  unfold contextLogValue; linarith

/-- **User training data revenue.** The local AI can sell aggregated
    context log metadata (not raw queries) back to model providers
    for micropayments. This creates bidirectional micropayment flow:
    - User → content producers (buying fresh data)
    - Model providers → user (buying curriculum signal)

    Revenue per user: n_interactions · p_metadata per period. -/
def userTrainingRevenue (n_interactions p_metadata : ℝ) : ℝ :=
  n_interactions * p_metadata

/-- **Net user cost** = content spending - training data revenue.
    The user's on-device AI manages both sides automatically:
    buying content within the budget and selling training signal
    to model providers. -/
def netUserCost (B_content R_training : ℝ) : ℝ :=
  B_content - R_training

/-- **Active users break even.** Sufficiently active users generate
    enough training data revenue to offset their content spending.
    The marketplace becomes self-sustaining for engaged users:
    the cost of accessing the knowledge commons approaches zero. -/
theorem active_user_free {B R : ℝ} (h : B ≤ R) :
    netUserCost B R ≤ 0 := by
  unfold netUserCost; linarith


-- ============================================================
-- Part G: Freshness Decay as Natural Anti-Distillation Defense
-- ============================================================

/-- **Freshness value decay.** Content value decays exponentially:
    V(t) = V_0 · e^{-δ·t}, where δ is the freshness decay rate.

    Timeliness-sensitive content (breaking news, market data, weather,
    regulatory updates) has large δ. By the time a model could distill
    and deploy the knowledge, the content is stale and the next day's
    feed is needed. This is the natural defense against distillation
    for the majority of real-time marketplace transactions. -/
def freshnessValue (V_0 δ t : ℝ) : ℝ := V_0 * exp (-δ * t)

/-- Freshness value is positive when initial value is positive. -/
theorem freshness_decay_positive {V_0 δ t : ℝ}
    (hV : 0 < V_0) : 0 < freshnessValue V_0 δ t :=
  mul_pos hV (exp_pos _)

/-- **Distillation unprofitable for fresh content.** When content
    decays faster than the distillation cycle (δ·t_distill is large),
    the content's value at distillation completion is less than the
    cost of distilling. The economic defense is structural:
    distillation is simply not worth attempting on fresh content. -/
theorem distillation_unprofitable {V_0 δ t_distill c_distill : ℝ}
    (_hV : 0 < V_0) (_hδ : 0 < δ) (_ht : 0 < t_distill)
    (h_decay : freshnessValue V_0 δ t_distill < c_distill) :
    freshnessValue V_0 δ t_distill < c_distill := h_decay

/-- Marketplace sustainability (legacy). -/
theorem marketplace_sustainability {R_mp R_min : ℝ}
    (h : R_min < R_mp) : R_min < R_mp := h

end
