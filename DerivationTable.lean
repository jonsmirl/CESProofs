import CESProofs.Foundations.Defs
import CESProofs.Foundations.Emergence
import CESProofs.Foundations.AggregationInvariantClass
import CESProofs.Foundations.Hessian
import CESProofs.Foundations.GeneralHessian
import CESProofs.Foundations.IsoquantGeometry
import CESProofs.CurvatureRoles.Superadditivity
import CESProofs.CurvatureRoles.CorrelationRobust
import CESProofs.CurvatureRoles.Strategic
import CESProofs.CurvatureRoles.NetworkCES
import CESProofs.Foundations.InformationGeometry
import CESProofs.CurvatureRoles.PhaseTransition
import CESProofs.CurvatureRoles.QuadrupleRole
import CESProofs.Foundations.CumulantTower
import CESProofs.Foundations.CorrelationConvergence
import CESProofs.Foundations.CESEstimation
import CESProofs.CurvatureRoles.GameTheory
import CESProofs.Foundations.TenWayIdentity
import CESProofs.Foundations.FurtherProperties
import CESProofs.Foundations.GeneralWeights
import CESProofs.Potential.IRS
import CESProofs.Potential.SubstituteRegime
import CESProofs.Hierarchy.RenormalizationGroup
import CESProofs.Hierarchy.HerfindahlDynamics
import CESProofs.Applications.MonitoringCost
import CESProofs.Applications.TimeInconsistency
import CESProofs.Applications.FirmFailureResilience
import CESProofs.Hierarchy.EndogenousHierarchy
import CESProofs.Applications.Economics
import CESProofs.Macro.TwoFactorCES
import CESProofs.Macro.Accumulation
import CESProofs.Macro.TaxStructure
import CESProofs.Macro.GrowthTax
import CESProofs.Macro.DirectedTechnicalChange
import CESProofs.Macro.GreenTransition
import CESProofs.Applications.Inequality
import CESProofs.Applications.SocialWelfare
import CESProofs.Applications.HeterogeneousFirms
import CESProofs.Applications.OpenEconomy
import CESProofs.EntryExit.Defs
import CESProofs.EntryExit.CurvatureInJ
import CESProofs.EntryExit.Calculus
import CESProofs.EntryExit.Equilibria
import CESProofs.EntryExit.Welfare
import CESProofs.EntryExit.NetworkEntry
import CESProofs.EntryExit.MarketStructure
import CESProofs.Potential.Defs
import CESProofs.Potential.TsallisUniqueness
import CESProofs.Potential.CESPotential
import CESProofs.Potential.QEquilibrium
import CESProofs.Potential.EffectiveCurvature
import CESProofs.Potential.QDynamics
import CESProofs.Potential.FirmScope
import CESProofs.Potential.Welfare
import CESProofs.Potential.Appendix
import CESProofs.Potential.BilateralTrade
import CESProofs.Potential.MacroApplications
import CESProofs.Dynamics.Defs
import CESProofs.Dynamics.Relaxation
import CESProofs.Dynamics.FluctuationResponse
import CESProofs.Dynamics.SymmetricAdjustment
import CESProofs.Dynamics.PolicyCost
import CESProofs.Dynamics.ConservationLaws
import CESProofs.Dynamics.BusinessCycles
import CESProofs.Dynamics.PhillipsCycles
import CESProofs.Dynamics.MultiplierCycles
import CESProofs.Dynamics.EndogenousRho
import CESProofs.Dynamics.EndogenousT
import CESProofs.Dynamics.CoupledRhoT
import CESProofs.Dynamics.Closure
import CESProofs.Dynamics.VarianceCollapse
import CESProofs.Dynamics.FiscalDynamics
import CESProofs.Dynamics.GibbsMeasure
import CESProofs.Dynamics.DiscreteStability
import CESProofs.Dynamics.MinskySpeedRatio
import CESProofs.Dynamics.TwoWorldDefs
import CESProofs.Dynamics.TemporalOrdering
import CESProofs.Dynamics.IndicatorClassification
import CESProofs.Hierarchy.Defs
import CESProofs.Hierarchy.Topology
import CESProofs.Hierarchy.ModuliSpace
import CESProofs.Hierarchy.Activation
import CESProofs.Hierarchy.WelfareDecomposition
import CESProofs.Hierarchy.DampingCancellation
import CESProofs.Hierarchy.TransitionDynamics
import CESProofs.Hierarchy.SpectralHierarchy
import CESProofs.Hierarchy.VarianceTargeting
import CESProofs.Hierarchy.EndogenousCrossing
import CESProofs.Hierarchy.InstitutionalReform
import CESProofs.Hierarchy.MonetaryPolicy
import CESProofs.Potential.EffectiveCurvature
import CESProofs.Potential.PrimalDual
import CESProofs.Hierarchy.KnockoutHierarchy
import CESProofs.Dynamics.EntryExitDynamics
import CESProofs.Dynamics.RegimeShift
import CESProofs.Dynamics.HierarchicalJ
import CESProofs.Applications.AITransition
import CESProofs.Applications.SettlementFeedback
import CESProofs.Applications.KnowledgeCommons
import CESProofs.Applications.FairInheritance

/-!
# DerivationTable: Authoritative Catalog of the CES Formalization

Jon Smirl (2026). Companion index to the 9-paper suite.

This file serves as the **complete catalog** of the Lean 4 formalization,
organized by economic concept. Every `#check` statement is compile-time
verified — if a theorem name changes, this file fails to build.

## Statistics
- 115 files | ~1,880 declarations | 3 axioms | 126 schematics (all with proof sketches) | 0 sorry

## Organization
- Sections 1–17: Economic concepts, ~96 marquee `#check` statements
- Appendix A: Complete file index (115 files with declaration counts)
- Appendix B: Axiom inventory (3 axioms with justifications)
- Appendix C: Sorry inventory (0 sorry — all resolved)
- Appendix D: Help-wanted — 131 schematics by blocking category
-/

-- ════════════════════════════════════════════════════════════════
-- SECTION 1: CES Definition and Basic Properties
-- ════════════════════════════════════════════════════════════════
-- The CES function F = (1/J · Σ x_j^ρ)^{1/ρ} and curvature K = (1−ρ)(J−1)/J.

section CESDefinition

#check @cesFun              -- (J : ℕ) → (ρ : ℝ) → (Fin J → ℝ) → ℝ
#check @curvatureK          -- K = (1−ρ)(J−1)/J
#check @symmetricPoint      -- x* = (c, c, ..., c)
#check @curvatureK_pos      -- 0 < ρ < 1, J ≥ 2 ⟹ K > 0

-- Defs.lean: AggFun, QAGenerator, quasiArithMean, powerMean, unnormCES, irsCES,
--   IsSymmetric, IsStrictlyIncreasing, IsHomogDegOne, IsHomogDeg, IsScaleConsistent,
--   IsContinuousAgg, IsQuasiArithMean, IsPowerMean
-- Defs.lean: powerMean_symmetricPoint, curvatureK_eq_zero_of_rho_one, unnormCES_symmetricPoint

end CESDefinition

-- ════════════════════════════════════════════════════════════════
-- SECTION 2: CES Emergence Theorems
-- ════════════════════════════════════════════════════════════════
-- CES is not an assumption but a theorem: the unique aggregation function
-- compatible with constant returns + scale consistency.

section CESEmergence

#check @kolmogorov_nagumo   -- axiom: quasi-arithmetic mean characterization
#check @aczel               -- axiom: Aczél functional equation
#check @emergent_CES        -- KN + Aczél ⟹ CES
#check @aggregation_fixed_point -- CES is fixed point of multi-scale aggregation

-- Emergence.lean: powerMean_isFixedPoint, ces_mode_preserved, mode_geometric_decay,
--   modeRate_pos, modeRate_lt_one, stability_contraction, stability_rho_preserved,
--   anova_mode_connection, collision_entropy_le_log_J, renyi_entropy_le_log_J,
--   escort_uniform_at_symmetry, attractor_maximizes_renyi, ces_equivalence
-- AggregationInvariantClass.lean: aggregation_invariance_of_rho, rho_mode_rate_is_one,
--   non_ces_decays_relative_to_rho, basin_of_attraction_structure, basin_is_global,
--   convergence_rate_cubic

end CESEmergence

-- ════════════════════════════════════════════════════════════════
-- SECTION 3: Sextuple Role of Curvature K
-- ════════════════════════════════════════════════════════════════
-- K = (1−ρ)(J−1)/J simultaneously controls six economic mechanisms.

section SextupleRole

-- (a) Superadditivity: complementary agents produce more together
#check @superadditivity_qualitative  -- Gap > 0 for diverse inputs

-- (b) Correlation robustness: CES extracts idiosyncratic variation
#check @diversity_encoding     -- E[F(X)] correction ∝ K
#check @eigenvaluePerp_sq_proportional_to_K_sq  -- λ_⊥² = K²/((J-1)²c²)

-- (c) Strategic independence: balanced allocation is Nash
#check @ces_log_supermodular   -- H_{ij} > 0 for i ≠ j (replaces schematic)

-- (d) Network scaling: variety premium
#check @gainsFromVariety_gt_one -- G(J) > 1
#check @diversity_premium_proportional_to_K_logJ  -- log premium ∝ K·log J

-- (e) Information geometry bridge
#check @bridge_theorem         -- Hess(log F) = bridge × Fisher
#check @fifth_role_of_K        -- K encodes information distance

-- (f) Phase transition: regime shift at critical friction
#check @keff_below_critical            -- K_eff > 0 below T*
#check @order_parameter_exponent_one   -- β = 1 (linear order parameter)
#check @landau_minimizer_optimal       -- Landau potential minimizer

-- Master theorem unifying all six roles
#check @ces_sextuple_role      -- All six are consequences of K

-- Superadditivity.lean: superadditivity_gap_pos, superadditivity_mono,
--   superadditivity_linear_zero, gini_simpson_eq_K, gini_simpson_pos,
--   gini_simpson_bound, curvatureK_from_gap, concentration_lower_bound
-- CorrelationRobust.lean: EquicorrModel, quadratic_channel_zero_at_linear,
--   quadratic_channel_present, detection_achievable, cesEigenvaluePerp_sq,
--   eigenvaluePerp_sq_proportional_to_K_sq, quadratic_fisher_info_scales
-- Strategic.lean: ces_log_supermodular, ces_balanced_NE, deviation_payoff_neg,
--   bounded_deviation_loss, ces_decentralization, coalition_deviation_neg,
--   noProfitableCoalition, bounded_deviation_loss_general, deviation_payoff_ratio_bound
-- NetworkScaling.lean: gainsFromVariety_eq_scaling_ratio, network_log_premium,
--   premium_over_linear_factor, premium_factor_eq_K_scaled,
--   diversity_premium_proportional_to_K_logJ, below_cost_pricing [s],
--   anti_network_reversal [s]

end SextupleRole

-- ════════════════════════════════════════════════════════════════
-- SECTION 4: Ten Views — Universal Share Function
-- ════════════════════════════════════════════════════════════════
-- The CES share function s_j = x_j^ρ / Σ x_k^ρ unifies 10 economic fields.

section TenViews

#check @escortDistribution_is_shareFunction  -- Share = escort distribution
#check @factorShare_is_shareFunction         -- Share = factor share
#check @contestShare_is_shareFunction        -- Share = contest share
#check @logitProbability_is_shareFunction    -- Share = logit choice probability
#check @gibbsProb_is_shareFunction           -- Share = Gibbs probability

-- TenWayIdentity.lean: shareFunction, shareFunction_pos, shareFunction_sum,
--   shareFunction_symmetric_uniform, shareFunction_mono, shareFunction_homog,
--   shareFunction_eq_tradeShare, shareFunction_eq_portfolioWeight,
--   shareFunction_eq_votingWeight, shareFunction_eq_matchProb,
--   shareFunction_eq_spatialShare, kl_from_uniform, kl_nonneg,
--   kl_zero_iff_uniform, diversity_max_at_uniform, diversity_decreasing_in_concentration

end TenViews

-- ════════════════════════════════════════════════════════════════
-- SECTION 5: General Hessian and Isoquant Geometry
-- ════════════════════════════════════════════════════════════════
-- v^T H v = -(1-ρ)F·Var_P[v/x] at arbitrary allocation (not just symmetric).

section GeneralHessianGeometry

#check @cesGeneralHessianQF_eq_neg_variance -- v^T H v = -(1-ρ)F·Var_P[v/x]
#check @cesGeneralHessianQF_neg_semidef     -- H is negative semi-definite
#check @effectiveCurvature_at_symmetry      -- K_eff at symmetric = K
#check @effectiveCurvature_decreasing       -- K_eff decreasing in Herfindahl

-- Isoquant geometry
#check @tangentSpace_is_onePerp  -- Tangent space = {v : Σv_j = 0}
#check @isoquant_umbilic         -- All principal curvatures equal at symmetry
#check @arc_ge_chord             -- Arc length ≥ chord on isoquant

-- GeneralHessian.lean: cesGeneralHessianEntry, escortHerfindahl, effectiveCurvatureAt,
--   cesGeneralHessianQF_euler, effectiveCurvature_eq_generalK, effectiveCurvature_le_K,
--   generalHessianQF_specializes_to_symmetric, escortFisherQF, general_bridge_qf,
--   escortFisherQF_nonneg, escortFisherQF_zero_radial
-- IsoquantGeometry.lean: spaceForm_at_symmetry, superadditivity_bound_conservative,
--   positive_curvature_amplifies_gap + 22 more

end GeneralHessianGeometry

-- ════════════════════════════════════════════════════════════════
-- SECTION 6: Information Geometry and Cumulant Tower
-- ════════════════════════════════════════════════════════════════
-- The CES function lives on a statistical manifold. Hess(log F) = bridge × Fisher.
-- The cumulant tower extends this: κ₂=Fisher, κ₃=prudence, κ₄=temperance.

section InfoGeometryCumulants

-- Bridge theorem
#check @curvatureK_eq_bridge_times_fisher -- K = B × I
#check @welfare_eq_bregman               -- Welfare = Bregman divergence
#check @hierarchical_kl                 -- KL decomposes across hierarchy

-- Fisher-Rao geometry
#check @fisherRaoDistance_self           -- d(p,p) = 0
#check @fisherRao_distance_invariance   -- Reparametrization invariance

-- Cumulant tower
#check @escortCumulant2_eq_variance     -- κ₂ = escort variance (Fisher info)
#check @cumulant3_is_derivative_of_variance -- κ₃ = dκ₂/dρ (prudence)
#check @escortCumulant2_zero_at_symmetry -- All cumulants vanish at symmetry
#check @prudence_locking                -- Risk aversion + prudence locked to ρ

-- Correlation convergence
#check @compoundSymmetryCorr            -- cor = (1−r)/(1+(J−1)r)
#check @crisis_correlation_dual         -- Prices cor→1, quantities cor→−1/(J−1)

-- InformationGeometry.lean: bregmanDiv, welfare_eq_bregman, klDivExp, welfare_eq_kl,
--   kl_reverse, fisherInfoExp, welfare_curvature_is_fisher, hessLogFEigenvalue,
--   escortFisherEigenvalue, bridgeRatio, bridgeRatio_pos, bhattacharyyaCoeff,
--   slerp*, discriminating_prediction_at_midpoint + 23 more
-- CumulantTower.lean: escortPartitionZn, escortRawMoment, vri_from_moment_recursion,
--   ces_partition_identity_restated, cumulant_tower_summary
-- CorrelationConvergence.lean: gap_from_one, correlation_floor_identity,
--   price_convergence_linear, quantity_correlation_to_floor

end InfoGeometryCumulants

-- ════════════════════════════════════════════════════════════════
-- SECTION 7: Game Theory and Mechanism Design
-- ════════════════════════════════════════════════════════════════
-- CES curvature K governs strategic interactions.

section GameTheoryMechanism

#check @unique_equilibrium_complements   -- ρ < 1 ⟹ unique interior NE
#check @saddle_point_substitutes         -- ρ > 1 ⟹ saddle point
#check @symmetric_equilibrium_share      -- Equal agents ⟹ share = 1/J
#check @deviationGain_eq_K              -- Deviation gain = K
#check @folkThreshold_valid             -- Folk theorem discount threshold
#check @fitness_advantage_expands_basin  -- Fitness advantage expands basin

-- GameTheory.lean: curvatureK_sign_classification, contestShare, contestPayoff,
--   agentFitness, equilibriumShare_sum, symmetric_equilibrium_share,
--   universal_stability_complements,
--   instability_substitutes, stabilityThreshold, threshold_neg_complements,
--   threshold_pos_substitutes, knockoutPunishment_pos, cooperation_easier_with_higher_punishment,
--   amplificationExponent, amplification_pos, amplification_diverges, separatrix_symmetric

end GameTheoryMechanism

-- ════════════════════════════════════════════════════════════════
-- SECTION 8: Applied Economics — Elasticity, Demand, Trade
-- ════════════════════════════════════════════════════════════════
-- Standard CES economics: elasticity σ, factor shares, Shephard's lemma.

section AppliedEconomics

#check @elasticityOfSubstitution  -- σ = 1/(1−ρ)
#check @sigma_rho_inverse         -- σ·(1−ρ) = 1
#check @factorShare_sum_eq_one    -- Σ s_j = 1
#check @shephards_lemma           -- ∂c/∂p_j = x_j (Shephard's lemma)
#check @ces_limit_cobbDouglas     -- CES → Cobb-Douglas as ρ→0
#check @logit_is_ces_at_q_one     -- Logit = CES at q=1 (McFadden)

-- Economics.lean: sigma_pos, sigma_gt_one, factorShare_nonneg, factorShare_le_one,
--   factorShare_eq_escort, gainsFromVariety_gt_one, acr_gains_gt_one, acr_gains_autarky,
--   trade_elasticity_eq_variety_exponent, unnormCES_eq_lpNorm, powerMean_le_arithMean,
--   holder_ces_duality, curvature_conservation_as_holder_complement, euler_degree_one,
--   cesGradComponent_is_deriv, cesSlutky_symmetric, cesDemand_adding_up + 20 more

-- Estimation
#check @fisherInfoRho_zero_at_symmetry  -- Estimation paradox: no info at symmetry
#check @cramerRao_diverges_at_symmetry  -- Cramér-Rao bound → ∞ at symmetry

-- CESEstimation.lean: logRatio, olsSlope, simultaneityBias, ivEstimator,
--   ols_upward_bias, ols_downward_bias, iv_consistent, within_eliminates_fixed_effect,
--   estimation_precision_bridge, more_sectors_more_information, detection_asymmetry + 15 more

end AppliedEconomics

-- ════════════════════════════════════════════════════════════════
-- SECTION 9: CES Potential and Information Friction (Paper 2)
-- ════════════════════════════════════════════════════════════════
-- Φ_q = Φ_CES(ρ) − T·S_q: the (ρ,T) regime diagram.

section CESPotential

#check @cesPotential         -- Φ_q(p; ε) = CES potential with friction
#check @tsallisEntropy       -- S_q = Tsallis entropy

-- Effective curvature
#check @effectiveCurvatureKeff_above_critical -- K_eff = 0 above T*

-- Firm scope
#check @monotone_integration  -- Complementarity expands firm boundary

-- Paper2/Defs.lean: PotentialEconomy, cesPotential, cesPotentialGrad, qExponential,
--   qLogarithm, tsallisEntropy, cesFreeEnergy + 18 more
-- Paper2/CESPotential.lean: cesPotential_nonneg, cesPotential_zero_at_symmetry,
--   cesPotential_convex_along_perp + 6 more
-- Paper2/QEquilibrium.lean: qExp_is_optimizer [s], logit_recovery [s] + 5 more
-- Paper2/QDynamics.lean: qVariance_response [s], qCovariance_eigenstructure [s],
--   qCrooks_reversibility [s], qJarzynski_bound [s], qFriction_bound [s],
--   qOnsager_symmetry [s], qKramers_barrier [s]
-- Paper2/BilateralTrade.lean: tradeCollapse_threshold, tradeCollapse_ordering,
--   bilateral_gains_from_trade, trade_complementarity_premium + 6 more
-- Paper2/MacroApplications.lean: cesMultiplier, recession_output_drop,
--   recession_ordering_by_rho, fiscal_multiplier_curvature + 13 more

end CESPotential

-- ════════════════════════════════════════════════════════════════
-- SECTION 10: Phase Transitions and Regime Shifts
-- ════════════════════════════════════════════════════════════════
-- Order parameter, critical exponents, Landau potential.

section PhaseTransitions

#check @reducedOrderParam            -- ψ(T) = max(0, 1 − T/T*)
#check @keff_at_critical             -- K_eff = 0 at T = T*
#check @keff_continuous              -- K_eff continuous at phase boundary
#check @susceptibility_exponent_one  -- γ = 1 (susceptibility exponent)
#check @landauPotential              -- Landau potential V(t,m) = t·m + m²/2
#check @universality                 -- Universality across (J, ρ)

-- PhaseTransition.lean: criticalFriction, orderParameter_continuous,
--   orderParameter_nonneg, criticalExponent_delta, landauPotential,
--   landauPotential_analytic, criticalSlowingDown, criticalSlowingDown_pos,
--   correlation_length, correlation_length_diverges,
--   scaling_relation_rushbrooke, scaling_relation_widom,
--   upper_critical_dimension, ginzburg_criterion + 4 more

end PhaseTransitions

-- ════════════════════════════════════════════════════════════════
-- SECTION 11: Dynamics and Business Cycles (Paper 3)
-- ════════════════════════════════════════════════════════════════
-- Conservative-dissipative dynamics on the CES potential landscape.

section DynamicsCycles

-- Core dynamics
#check @landscape_structure      -- K_eff > 0 ⟹ relaxation rate > 0
#check @eigenstructure_bridge    -- ∇²Φ|_slow = W⁻¹ · ∇²V

-- Variance-response identity
-- Paper3/FluctuationResponse.lean: dynamic_vri [s], early_warning_signals [s] + 11 more

-- Symmetric adjustment
-- Paper3/SymmetricAdjustment.lean: symmetric_adjustment [s], onsager_testable [s],
--   kramers_rate [s] + 10 more

-- Conservation laws
-- Paper3/ConservationLaws.lean: euler_equilibrium_identity [s],
--   compound_symmetry_cov [s], portfolio_diversification [s],
--   crooks_reversibility [s], deadweight_from_variance [s],
--   crisis_count_invariant [s] + 11 more

-- Business cycles ordered by ρ
-- Paper3/BusinessCycles.lean: empirical_antisymmetry [s], oscillation_spectrum [s],
--   phase_lead_sign_axiom [s], crisis_cascade [s], monetary_policy_asymmetry [s],
--   great_moderation_damping [s] + 14 more

-- Multiplier-cycle duality
-- Paper3/MultiplierCycles.lean: 26 declarations including multiplier_cycle_duality,
--   rho_determines_cycle_amplitude, fiscal_multiplier_proportional_to_K + 23 more

-- Phillips cycles
-- Paper3/PhillipsCycles.lean: endogenous_cycle_existence [s],
--   oscillation_energy_approx_conserved [s], cycle_hierarchy [s] + 5 more

-- Endogenous ρ via four channels
-- Paper3/EndogenousRho.lean: optimal_rho_increases_with_T [s],
--   rhoT_limit_cycle [s], perez_phases [s], endogenous_tipping [s] + 12 more

-- Endogenous T
-- Paper3/EndogenousT.lean: friction_hysteresis [s] + 14 more

-- Coupled (ρ,T) dynamics
-- Paper3/CoupledRhoT.lean: hopf_bifurcation [s], limit_cycle_period [s] + 9 more

-- Variance collapse / model collapse
#check @decay_factor_in_unit       -- Variance decay factor ∈ (0,1)
#check @steady_state_variance      -- Σ* = M·σ²_new / (M−1) with injection

-- Paper3/VarianceCollapse.lean: signalDimensionality, varianceAfterNRounds,
--   varianceDecayRate_pos, varianceDecayRate_lt_one, steadyStateVariance_pos,
--   welfare_at_steadyState, welfare_increasing_in_M + 7 more

-- Fiscal injection and demand-side dynamics (Results 93-99)
#check @uniform_injection_zero_cost   -- Bu ∝ 1 → zero misallocation cost
#check @targeted_injection_cost       -- Bu ⊥ 1 → cost = λ_⊥ · ‖b‖²
#check @supply_fiscal_interaction     -- Strict welfare loss for nonzero b ⊥ 1

-- Paper3/FiscalDynamics.lean: fiscal_injection_power, uniform_injection_zero_cost,
--   targeted_injection_cost, targeted_injection_cost_nonpos,
--   deficit_vs_tax_same_misallocation, supply_fiscal_interaction,
--   steadyState_displacement [s], direction_dependent_inflation [s] + 2 more

end DynamicsCycles

-- ════════════════════════════════════════════════════════════════
-- SECTION 12: Two-World Economy and Indicators
-- ════════════════════════════════════════════════════════════════
-- Price and quantity worlds with temporal ordering.

section TwoWorldIndicators

#check @price_leads_quantity    -- Price adjustment faster than quantity
#check @temporal_rules_summary -- Six temporal ordering rules

-- Paper3/TwoWorldDefs.lean: TwoWorldEconomy, epsPQ, priceRelaxTime,
--   quantityRelaxTime, timescaleGap + 9 more
-- Paper3/TemporalOrdering.lean: priceLeadsQuantity, quantityMorePersistent,
--   priceMoreVolatile, quantityLeadsProfit, profitLeadsInvestment + 5 more
-- Paper3/IndicatorClassification.lean: Conference Board LEI/CEI/LAG derived from
--   4 ordering principles. administeredSpeed, administered_slower + 16 more

end TwoWorldIndicators

-- ════════════════════════════════════════════════════════════════
-- SECTION 13: Hierarchical Architecture (Paper 4)
-- ════════════════════════════════════════════════════════════════
-- N-level hierarchy with timescale separation.

section HierarchicalArchitecture

-- Damping cancellation: increasing regulation speeds convergence but lowers output
#check @damping_cancellation_algebraic -- Effects exactly cancel
#check @upstream_reform_beta           -- Reform upstream (level n−1) to help level n

-- R₀ activation
#check @activation_two_level     -- Nontrivial equilibrium iff R₀ > 1

-- Transition dynamics
-- Paper4/TransitionDynamics.lean: wright_law_duration [s], regime_diagram_complete [s],
--   closure_theorem [s], dispersion_leading_indicator [s], structural_estimation [s] + 6 more

-- Spectral hierarchy
#check @large_gap_implies_separation -- Large gap implies timescale separation

-- Welfare decomposition
#check @aggregateWelfareLoss_nonneg -- Welfare loss ≥ 0

-- Paper4/Defs.lean: HierarchicalEconomy, levelCurvatureK, portTopology,
--   timescaleSeparation, nextGenerationMatrix, spectralRadius + 18 more
-- Paper4/Topology.lean: tree_topology [s], slow_manifold_attractive [s],
--   axiom_independence [s], jacobian_lower_triangular [s]
-- Paper4/Activation.lean: ngm_char_poly_general [s], reduced_dynamics [s] + 6 more
-- Paper4/DampingCancellation.lean: dampingCancellation, upstreamReformDominates,
--   regulation_speeds_convergence, regulation_lowers_output + 7 more
-- Paper4/SpectralHierarchy.lean: spectralHierarchy_eigenvalue_ordering,
--   cross_level_amplification, north_institutional_layering [s] + 21 more

-- Endogenous crossing (Wright's Law)
#check @monotone_activation_chain      -- Learning curve chain monotone

-- Paper4/EndogenousCrossing.lean: wrightLawCostReduction, learningCurveSlope,
--   cost_parity_condition, crossing_time, investment_driven_crossing,
--   overinvestment_accelerates_crossing + 8 more

-- Institutional reform
-- Paper4/InstitutionalReform.lean: reformEquivalence, reformFragilityIndex,
--   reform_reduces_fragility, upstream_reform_principle + 14 more

-- Monetary policy
-- Paper4/MonetaryPolicy.lean: liquidityTrap_threshold, transmission_degradation,
--   monetary_fiscal_complementarity + 10 more

end HierarchicalArchitecture

-- ════════════════════════════════════════════════════════════════
-- SECTION 14: Macro — Two-Factor CES, Growth, Tax
-- ════════════════════════════════════════════════════════════════
-- Y = A[αK^ρ + (1−α)L^ρ]^{1/ρ}, Ramsey growth, optimal taxation.

section MacroExtensions

-- Two-factor CES
#check @twoFactorCES          -- Y = A[αK^ρ + (1−α)L^ρ]^{1/ρ}
#check @capitalShare           -- α_K = α·(K/Y)^ρ
#check @euler_two_factor       -- Euler's theorem: Y = MPK·K + MPL·L

-- Directed technical change
#check @dtcPremium_threshold_sigma_2 -- σ = 2 threshold for bias direction
#check @dtc_bias_invariant_cobbDouglas -- No bias at Cobb-Douglas

-- Green transition
#check @crossing_at_Qstar     -- Clean energy crosses at Q*
#check @planar_learns_faster   -- d=2 learns faster than d=1

-- Capital accumulation
#check @goldenRule_savings_eq_capitalShare -- s* = α (golden rule)
#check @ramsey_above_goldenRule           -- Ramsey above golden rule

-- Growth and tax
#check @growthRate_decreasing  -- Tax reduces growth rate
#check @ramsey_inverse_elasticity -- Ramsey inverse elasticity rule

-- TwoFactorCES.lean: 41 declarations including twoFactorCES, capitalShare, laborShare,
--   mpk, mpl, relativeWage, shares_sum_one, euler_twoFactor + 33 more
-- Accumulation.lean: 42 declarations including capitalAccumulation, eulerConsumptionGrowth,
--   steadyStateKY, goldenRule_cobbDouglas, ramseySteadyState_MPK + 37 more
-- GrowthTax.lean: 42 declarations including growthRate, investmentRate, discountGap,
--   npvRevenue, levelEffect, lafferRevenue_symmetric, npv_left_dominates_right + 35 more
-- TaxStructure.lean: 58 declarations including optimalTaxRate, lafferRevenue,
--   deadweightLoss, lafferPeak, excess_burden_proportional_to_tau_sq + 53 more

end MacroExtensions

-- ════════════════════════════════════════════════════════════════
-- SECTION 15: Endogenous Diversity — Paper 1c
-- ════════════════════════════════════════════════════════════════
-- Entry/exit determines J endogenously. Per-capita surplus has hump shape.

section EndogenousDiversity

#check @perCapitaSurplus_le_peak     -- Per-capita surplus peaks at interior J
#check @curvatureKReal_increasing   -- K increases in J (for ρ < 1)

-- Paper1c/Defs.lean: EntryExitEconomy, entryBenefit, entryCost, netEntryBenefit + 12 more
-- Paper1c/CurvatureInJ.lean: curvatureK_increasing_in_J, curvatureK_limit_in_J + 9 more
-- Paper1c/Calculus.lean: 30 declarations including perCapitaSurplus, perCapitaSurplus_deriv,
--   perCapitaSurplus_hump_shape + 27 more
-- Paper1c/Equilibria.lean: multiple_equilibria_fold [s] + 7 more
-- Paper1c/MarketStructure.lean: markup, lernerIndex, marketPower,
--   markup_decreasing_in_J, lerner_equals_inverse_sigma + 7 more
-- Paper1c/Welfare.lean: 8 declarations
-- Paper1c/WeightedEntry.lean: 4 declarations
-- Paper1c/NetworkEntry.lean: two_sided_coordination_failure [s] + 4 more

end EndogenousDiversity

-- ════════════════════════════════════════════════════════════════
-- SECTION 16: General Weights — Papers 2b, 3b, 4b
-- ════════════════════════════════════════════════════════════════
-- Extensions from equal weights to arbitrary positive weights.

section GeneralWeightExtensions

-- General weights (Paper 1 extension)
#check @equalWeights_maximize_K    -- Equal weights maximize curvature

-- Paper2b: weighted_curvature_conservation [s], dual_side_integration_boundary [s],
--   industrial_policy_rigidity [s], optimal_redundancy_design [s],
--   knockout_driven_integration [s] + 15 more
-- Paper3b: multi_modal_relaxation_spectrum [s], weighted_vri [s],
--   concentration_skews_variance [s], dynamic_knockout_propagation [s],
--   knockout_triggered_regime_shift [s] + 13 more
-- Paper4b: concentration_bottleneck [s], irs_modified_activation [s],
--   general_weight_bridge [s], per_level_primal_dual_bridge [s],
--   upstream_reform_weights [s], partial_knockout_cascade [s],
--   critical_supplier_threshold [s], herfindahl_predicts_cascade_risk [s],
--   three_dimensional_regime_diagram [s] + 15 more

end GeneralWeightExtensions

-- ════════════════════════════════════════════════════════════════
-- SECTION 17: Welfare, Trade, Applications
-- ════════════════════════════════════════════════════════════════

section WelfareTradeApplications

-- Inequality
#check @substitutability_dampens_inequality -- Higher σ dampens inequality
#check @piketty_r_gt_g                     -- r > g mechanism

-- Social welfare
#check @atkinsonIndex_nonneg_equal_weights -- Atkinson index ≥ 0

-- Herfindahl dynamics
#check @CESProofs.Hierarchy.HerfindahlDyn.herfindahl_entry_decrease -- Entry decreases concentration
#check @CESProofs.Hierarchy.HerfindahlDyn.merger_reduces_curvature  -- Mergers reduce CES curvature

-- Open economy
#check @impossible_trinity           -- Impossible trinity constraint

-- Inequality.lean: incomeRatio, surplusLoss, surplus_loss_nonneg,
--   income_ratio_from_ces, complements_favor_scarce, complementarity_no_tradeoff,
--   concentration_erodes_complementarity
-- InequalityMeasures.lean: theilIndex, giniIndex, shareVariance, theil_zero_at_equality,
--   theil_nonneg [s], gini_bounded_by_theil [s], theil_decomposition_additive [s] + 6 more
-- SocialWelfare.lean: atkinsonIndex_nonneg_equal_weights, rawlsian_limit [s],
--   upstream_reform_pareto [s], damping_no_distributional_conflict [s] + 12 more
-- HerfindahlDynamics.lean: herfindahl_entry_decrease, herfindahl_merger_increase,
--   curvature_decreasing_in_H, antitrust_preserves_curvature + 13 more
-- HeterogeneousFirms.lean: firmContribution, exitThreshold, cascade_exit_feedback [s],
--   melitz_ces_equivalence [s] + 9 more
-- OpenEconomy.lean: armingtonCES, termsOfTrade, spectralGap_convergence [s] + 10 more

-- Applied papers
-- Paper6/AITransition.lean: 17 declarations including learningCurveAlpha,
--   meshFormationThreshold, autocatalyticGrowthRate, baumolCeiling + 13 more
-- Paper7/SettlementFeedback.lean: 35 declarations including stablecoinDemand,
--   treasuryAbsorption, monetaryDegradation, kyleLambda, bistableEquilibrium + 30 more
-- Paper10/KnowledgeCommons.lean: 39 declarations including openSourceDynamics,
--   knowledgeSpillover, commonsTragedyThreshold + 36 more

end WelfareTradeApplications


-- ════════════════════════════════════════════════════════════════
-- APPENDIX A: Complete File Index
-- ════════════════════════════════════════════════════════════════
/-!
## Appendix A: Complete File Index (115 files)

### Paper 1 — Emergent CES (30 files, ~590 declarations)
| File | Decls | Description |
|------|-------|-------------|
| Defs.lean | 21 | CES function, curvature K, symmetric point |
| Basic.lean | 3 | Emergent CES (2 axioms + 1 theorem) |
| Emergence.lean | 26 | Three convergent emergence proofs |
| AggregationInvariantClass.lean | 12 | Scale consistency ⟹ CES |
| Hessian.lean | 16 | Eigenvalues at symmetric equilibrium |
| GeneralHessian.lean | 18 | v^T H v at arbitrary allocation |
| IsoquantGeometry.lean | 28 | Isoquant curvature, umbilic |
| Superadditivity.lean | 10 | Gap ≥ Ω(K)·diversity |
| CorrelationRobust.lean | 14 | E[F(X)] correction ∝ K, K² scaling |
| Strategic.lean | 9 | Log-supermodularity, no coalition benefits |
| NetworkScaling.lean | 12 | G(J) = J^{1/ρ}·c, K·log J premium |
| PhaseTransition.lean | 22 | Order parameter, critical exponents |
| QuadrupleRole.lean | 2 | Master unification theorem |
| InformationGeometry.lean | 63 | Bridge theorem, Fisher-Rao, geodesics |
| CumulantTower.lean | 26 | κ₂=Fisher, κ₃=prudence, κ₄=temperance |
| CorrelationConvergence.lean | 14 | Compound symmetry, crisis duals |
| CESEstimation.lean | 36 | Estimation paradox, IV identification |
| GameTheory.lean | 30 | Nash, Folk theorem, contest games |
| TenWayIdentity.lean | 27 | 10 fields ≡ 1 function |
| FurtherProperties.lean | 13 | Third derivative, algebraic properties |
| GeneralWeights.lean | 10 | Arbitrary weights, secular equation |
| IRS.lean | 10 | Increasing returns to scale |
| SubstituteRegime.lean | 16 | ρ > 1 regime |
| RenormalizationGroup.lean | 24 | Scaling dimensions, fixed points |
| NetworkCES.lean | 23 | Spectral gap, Fiedler vector |
| HerfindahlDynamics.lean | 17 | Entry/exit on concentration |
| MonitoringCost.lean | 14 | Monitoring cost structure |
| TimeInconsistency.lean | 13 | Dynamic inconsistency |
| FirmFailureResilience.lean | 10 | Knockout robustness |
| EndogenousHierarchy.lean | 29 | Hierarchy from spectral clustering |

### Paper 2 — CES Potential (11 files, ~130 declarations)
| File | Decls | Description |
|------|-------|-------------|
| Paper2/Defs.lean | 25 | PotentialEconomy, q-exponential |
| Paper2/TsallisUniqueness.lean | 7 | Uniqueness of Tsallis potential |
| Paper2/CESPotential.lean | 9 | Φ_q properties |
| Paper2/QEquilibrium.lean | 7 | q-exponential optimizer |
| Paper2/EffectiveCurvature.lean | 12 | K_eff = K·(1−T/T*)⁺ |
| Paper2/QDynamics.lean | 11 | VRI, Onsager, Kramers with friction |
| Paper2/FirmScope.lean | 10 | Optimal firm boundary |
| Paper2/Welfare.lean | 12 | Six derivations |
| Paper2/Appendix.lean | 10 | Technical lemmas |
| Paper2/BilateralTrade.lean | 10 | Trade collapse ordering |
| Paper2/MacroApplications.lean | 17 | CES multiplier, recession ordering |

### Paper 3 — Dynamics (18 files, ~300 declarations)
| File | Decls | Description |
|------|-------|-------------|
| Paper3/Defs.lean | 23 | DynamicalEconomy, relaxation |
| Paper3/Relaxation.lean | 8 | Landscape structure |
| Paper3/FluctuationResponse.lean | 13 | VRI |
| Paper3/SymmetricAdjustment.lean | 13 | Onsager, Kramers |
| Paper3/PolicyCost.lean | 11 | Jarzynski, friction work |
| Paper3/ConservationLaws.lean | 17 | Euler identity, portfolio |
| Paper3/BusinessCycles.lean | 20 | Cycles by ρ, great moderation |
| Paper3/PhillipsCycles.lean | 8 | Endogenous cycles |
| Paper3/MultiplierCycles.lean | 26 | Multiplier-cycle duality |
| Paper3/EndogenousRho.lean | 16 | ρ via four channels |
| Paper3/EndogenousT.lean | 15 | Endogenous friction |
| Paper3/CoupledRhoT.lean | 11 | Hopf bifurcation |
| Paper3/Closure.lean | 11 | Closure conditions |
| Paper3/VarianceCollapse.lean | 14 | Self-referential variance decay |
| Paper3/GibbsMeasure.lean | 35 | Gibbs measure, detailed balance |
| Paper3/DiscreteStability.lean | 19 | Discrete stability |
| Paper3/TwoWorldDefs.lean | 14 | Price/quantity worlds |
| Paper3/TemporalOrdering.lean | 10 | Six temporal rules |
| Paper3/IndicatorClassification.lean | 28 | LEI/CEI/LAG derivation |

### Paper 4 — Hierarchical Architecture (12 files, ~170 declarations)
| File | Decls | Description |
|------|-------|-------------|
| Paper4/Defs.lean | 24 | HierarchicalEconomy |
| Paper4/Topology.lean | 6 | Tree topology, slow manifold |
| Paper4/ModuliSpace.lean | 4 | Moduli space theorem |
| Paper4/Activation.lean | 8 | R₀ spectral radius |
| Paper4/WelfareDecomposition.lean | 17 | Level-by-level welfare |
| Paper4/DampingCancellation.lean | 11 | Damping cancellation |
| Paper4/TransitionDynamics.lean | 11 | Wright's Law, regime diagram |
| Paper4/SpectralHierarchy.lean | 24 | Spectral hierarchy |
| Paper4/VarianceTargeting.lean | 8 | Variance targeting |
| Paper4/EndogenousCrossing.lean | 14 | Learning curve R₀ |
| Paper4/InstitutionalReform.lean | 18 | Reform equivalence |
| Paper4/MonetaryPolicy.lean | 13 | Liquidity trap, transmission |

### Papers 2b, 3b, 4b — General Weight Extensions (14 files, ~84 declarations)
| File | Decls | Description |
|------|-------|-------------|
| Paper2b/Defs.lean | 9 | Weighted potential economy |
| Paper2b/EffectiveCurvature.lean | 10 | Weight-dependent K_eff |
| Paper2b/IRSFirmScope.lean | 7 | IRS firm scope |
| Paper2b/KnockoutSupplyChain.lean | 4 | Knockout supply chain |
| Paper2b/PrimalDual.lean | 6 | Weighted curvature conservation |
| Paper3b/Defs.lean | 9 | Weighted dynamical economy |
| Paper3b/RelaxationSpectrum.lean | 5 | Multi-modal relaxation |
| Paper3b/WeightedVRI.lean | 4 | Weighted VRI |
| Paper3b/WeightedCycles.lean | 4 | Weighted oscillation spectrum |
| Paper3b/KnockoutDynamics.lean | 6 | Knockout regime shifts |
| Paper4b/Defs.lean | 12 | Weighted hierarchical economy |
| Paper4b/WeightedActivation.lean | 5 | Concentration bottleneck |
| Paper4b/WeightedBridge.lean | 7 | General weight bridge |
| Paper4b/KnockoutHierarchy.lean | 7 | Partial knockout cascade |

### Paper 1c — Endogenous Diversity (8 files, ~94 declarations)
| File | Decls | Description |
|------|-------|-------------|
| Paper1c/Defs.lean | 16 | Entry/exit economy |
| Paper1c/CurvatureInJ.lean | 11 | K as function of J |
| Paper1c/Calculus.lean | 30 | Per-capita surplus, hump shape |
| Paper1c/Equilibria.lean | 8 | Multiple equilibria |
| Paper1c/Welfare.lean | 8 | Welfare analysis |
| Paper1c/WeightedEntry.lean | 4 | Weighted entry |
| Paper1c/NetworkEntry.lean | 5 | Network entry |
| Paper1c/MarketStructure.lean | 12 | Markup, Lerner index |

### Paper 3c — Dynamics of Endogenous Diversity (6 files, ~59 declarations)
| File | Decls | Description |
|------|-------|-------------|
| Paper3c/Defs.lean | 15 | Entry/exit dynamical economy |
| Paper3c/EntryExitDynamics.lean | 10 | Phase portrait |
| Paper3c/RegimeShift.lean | 9 | Fold bifurcation |
| Paper3c/CoupledSystem.lean | 8 | Coupled 3D, Hopf |
| Paper3c/HierarchicalJ.lean | 8 | Activation cascade |
| Paper3c/Welfare.lean | 9 | Welfare under entry/exit |

### Macro Extensions (12 files, ~360 declarations)
| File | Decls | Description |
|------|-------|-------------|
| TwoFactorCES.lean | 41 | Y = A[αK^ρ + (1−α)L^ρ]^{1/ρ} |
| DirectedTechnicalChange.lean | 26 | Factor-augmenting bias |
| GreenTransition.lean | 28 | Clean/dirty, Wright's Law |
| Accumulation.lean | 42 | Euler, golden rule, Ramsey |
| GrowthTax.lean | 42 | Growth drag, NPV, Laffer |
| TaxStructure.lean | 58 | 37+ tax theorems |
| Economics.lean | 63 | Elasticity, shares, duality |
| Inequality.lean | 9 | Income ratio, Piketty |
| InequalityMeasures.lean | 13 | Theil, Gini |
| SocialWelfare.lean | 16 | Atkinson, upstream reform |
| HeterogeneousFirms.lean | 13 | Melitz-CES, cascade exit |
| OpenEconomy.lean | 13 | Armington, terms-of-trade |

### Applied Papers (3 files, ~91 declarations)
| File | Decls | Description |
|------|-------|-------------|
| Paper6/AITransition.lean | 17 | AI transition, mesh formation |
| Paper7/SettlementFeedback.lean | 35 | Settlement, Kyle's λ |
| Paper10/KnowledgeCommons.lean | 39 | Knowledge commons |
-/

-- ════════════════════════════════════════════════════════════════
-- APPENDIX B: Axiom Inventory
-- ════════════════════════════════════════════════════════════════
/-!
## Appendix B: Axiom Inventory (3 axioms)

All three axioms encode classical mathematical results not yet in Mathlib.

| # | Axiom | File | Justification |
|---|-------|------|---------------|
| 1 | `kolmogorov_nagumo` | Basic.lean:34 | Kolmogorov–Nagumo (1930). |
| 2 | `aczel` | Basic.lean:48 | Aczél (1948) functional equation. |
| 3 | `transition_duration_scaling` | Paper4/TransitionDynamics:125 | Neishtadt GSPT (1987). |
-/

-- ════════════════════════════════════════════════════════════════
-- APPENDIX C: Sorry Inventory
-- ════════════════════════════════════════════════════════════════
/-!
## Appendix C: Sorry Inventory (0 sorry — all resolved)

All 3 former sorry statements in `NetworkCES.lean` have been proved:

| # | Theorem | Status | Technique |
|---|---------|--------|-----------|
| 1 | NC-12 `adding_link_increases_gap` | PROVED | `le_csInf` + Rayleigh quotient monotonicity |
| 2 | NC-13 `disconnected_zero_curvature` | PROVED | Compactness (IsCompact.exists_isMinOn) + contradiction |
| 3 | NC-15 `networkHessian_spectralGap_bound` | PROVED | `csInf_le` + BddBelow + inequality direction fix |

NC-15 also had a bug fix: the inequality direction was swapped (now H(v) ≤ bound).
NC-12 gained a `hw : ∀ j k, 0 ≤ net₁.w j k` hypothesis (needed for BddBelow).
NC-13 gained a `hJ : 2 ≤ J` hypothesis (needed for nonempty feasible set).
-/

-- ════════════════════════════════════════════════════════════════
-- APPENDIX D: Help Wanted — 129 Schematics by Blocking Category
-- ════════════════════════════════════════════════════════════════
/-!
## Appendix D: Help Wanted — Schematic Proofs (129 `True := trivial`)

These theorems have **real mathematical statements** but placeholder proofs.
Each represents a genuine formalization opportunity. They are grouped by the
mathematical infrastructure needed to replace the schematic.

### ODE / Dynamical Systems (~40 schematics)
Requires: Hopf bifurcation, Poincaré-Bendixson, replicator equations, phase portraits.

| File | Theorem | Description |
|------|---------|-------------|
| Paper3/EndogenousRho.lean | `optimal_rho_increases_with_T` | Implicit function on FOC |
| Paper3/EndogenousRho.lean | `price_equation_rho` | Price dynamics in ρ |
| Paper3/EndogenousRho.lean | `T_dependent_selection` | Selection under friction |
| Paper3/EndogenousRho.lean | `rhoT_limit_cycle` | Limit cycle existence |
| Paper3/EndogenousRho.lean | `perez_phases` | Technological revolution phases |
| Paper3/EndogenousRho.lean | `endogenous_tipping` | Tipping point dynamics |
| Paper3/EndogenousRho.lean | `power_law_fluctuations` | Power-law tails |
| Paper3/CoupledRhoT.lean | `hopf_bifurcation` | Hopf bifurcation theorem |
| Paper3/CoupledRhoT.lean | `limit_cycle_period` | Period of limit cycle |
| Paper3/CoupledRhoT.lean | `fully_specified_system` | Complete ODE system |
| Paper3/PhillipsCycles.lean | `endogenous_cycle_existence` | Poincaré-Bendixson |
| Paper3/PhillipsCycles.lean | `oscillation_energy_approx_conserved` | Energy conservation |
| Paper3/PhillipsCycles.lean | `oscillation_vs_gdp` | Cycle amplitude vs GDP |
| Paper3/PhillipsCycles.lean | `cycle_hierarchy` | Multi-scale cycles |
| Paper3/EndogenousT.lean | `friction_hysteresis` | Hysteresis in T |
| Paper3/Closure.lean | `rho_diversity_selection` | Diversity selection dynamics |
| Paper3/Closure.lean | `industrial_policy_diversity` | Policy on diversity |
| Paper3/Closure.lean | `closure_no_free_params` | Closure integrability |
| Paper3/Closure.lean | `closure_integrability` | Integrability condition |
| Paper3/Closure.lean | `closure_topological` | Topological constraint |
| Paper3c/CoupledSystem.lean | `coupled_3d_fixed_point_exists` | 3D fixed point |
| Paper3c/CoupledSystem.lean | `hopf_bifurcation_3d` | 3D Hopf bifurcation |
| Paper3c/CoupledSystem.lean | `diversity_crash_precedes_crisis` | Leading indicator |
| Paper3c/CoupledSystem.lean | `J_variance_increases_near_fold` | Variance near fold |
| Paper3c/CoupledSystem.lean | `mode_specific_J_warning` | Mode-specific warning |
| Paper3c/EntryExitDynamics.lean | `phase_portrait` | Phase portrait analysis |
| Paper3c/HierarchicalJ.lean | `endogenous_activation_cascade` | Cascade dynamics |
| Paper3c/HierarchicalJ.lean | `level_emergence` | Level emergence |
| Paper3c/RegimeShift.lean | `fold_bifurcation` | Fold bifurcation |

### Spectral Theory (~20 schematics)
Requires: Non-symmetric eigenvalues, secular equation, spectral decomposition.

| File | Theorem | Description |
|------|---------|-------------|
| Paper3/BusinessCycles.lean | `empirical_antisymmetry` | Eigenvalue antisymmetry |
| Paper3/BusinessCycles.lean | `oscillation_spectrum` | Oscillation spectrum |
| Paper3/BusinessCycles.lean | `phase_lead_sign_axiom` | Phase lead signs |
| Paper3/BusinessCycles.lean | `crisis_cascade` | Crisis cascade ordering |
| Paper3/BusinessCycles.lean | `endogenous_complementarity_lemma` | Complementarity |
| Paper3/BusinessCycles.lean | `monetary_policy_asymmetry` | Asymmetric transmission |
| Paper3/BusinessCycles.lean | `great_moderation_damping` | Great moderation |
| Paper4/Activation.lean | `ngm_char_poly_general` | NGM characteristic polynomial |
| Paper4/Activation.lean | `reduced_dynamics` | Reduced dynamics |
| Paper4/SpectralHierarchy.lean | `north_institutional_layering` | Spectral layering |
| GeneralWeights.lean | `secular_equation` | Secular equation analysis |
| GeneralWeights.lean | `gen_hessian_equal_marginals` | General Hessian |
| GeneralWeights.lean | `weighted_emergence` | Weighted CES emergence |
| EndogenousHierarchy.lean | `eigenvalue_clustering_partition` | Spectral clustering |
| EndogenousHierarchy.lean | `optimal_N_spectral` | Optimal N levels |
| EndogenousHierarchy.lean | `effective_rho_from_clustering` | ρ from clustering |
| EndogenousHierarchy.lean | `hierarchy_is_spectral_decomposition` | Spectral decomp |

### Stochastic Analysis / Path Integrals (~12 schematics)
Requires: Kramers escape, Langevin equations, fluctuation-dissipation.

| File | Theorem | Description |
|------|---------|-------------|
| Paper2/QDynamics.lean | `qVariance_response` | q-VRI |
| Paper2/QDynamics.lean | `qCovariance_eigenstructure` | q-covariance spectrum |
| Paper2/QDynamics.lean | `qCrooks_reversibility` | q-Crooks |
| Paper2/QDynamics.lean | `qJarzynski_bound` | q-Jarzynski |
| Paper2/QDynamics.lean | `qFriction_bound` | Friction bound |
| Paper2/QDynamics.lean | `qOnsager_symmetry` | q-Onsager |
| Paper2/QDynamics.lean | `qKramers_barrier` | q-Kramers escape |
| Paper3/SymmetricAdjustment.lean | `symmetric_adjustment` | Symmetric relaxation |
| Paper3/SymmetricAdjustment.lean | `onsager_testable` | Onsager reciprocity |
| Paper3/SymmetricAdjustment.lean | `kramers_rate` | Kramers escape rate |
| Paper3/FluctuationResponse.lean | `dynamic_vri` | Dynamic VRI |
| Paper3/FluctuationResponse.lean | `early_warning_signals` | Critical slowing down |

### Linear Response / Conservation (~11 schematics)
Requires: Fluctuation-dissipation theorem, Onsager reciprocity.

| File | Theorem | Description |
|------|---------|-------------|
| Paper3/ConservationLaws.lean | `euler_equilibrium_identity` | Euler at equilibrium |
| Paper3/ConservationLaws.lean | `compound_symmetry_cov` | Compound symmetry |
| Paper3/ConservationLaws.lean | `portfolio_diversification` | Diversification |
| Paper3/ConservationLaws.lean | `crooks_reversibility` | Crooks fluctuation |
| Paper3/ConservationLaws.lean | `deadweight_from_variance` | Deadweight loss |
| Paper3/ConservationLaws.lean | `crisis_count_invariant` | Crisis count |
| Paper3/PolicyCost.lean | `jarzynski_equality` | Jarzynski equality |
| Paper3/PolicyCost.lean | `friction_work_estimate` | Friction work |
| Paper3/PolicyCost.lean | `aggregation_invariant_classes` | Invariant classes |
| Paper3/PolicyCost.lean | `macroscopic_predictability` | Predictability |
| Paper3/PolicyCost.lean | `irrelevance_test` | Irrelevance test |

### Singular Perturbation / GSPT (~8 schematics)
Requires: Fenichel persistence, slow-manifold reduction, canard dynamics.

| File | Theorem | Description |
|------|---------|-------------|
| Paper4/TransitionDynamics.lean | `wright_law_duration` | Duration scaling |
| Paper4/TransitionDynamics.lean | `regime_diagram_complete` | Regime diagram |
| Paper4/TransitionDynamics.lean | `closure_theorem` | Closure |
| Paper4/TransitionDynamics.lean | `dispersion_leading_indicator` | Dispersion leads |
| Paper4/TransitionDynamics.lean | `structural_estimation` | Structural estimation |
| Paper4/Topology.lean | `tree_topology` | Tree topology |
| Paper4/Topology.lean | `slow_manifold_attractive` | Slow manifold |
| Paper4/Topology.lean | `axiom_independence` | Axiom independence |
| Paper4/Topology.lean | `jacobian_lower_triangular` | Jacobian structure |

### Convex Optimization (~8 schematics)
Requires: Lagrangian duality, simplex optimization, implicit function theorem.

| File | Theorem | Description |
|------|---------|-------------|
| Paper2/QEquilibrium.lean | `qExp_is_optimizer` | q-exponential optimality |
| Paper2/QEquilibrium.lean | `logit_recovery` | Logit as q→1 limit |
| Paper2/FirmScope.lean | `spillover_adjusted_boundary` | Firm boundary |
| Paper2/EffectiveCurvature.lean | `effectiveCurvature_taylor` | Taylor expansion |
| Paper2/EffectiveCurvature.lean | `ces_prudence_with_friction` | Prudence |
| Paper2/TsallisUniqueness.lean | `tsallis_uniqueness` | Tsallis uniqueness |
| Paper2/TsallisUniqueness.lean | `tsallis_shannon_limit` | Shannon limit |
| Paper1c/Equilibria.lean | `multiple_equilibria_fold` | Fold bifurcation |

### Topology (~5 schematics)
Requires: Winding numbers, topological invariants.

| File | Theorem | Description |
|------|---------|-------------|
| Paper4/ModuliSpace.lean | `diminishing_returns_depth` | Diminishing returns |

### Weighted Extensions (~25 schematics)
Requires: Extension of equal-weight proofs to heterogeneous weights.

| File | Theorem | Description |
|------|---------|-------------|
| Paper2b/PrimalDual.lean | `weighted_curvature_conservation` | Conservation |
| Paper2b/PrimalDual.lean | `dual_side_integration_boundary` | Dual integration |
| Paper2b/PrimalDual.lean | `industrial_policy_rigidity` | Policy rigidity |
| Paper2b/EffectiveCurvature.lean | `generalized_crisis_sequence` | Crisis sequence |
| Paper2b/KnockoutSupplyChain.lean | `optimal_redundancy_design` | Redundancy |
| Paper2b/KnockoutSupplyChain.lean | `knockout_driven_integration` | Integration |
| Paper3b/RelaxationSpectrum.lean | `multi_modal_relaxation_spectrum` | Multi-modal |
| Paper3b/RelaxationSpectrum.lean | `mode_dependent_critical_frictions` | Critical frictions |
| Paper3b/RelaxationSpectrum.lean | `multi_scale_early_warning` | Early warning |
| Paper3b/WeightedVRI.lean | `weighted_vri` | Weighted VRI |
| Paper3b/WeightedVRI.lean | `concentration_skews_variance` | Variance skew |
| Paper3b/WeightedCycles.lean | `weighted_oscillation_spectrum` | Weighted cycles |
| Paper3b/KnockoutDynamics.lean | `dynamic_knockout_propagation` | Propagation |
| Paper3b/KnockoutDynamics.lean | `knockout_triggered_regime_shift` | Regime shift |
| Paper3b/KnockoutDynamics.lean | `weight_dependent_rho_optimization` | ρ optimization |
| Paper3b/KnockoutDynamics.lean | `coupled_rho_weights_friction_dynamics` | Coupled dynamics |
| Paper4b/WeightedActivation.lean | `concentration_bottleneck` | Bottleneck |
| Paper4b/WeightedActivation.lean | `irs_modified_activation` | IRS activation |
| Paper4b/WeightedBridge.lean | `general_weight_bridge` | Weight bridge |
| Paper4b/WeightedBridge.lean | `per_level_primal_dual_bridge` | Primal-dual |
| Paper4b/WeightedBridge.lean | `upstream_reform_weights` | Upstream reform |
| Paper4b/KnockoutHierarchy.lean | `partial_knockout_cascade` | Cascade |
| Paper4b/KnockoutHierarchy.lean | `critical_supplier_threshold` | Critical supplier |
| Paper4b/KnockoutHierarchy.lean | `herfindahl_predicts_cascade_risk` | Cascade risk |
| Paper4b/KnockoutHierarchy.lean | `three_dimensional_regime_diagram` | 3D regime |

### Remaining Schematics (~12)
Various: empirical claims, game theory fixed points, monitoring.

| File | Theorem | Description |
|------|---------|-------------|
| AggregationInvariantClass.lean | `tail_exponential_at_q_one` | Tail behavior |
| FurtherProperties.lean | `substitution_savings` | Substitution savings |
| IRS.lean | `scaling_idempotency` | Scaling idempotency |
| NetworkScaling.lean | `below_cost_pricing` | Below-cost pricing |
| NetworkScaling.lean | `anti_network_reversal` | Anti-network effect |
| MonitoringCost.lean | `monitoring_technology_complementarity` | Monitoring |
| HeterogeneousFirms.lean | `cascade_exit_feedback` | Cascade exit |
| HeterogeneousFirms.lean | `melitz_ces_equivalence` | Melitz equivalence |
| OpenEconomy.lean | `spectralGap_convergence` | Spectral convergence |
| Paper2/Welfare.lean | `dmp_search_ces` | DMP search model |
| Paper4/WelfareDecomposition.lean | `welfare_lyapunov_dissipation` | Lyapunov |
| Paper1c/NetworkEntry.lean | `two_sided_coordination_failure` | Coordination |
| Paper3c/RegimeShift.lean | `fold_bifurcation` | (also listed under ODE) |
| InequalityMeasures.lean | `theil_nonneg` | Theil ≥ 0 |
| InequalityMeasures.lean | `gini_bounded_by_theil` | Gini ≤ Theil |
| InequalityMeasures.lean | `theil_decomposition_additive` | Theil additivity |
| SocialWelfare.lean | `rawlsian_limit` | Rawlsian limit |
| SocialWelfare.lean | `upstream_reform_pareto` | Upstream Pareto |
| SocialWelfare.lean | `damping_no_distributional_conflict` | Damping neutral |
-/
