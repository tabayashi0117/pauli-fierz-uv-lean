import PauliFierzUV

/-!
# Axiom check

`#print axioms` for every theorem and lemma of the library, followed by a programmatic check
(the `#eval` at the end) that every declaration in the namespace `PauliFierzUV` depends only on
`propext`, `Classical.choice` and `Quot.sound`. The `#eval` raises an error otherwise, so
`lake env lean PauliFierzUV/Axioms.lean` fails on any `sorryAx` or any added axiom.
This file is not imported by the library; run it with `scripts/check_axioms.sh`.
-/

open Lean Elab Command

#print axioms PauliFierzUV.le_liminf_ereal_of_forall
#print axioms PauliFierzUV.PaperI.log_bound
#print axioms PauliFierzUV.PaperI.tendsto_log_div
#print axioms PauliFierzUV.PaperI.main_lower_from_relerr
#print axioms PauliFierzUV.PaperI.Scaling.dilate_dilate_inv
#print axioms PauliFierzUV.PaperI.Scaling.rpow_d_aux
#print axioms PauliFierzUV.PaperI.Scaling.admissible_dilate
#print axioms PauliFierzUV.PaperI.Scaling.hasFDerivAt_dilate
#print axioms PauliFierzUV.PaperI.Scaling.kinetic_dilate
#print axioms PauliFierzUV.PaperI.Scaling.mass_dilate
#print axioms PauliFierzUV.PaperI.Scaling.energy_dilate
#print axioms PauliFierzUV.PaperI.Scaling.Finf_scaling
#print axioms PauliFierzUV.PaperI.Scaling.F_scaling_dim3
#print axioms PauliFierzUV.PaperI.Scaling.F_lambda_scaling_dim3
#print axioms PauliFierzUV.PaperI.contDiff_fderiv_apply
#print axioms PauliFierzUV.PaperI.hcs_sq
#print axioms PauliFierzUV.PaperI.ibp
#print axioms PauliFierzUV.PaperI.contDiff_fieldV
#print axioms PauliFierzUV.PaperI.fderiv_fieldV
#print axioms PauliFierzUV.PaperI.pointwise
#print axioms PauliFierzUV.PaperI.hardy_field
#print axioms PauliFierzUV.PaperI.hardy_ratio_antitone
#print axioms PauliFierzUV.PaperI.hardy_ratio_ge
#print axioms PauliFierzUV.PaperI.log_four
#print axioms PauliFierzUV.PaperI.log_six
#print axioms PauliFierzUV.PaperI.log_ten
#print axioms PauliFierzUV.PaperI.normL1_eq
#print axioms PauliFierzUV.PaperI.normL2sq_eq
#print axioms PauliFierzUV.PaperI.gradSq_eq
#print axioms PauliFierzUV.PaperI.a_eq
#print axioms PauliFierzUV.PaperI.b_eq
#print axioms PauliFierzUV.PaperI.tstar_eq
#print axioms PauliFierzUV.PaperI.F1_first_expression
#print axioms PauliFierzUV.PaperI.F1_two_expressions
#print axioms PauliFierzUV.PaperI.F1_scale_lower
#print axioms PauliFierzUV.PaperI.nash_min_lower
#print axioms PauliFierzUV.PaperI.nash_min_attained
#print axioms PauliFierzUV.PaperI.coeff_physical
#print axioms PauliFierzUV.PaperI.coeff_working
#print axioms PauliFierzUV.PaperI.coeff_cF
#print axioms PauliFierzUV.PaperI.working_functional_scaling_pos
#print axioms PauliFierzUV.PaperI.working_functional_scaling
#print axioms PauliFierzUV.PaperI.crossover_ratio
#print axioms PauliFierzUV.PaperI.vacuum_energy
#print axioms PauliFierzUV.PaperI.params_identities
#print axioms PauliFierzUV.PaperI.sq_mul_sinc
#print axioms PauliFierzUV.PaperI.integral_u
#print axioms PauliFierzUV.PaperI.integral_u_sq
#print axioms PauliFierzUV.PaperI.integral_du_sq
#print axioms PauliFierzUV.PaperI.hasDerivAt_uProfile
#print axioms PauliFierzUV.PaperI.a_value
#print axioms PauliFierzUV.PaperI.exists_root
#print axioms PauliFierzUV.PaperI.scale_lower
#print axioms PauliFierzUV.PaperI.scale_attained
#print axioms PauliFierzUV.PaperI.block_amgm
#print axioms PauliFierzUV.PaperI.virial_exponent
#print axioms PauliFierzUV.PaperI.ell_scaling
#print axioms PauliFierzUV.PaperI.virial_kinetic
#print axioms PauliFierzUV.PaperI.virial_field
#print axioms PauliFierzUV.PaperI.norm_add_sq_ge
#print axioms PauliFierzUV.PaperI.weakfloor_combination
#print axioms PauliFierzUV.PaperI.weakfloor_bracket
#print axioms PauliFierzUV.PaperI.weakfloor_conclusion
#print axioms PauliFierzUV.PaperII.Budget.absorb
#print axioms PauliFierzUV.PaperII.Budget.budget_rows
#print axioms PauliFierzUV.PaperII.Budget.kappaStar_minimal
#print axioms PauliFierzUV.PaperII.Budget.kinetic_bad_set_small
#print axioms PauliFierzUV.PaperII.massMap_eq
#print axioms PauliFierzUV.PaperII.ratio_pos
#print axioms PauliFierzUV.PaperII.bddBelow_ratio
#print axioms PauliFierzUV.PaperII.iota_le
#print axioms PauliFierzUV.PaperII.le_iota
#print axioms PauliFierzUV.PaperII.liminfRatio_pos_iff
#print axioms PauliFierzUV.PaperII.iota_pos_iff
#print axioms PauliFierzUV.PaperII.lemma_1_1_i
#print axioms PauliFierzUV.PaperII.frequently_lt_of_liminfRatio_eq_zero
#print axioms PauliFierzUV.PaperII.lemma_1_1_ii
#print axioms PauliFierzUV.PaperII.lemma_1_1_equiv
#print axioms PauliFierzUV.PaperII.iota_pos_of_tendsto
#print axioms PauliFierzUV.PaperII.corollary_C
#print axioms PauliFierzUV.PaperII.log_one_add_ge
#print axioms PauliFierzUV.PaperII.intervalIntegrable_Lintegrand
#print axioms PauliFierzUV.PaperII.Lfun_nonneg
#print axioms PauliFierzUV.PaperII.Lfun_le
#print axioms PauliFierzUV.PaperII.Lfun_sq_le
#print axioms PauliFierzUV.PaperII.qK_le
#print axioms PauliFierzUV.PaperII.tK_le
#print axioms PauliFierzUV.PaperII.partI_first_order
#print axioms PauliFierzUV.PaperII.partI_first_order_liminf
#print axioms PauliFierzUV.PaperII.partI_large_coupling
#print axioms PauliFierzUV.PaperII.partI_large_coupling_liminf
#print axioms PauliFierzUV.PaperII.xK_eq
#print axioms PauliFierzUV.PaperII.tK_eq
#print axioms PauliFierzUV.PaperII.tK_nonneg
#print axioms PauliFierzUV.PaperII.ρK_nonneg
#print axioms PauliFierzUV.PaperII.one_lt_partIBound
#print axioms PauliFierzUV.PaperII.hasDerivAt_Lfun
#print axioms PauliFierzUV.PaperII.continuous_Lfun
#print axioms PauliFierzUV.PaperII.Lfun_zero
#print axioms PauliFierzUV.PaperII.integral_Lfun
#print axioms PauliFierzUV.PaperII.integral_amplitude
#print axioms PauliFierzUV.PaperII.integral_recoil
#print axioms PauliFierzUV.PaperII.tK_from_amplitude
#print axioms PauliFierzUV.PaperII.qK_from_recoil
#print axioms PauliFierzUV.PaperII.log_three_halves_bounds
#print axioms PauliFierzUV.PaperII.log_ge_partial
#print axioms PauliFierzUV.PaperII.arsinh_sqrt_half_gt
#print axioms PauliFierzUV.PaperII.Lfun_half_lt
#print axioms PauliFierzUV.PaperII.Lfun_half_pos
#print axioms PauliFierzUV.PaperII.two_xK_half_ge
#print axioms PauliFierzUV.PaperII.two_tK_half_le
#print axioms PauliFierzUV.PaperII.qK_half_le
#print axioms PauliFierzUV.PaperII.qK_half_nonneg
#print axioms PauliFierzUV.PaperII.two_sqrt_qt_half_le
#print axioms PauliFierzUV.PaperII.partI_explicit_arith
#print axioms PauliFierzUV.PaperII.theoremA_explicit_of_partI
#print axioms PauliFierzUV.PaperII.eventually_log_sq_le
#print axioms PauliFierzUV.PaperII.growth_of_curvatureBound
#print axioms PauliFierzUV.PaperII.tendsto_ratio_of_curvatureBound
#print axioms PauliFierzUV.PaperII.iota_pos_of_curvatureBound

-- Fail unless every declaration under `PauliFierzUV` uses only the three standard axioms.
#eval show CommandElabM Unit from do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, _) in env.constants.toList do
    if (`PauliFierzUV).isPrefixOf n then
      let axs ← liftCoreM <| Lean.collectAxioms n
      count := count + 1
      let extra := axs.filter (fun a => !allowed.contains a)
      if !extra.isEmpty then
        bad := bad.push (n, extra)
  if bad.isEmpty then
    logInfo m!"OK: {count} declarations under PauliFierzUV depend only on \
      [propext, Classical.choice, Quot.sound]"
  else
    throwError m!"Non-standard axioms found: {bad}"
