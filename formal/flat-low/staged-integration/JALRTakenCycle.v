Require Import JALRAddressCycle CycleView DUTRedirectDecode DUTRedirectSemantics ALUOutputTransfer EarlyControlStabilityHistory JointUpdateConnectionCertificates FormalDeclaredConnection ReferenceBankObservation RFReadPorts JointBoundaryRegisters ObservedJointRegisterConcrete DelayedRedirectObserved CoreSocModel ComparisonNodes FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem cycle_branch_ports memory inputs k observed committed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some committed ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->
 VM.find 1357(top_environment observed)=Some(Gval(Fuint 32)(cv_left v)) /\
 VM.find 1358(top_environment observed)=Some(Gval(Fuint 32)(cv_right v)).
Proof.
 intros Observe Legal Run Reset View.
 destruct(alu_output_observed_transfer_context memory inputs k observed committed Observe Legal Run Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 split.
 - assert(Source:VM.find 7816(history 9258%nat)=Some(Gval(Fuint 32)(cv_left v))).
 { rewrite(early_control_stable_7816_history (generated_observation_input inputs k)nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last. exact(cva_left _ _ View). }
 rewrite <-Last.
 eapply(declared_connection_value 1435 flat_statements joint_update_connection_1357_decl joint_update_connection_1357_mid joint_update_connection_1357_tail 1357 7816);
 [exact joint_update_connection_1357_position|exact joint_update_connection_1357_split|exact joint_update_connection_1357_straight|exact joint_update_connection_1357_mid_safe|exact joint_update_connection_1357_tail_safe|exact joint_update_connection_1357_nonregister|reflexivity|exact Source|apply dut_decode_adapt;exact(cva_left_width _ _ View)|apply Steps;vm_compute;lia].
 - assert(Source:VM.find 7819(history 9258%nat)=Some(Gval(Fuint 32)(cv_right v))).
 { rewrite(early_control_stable_7819_history (generated_observation_input inputs k)nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last. exact(cva_right _ _ View). }
 rewrite <-Last.
 eapply(declared_connection_value 1436 flat_statements joint_update_connection_1358_decl joint_update_connection_1358_mid joint_update_connection_1358_tail 1358 7819);
 [exact joint_update_connection_1358_position|exact joint_update_connection_1358_split|exact joint_update_connection_1358_straight|exact joint_update_connection_1358_mid_safe|exact joint_update_connection_1358_tail_safe|exact joint_update_connection_1358_nonregister|reflexivity|exact Source|apply dut_decode_adapt;exact(cva_right_width _ _ View)|apply Steps;vm_compute;lia].
Qed.
Theorem cycle_jalr_taken_step memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 jalr_match(cv_front_instruction before) ->cv_delayed_redirect after=true.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After Match.
 destruct(cycle_branch_ports memory inputs k current committed before Observe Legal Run Reset Before)as[Left Right].
 destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Observe Legal rf_read_front_member)as[instruction[Size Inst]].
 rewrite(cva_front_instruction _ _ Before)in Inst;inversion Inst;subst instruction.
 destruct(FormalObservedHistory.observed_history memory inputs k current Observe Legal)as[reset[history[Last[Steps Resets]]]].
 destruct(dut_decode_history (generated_observation_input inputs k)nil history 9259(cv_front_instruction before)Steps ltac:(rewrite Last;exact(cva_front_instruction _ _ Before))Size 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia))as[Selector Kind].
 rewrite Last in Selector,Kind.
 pose proof(dut_decode_controls_observed memory inputs k current(cv_front_instruction before)_ _ Observe Legal(cva_front_instruction _ _ Before)Selector Kind Size)as Controls.
 unfold dut_redirect_controls_match in Controls.
 destruct Controls as[_[_[_[_[_[_ Control]]]]]].
 change(N.land(to_N(cv_front_instruction before))28799=103)in Match.
 rewrite Match N.eqb_refl Bool.orb_true_r in Control.
 pose proof(dut_redirect_observed memory inputs k current(cv_left before)(cv_right before)_ _ Observe Legal Left Right Kind Selector(cva_left_width _ _ Before)(cva_right_width _ _ Before))as Value.
 unfold dut_redirect_function in Value. rewrite Control in Value. cbn in Value.
 pose proof(delayed_redirect_observed_step memory inputs k current committed true Observe Legal Run Reset Value)as Delayed.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7760 1 ltac:(apply(List.nth_error_In joint_boundary_registers 65%nat);vm_compute;reflexivity)Run NextObserve)as Copy.
 rewrite(cva_delayed_redirect _ _ After)Delayed in Copy;congruence.
Qed.
