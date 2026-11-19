Require Import JALRAddressCycle CycleView DUTRedirectDecode DUTRedirectSemantics ALUOutputTransfer EarlyControlStabilityHistory JointUpdateConnectionCertificates FormalDeclaredConnection ReferenceBankObservation RFReadPorts JointBoundaryRegisters ObservedJointRegisterConcrete DelayedRedirectObserved CoreSocModel ComparisonNodes FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import JALRTakenCycle MemoryPendingInvariant RFAluWritebackObserved RFWriteEffect MemoryCycleStep CycleInitialState.
Theorem cycle_redirect_raw_step memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cv_delayed_redirect after=(dut_reference_taken(to_N(cv_front_instruction before))(to_N(cv_left before))(to_N(cv_right before)) || N.eqb(N.land(to_N(cv_front_instruction before))28799)103).
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After.
 destruct(cycle_branch_ports memory inputs k current committed before Observe Legal Run Reset Before)as[Left Right].
 destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Observe Legal rf_read_front_member)as[instruction[Size Inst]].
 rewrite(cva_front_instruction _ _ Before)in Inst;inversion Inst;subst instruction.
 destruct(FormalObservedHistory.observed_history memory inputs k current Observe Legal)as[reset[history[Last[Steps Resets]]]].
 destruct(dut_decode_history (generated_observation_input inputs k)nil history 9259(cv_front_instruction before)Steps ltac:(rewrite Last;exact(cva_front_instruction _ _ Before))Size 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia))as[Selector Kind].
 rewrite Last in Selector,Kind.
 pose proof(dut_decode_controls_observed memory inputs k current(cv_front_instruction before)_ _ Observe Legal(cva_front_instruction _ _ Before)Selector Kind Size)as Controls.
 pose proof(dut_redirect_observed memory inputs k current(cv_left before)(cv_right before)_ _ Observe Legal Left Right Kind Selector(cva_left_width _ _ Before)(cva_right_width _ _ Before))as Value.
 rewrite(dut_redirect_decode _ _ _ _ _ Controls)in Value.
 pose proof(delayed_redirect_observed_step memory inputs k current committed _ Observe Legal Run Reset Value)as Delayed.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7760 1 ltac:(apply(List.nth_error_In joint_boundary_registers 65%nat);vm_compute;reflexivity)Run NextObserve)as Copy.
 rewrite(cva_delayed_redirect _ _ After)Delayed in Copy. exact(f_equal(fun value=>match value with Some(Gval _ (bit::_))=>bit|_=>false end)Copy).
Qed.

Definition cycle_reference_taken v :=
 dut_reference_taken(to_N(cv_commit_instruction v))
 (to_N(cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v)))))
 (to_N(cv_reference_bank v(to_nat(rf_instruction_address true(cv_commit_instruction v))))) ||
 N.eqb(N.land(to_N(cv_commit_instruction v))28799)103.
Definition cycle_redirect_decision v :Prop :=cv_late_bubble v=false ->cv_delayed_redirect v=cycle_reference_taken v.
Theorem cycle_redirect_decision_normal memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_reference_effect_step before after ->cycle_redirect_decision after.
Proof.
 intros Transition Reset Before After Banks Effect Late.
 pose proof(cycle_redirect_raw_step memory inputs k current next before after Transition Reset Before After)as Decision.
 pose proof(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)as Commit.
 destruct Transition as[Observe[Legal Rest]].
 assert(Size:size(cv_front_instruction before)=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Observe Legal rf_read_front_member)as[word[Size Word]].
 rewrite(cva_front_instruction _ _ Before)in Word;inversion Word;subst word;exact Size. }
 assert(Bound:forall second,(to_nat(rf_instruction_address second(cv_front_instruction before))<32)%coq_nat).
 { intro second. pose proof(to_nat_bounded(rf_instruction_address second(cv_front_instruction before)))as H.
 rewrite(rf_instruction_address_size second _ Size)in H. exact(elimT ltP H). }
 rewrite(cycle_forwarded_read memory inputs k current before false Observe Legal Before Banks)
 (cycle_forwarded_read memory inputs k current before true Observe Legal Before Banks)in Decision.
 unfold cycle_reference_taken. rewrite Commit(Effect _ (Bound false))(Effect _ (Bound true)). exact Decision.
Qed.
Theorem cycle_redirect_decision_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_redirect_decision v.
Proof.
 intros Observe View Late. pose proof(proj2(cycle_initial_bubbles memory inputs observed v Observe View))as Bubble.
 congruence.
Qed.
Require Import StartupLateBubbleInvariant Bubble7947Type PipelineBubbleInitialization StagedObservedRegister StagedCircuitRegisterHold.
Theorem cycle_late_bubble_reset memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment next)after ->cv_late_bubble after=true.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset After.
 pose proof(late_bubble_reset_successor memory inputs k committed Reset Run)as Value.
 destruct(bubble7947_run_type memory inputs(S k)committed Run)as[env[value[Env Rest]]].
 pose proof(staged_observed_register_copies memory inputs(S k)committed env next 7947
 (Logic.eq_refl true)(Logic.eq_refl true)bubble7947_initial_safe bubble7947_present Run Env NextObserve)as Copy.
 unfold top_environment in Value;rewrite Env in Value. rewrite Value in Copy.
 unfold staged_register_lookup in Copy.
 assert(Observed:VM.find 7947(top_environment next)=Some(Gval(Fuint 1)[::true])).
 { unfold top_environment. destruct(SVM.find nil next);[exact Copy|discriminate Copy]. }
 rewrite(cva_late_bubble _ _ After)in Observed;congruence.
Qed.
Theorem cycle_redirect_decision_preserved memory inputs k current next before after reset :
 cycle_transition memory inputs k current next ->cycle_reset inputs k reset ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 (reset=false ->cycle_banks_agree before /\cycle_reference_effect_step before after) ->cycle_redirect_decision after.
Proof.
 intros Transition Reset Before After Update. destruct reset.
 - intro Late. pose proof(cycle_late_bubble_reset memory inputs k current next after Transition Reset After);congruence.
 - destruct(Update(Logic.eq_refl _))as[Banks Effect].
   exact(cycle_redirect_decision_normal memory inputs k current next before after Transition Reset Before After Banks Effect).
Qed.
