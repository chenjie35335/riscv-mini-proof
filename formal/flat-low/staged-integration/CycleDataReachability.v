Require Import CycleDataNormalStep CycleISAReferenceAdvance RFArithmeticPendingClosure RFModeReachability
 CycleView ExternalReset CoreSocModel FormalLocalHistory ReferenceInstructionDecode
 RFAddPendingInvariant RFBitwisePendingInvariant RFSubtractPendingInvariant RFComparePendingInvariant
 RFCompareImmediatePendingInvariant RFShiftPendingInvariant RFUpperPendingInvariant
 MemoryPendingInvariant StorePendingInvariant PCRelativePendingInvariant CycleRedirectDecision
 JALRPendingAlignment JALRTakenInvariant.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Definition cycle_control_pending v : Prop :=
 cycle_pc_phase v /\ cycle_pc_aligned v /\ cycle_pc_relative_pending v /\
 cycle_redirect_decision v /\ cycle_jalr_pending v /\ cycle_jalr_taken v.
Definition cycle_data_state env v : Prop :=
 cycle_banks_agree v /\ cycle_rf_arithmetic_pending v /\ cycle_memory_pending v /\
 cycle_store_pending env v /\ generated_assert_m0_5_local env.
Theorem cycle_data_reachable_from_control memory inputs k observations views :
 (forall i,(i<=k)%coq_nat ->generated_observe memory inputs i=Some(observations i)) ->
 (forall i,(i<=k)%coq_nat ->generated_legal_trace memory inputs i) ->
 (forall i,(i<=k)%coq_nat ->cycle_view_at(top_environment(observations i))(views i)) ->
 (forall i,(i<k)%coq_nat ->cycle_reset inputs i false ->cycle_control_pending(views i)) ->
 (forall i,(i<k)%coq_nat ->cycle_reset inputs i false ->exists row csr,
   (row<37)%coq_nat /\
   N.land(to_N(cv_commit_instruction(views i)))(reference_instruction_mask row)=reference_instruction_code row /\
   VM.find 7332(top_environment(observations i))=Some(Gval(Fuint 32)csr) /\size csr=32%nat) ->
 cycle_data_state(top_environment(observations k))(views k).
Proof.
 induction k as[|k IH];intros Observations Legal Views Controls Classes.
 - exact(cycle_data_base memory inputs(observations 0%nat)(views 0%nat)
     (Observations 0%nat ltac:(lia))(Legal 0%nat ltac:(lia))(Views 0%nat ltac:(lia))).
 - assert(Previous:cycle_data_state(top_environment(observations k))(views k)).
   { apply IH;intros;[apply Observations|apply Legal|apply Views|apply Controls|apply Classes];try assumption;lia. }
   assert(Transition:cycle_transition memory inputs k(observations k)(observations(S k))).
   { unfold cycle_transition. split;[apply Observations;lia|]. split;[apply Legal;lia|].
     split;[apply Observations;lia|]. split;[apply Legal;lia|].
     pose proof(Observations(S k)ltac:(lia))as Observe.
     unfold generated_observe,generated_observe_cycle in Observe.
     destruct(generated_run memory inputs(S k))as[committed|]eqn:Run;[exists committed;reflexivity|discriminate]. }
   destruct(legal_observation_reset memory inputs k(Legal k ltac:(lia)))as[reset Reset].
   destruct reset.
   + exact(cycle_data_reset_step memory inputs k(observations k)(observations(S k))(views k)(views(S k))
       Transition Reset(Views k ltac:(lia))(Views(S k)ltac:(lia))).
   + destruct Previous as[Banks[Arithmetic[Memory[Store Assertion]]]].
     destruct Arithmetic as[Add[Bitwise[Subtract[Compare[Immediate[Shift Upper]]]]]].
     destruct(Controls k ltac:(lia)Reset)as[Phase[Aligned[Relative[Redirect[Jalr Taken]]]]].
     destruct(Classes k ltac:(lia)Reset)as[row[csr[Row[Match[CSR Width]]]]].
     assert(Pending:cycle_isa_pending(views k)).
     { constructor;try assumption.
       exact(cycle_writeback_mode_reachable memory inputs k(observations k)(views k)
         (Observations k ltac:(lia))(Legal k ltac:(lia))(Views k ltac:(lia))). }
     exact(cycle_data_normal_step memory inputs k(observations k)(observations(S k))(views k)(views(S k))row csr
       Transition Reset(Views k ltac:(lia))(Views(S k)ltac:(lia))Banks Pending Row Match CSR Width).
Qed.
