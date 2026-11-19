Require Import CycleInstructionClassReachable JALRPendingInvariant CycleDataReachability CycleDataNormalStep CycleISAReferenceAdvance RFArithmeticPendingClosure RFModeReachability
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
Definition cycle_joint_pending env v : Prop :=
 cycle_data_state env v /\ cycle_pc_relative_pending v /\ cycle_redirect_decision v /\
 cycle_jalr_pending v /\ cycle_jalr_taken v.
Theorem cycle_joint_reachable_from_pc memory inputs k observations views :
 (forall i,(i<=k)%coq_nat ->generated_observe memory inputs i=Some(observations i)) ->
 (forall i,(i<=k)%coq_nat ->generated_legal_trace memory inputs i) ->
 (forall i,(i<=k)%coq_nat ->cycle_view_at(top_environment(observations i))(views i)) ->
 (forall i,(i<=k)%coq_nat ->cycle_pc_aligned(views i)) ->
 (forall i,(i<k)%coq_nat ->cycle_reset inputs i false ->exists csr,
   VM.find 7332(top_environment(observations i))=Some(Gval(Fuint 32)csr) /\size csr=32%nat) ->
 cycle_joint_pending(top_environment(observations k))(views k).
Proof.
 induction k as[|k IH];intros Observations Legal Views Alignment CSRs.
 - split.
   + exact(cycle_data_base memory inputs(observations 0%nat)(views 0%nat)
       (Observations 0%nat ltac:(lia))(Legal 0%nat ltac:(lia))(Views 0%nat ltac:(lia))).
   + split;[exact(cycle_pc_relative_pending_base memory inputs _ _ (Observations 0%nat ltac:(lia))(Views 0%nat ltac:(lia)))|].
     split;[exact(cycle_redirect_decision_base memory inputs _ _ (Observations 0%nat ltac:(lia))(Views 0%nat ltac:(lia)))|].
     split;[exact(cycle_jalr_pending_base memory inputs _ _ (Observations 0%nat ltac:(lia))(Views 0%nat ltac:(lia)))|].
     exact(cycle_jalr_taken_base memory inputs _ _ (Observations 0%nat ltac:(lia))(Views 0%nat ltac:(lia))).
 - assert(Previous:cycle_joint_pending(top_environment(observations k))(views k)).
   { apply IH;intros;[apply Observations|apply Legal|apply Views|apply Alignment|apply CSRs];try assumption;lia. }
   assert(Transition:cycle_transition memory inputs k(observations k)(observations(S k))).
   { unfold cycle_transition. split;[apply Observations;lia|]. split;[apply Legal;lia|].
     split;[apply Observations;lia|]. split;[apply Legal;lia|].
     pose proof(Observations(S k)ltac:(lia))as Observe.
     unfold generated_observe,generated_observe_cycle in Observe.
     destruct(generated_run memory inputs(S k))as[committed|]eqn:Run;[exists committed;reflexivity|discriminate]. }
   destruct(legal_observation_reset memory inputs k(Legal k ltac:(lia)))as[reset Reset].
   destruct reset.
   + split.
     * exact(cycle_data_reset_step memory inputs k _ _ _ _ Transition Reset(Views k ltac:(lia))(Views(S k)ltac:(lia))).
     * split;[exact(cycle_pc_relative_pending_reset memory inputs k _ _ _ Transition Reset(Views(S k)ltac:(lia)))|].
       split.
       { intro Late. pose proof(cycle_late_bubble_reset memory inputs k _ _ _ Transition Reset(Views(S k)ltac:(lia)));congruence. }
       split;[exact(cycle_jalr_pending_reset memory inputs k _ _ _ Transition Reset(Views(S k)ltac:(lia)))|].
       exact(cycle_jalr_taken_reset memory inputs k _ _ _ Transition Reset(Views(S k)ltac:(lia))).
   + destruct Previous as[Data[Relative[Redirect[Jalr Taken]]]].
     destruct Data as[Banks[Arithmetic[Memory[Store Assertion]]]].
     destruct Arithmetic as[Add[Bitwise[Subtract[Compare[Immediate[Shift Upper]]]]]].
     pose proof(Alignment k ltac:(lia))as Aligned.
     pose proof(proj2 Aligned)as Phase.
     destruct(cycle_commit_instruction_reference_row memory inputs k _ _
       (Observations k ltac:(lia))(Legal k ltac:(lia))Reset(Views k ltac:(lia)))as[row[Row Match]].
     destruct(CSRs k ltac:(lia)Reset)as[csr[CSR Width]].
     assert(Pending:cycle_isa_pending(views k)).
     { constructor;try assumption.
       exact(cycle_writeback_mode_reachable memory inputs k _ _
         (Observations k ltac:(lia))(Legal k ltac:(lia))(Views k ltac:(lia))). }
     pose proof(cycle_isa_reference_advance memory inputs k _ _ _ _ row csr Transition Reset
       (Views k ltac:(lia))(Views(S k)ltac:(lia))Banks Pending Row Match CSR Width)as Effect.
     split.
     * exact(cycle_data_normal_step memory inputs k _ _ _ _ row csr
         Transition Reset(Views k ltac:(lia))(Views(S k)ltac:(lia))Banks Pending Row Match CSR Width).
     * split;[exact(cycle_pc_relative_pending_normal memory inputs k _ _ _ _ Transition Reset
         (Views k ltac:(lia))(Views(S k)ltac:(lia))(Alignment(S k)ltac:(lia)))|].
       split;[exact(cycle_redirect_decision_normal memory inputs k _ _ _ _ Transition Reset
         (Views k ltac:(lia))(Views(S k)ltac:(lia))Banks Effect)|].
       split;[exact(cycle_jalr_pending_normal memory inputs k _ _ _ _ Transition Reset
         (Views k ltac:(lia))(Views(S k)ltac:(lia))Banks Effect)|].
       exact(cycle_jalr_taken_normal memory inputs k _ _ _ _ Transition Reset
         (Views k ltac:(lia))(Views(S k)ltac:(lia))).
Qed.
