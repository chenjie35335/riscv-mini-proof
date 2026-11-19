Require Import RegisterInvariants FormalLocalHistory ComparisonNodes RFWritebackSelection JointUpdateBoundaryHistory.
Require Import RFLoadWriteback SharedLoadInput RFNonAluBubbleHazard ObservedJointRegisterConcrete JointBoundaryRegisters StagedRegisterHold FormalObservedHistory CycleView.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Require Import CoreSocModel.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_load_writeback_observed memory inputs k observed result :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7756(top_environment observed)=Some(Gval(Fuint 2)[::true;false]) ->
 VM.find 7904(top_environment observed)=Some(Gval(Fsint 33)result) ->
 VM.find 786(top_environment observed)=Some(Gval(Fuint 32)(take 32 result)).
Proof.
 intros Observe Legal Select Result.
 assert(M:List.In(7755%nat,3%nat)joint_boundary_registers).
 { apply(List.nth_error_In joint_boundary_registers 60%nat). vm_compute;reflexivity. }
 assert(A:List.In(7752%nat,32%nat)joint_boundary_registers).
 { apply(List.nth_error_In joint_boundary_registers 57%nat). vm_compute;reflexivity. }
 assert(R:List.In(9222%nat,32%nat)joint_boundary_registers).
 { apply(List.nth_error_In joint_boundary_registers 69%nat). vm_compute;reflexivity. }
 destruct(observed_joint_register_concrete memory inputs k observed 7755 3 Observe Legal M)as[mode[ModeSize Mode]].
 destruct mode as[|low[|middle[|high restmode]]];try discriminate ModeSize.
 destruct restmode;[|discriminate ModeSize].
 destruct(observed_joint_register_concrete memory inputs k observed 7752 32 Observe Legal A)as[address[AddressSize Address]].
 destruct address as[|b0[|b1 rest]];try discriminate AddressSize.
 destruct(observed_joint_register_concrete memory inputs k observed 9222 32 Observe Legal R)as[raw[RawSize Raw]].
 pose proof(shared_load_observed_result memory inputs k observed low middle high b0 b1 rest raw Observe Legal RawSize Mode Address Raw)as Computed.
 rewrite Result in Computed. inversion Computed;subst result.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Held:forall node,has_register node flat_statements=true ->forall t,(t<=9259)%coq_nat ->
 VM.find node(history t)=VM.find node(top_environment observed)).
 { intros node Register.
 assert(H:forall t,(t<=9259)%coq_nat ->VM.find node(history t)=VM.find node(history 0%nat)).
 { induction t as[|t IH];intro Bound;[reflexivity|].
 rewrite(staged_combinational_holds_registers _ flat_memories(history t)(history t)(history(S t))flat_statements node Register(Steps t ltac:(lia))). apply IH;lia. }
 intros t Bound. rewrite(H t Bound) -(H 9259%nat ltac:(lia)) Last. reflexivity. }
 assert(Selects:forall t,(t<=9259)%coq_nat ->VM.find 7756(history t)=Some(Gval(Fuint 2)[::true;false])).
 { intros t Bound. pose proof(joint_update_register_history_same _ history 9259 7756 2 rf_nonalu_mode_member Steps)as Hold.
 rewrite(Hold t Bound) -(Hold 9259%nat ltac:(lia)) Last. exact Select. }
 rewrite <-Last.
 apply(rf_load_writeback_register_history (formal_invalid_policy (generated_observation_input inputs k) nil) history 9259 low middle high b0 b1 rest raw RawSize Selects).
 - intros t Bound. rewrite(Held 7755 rf_load_mode_register t Bound). exact Mode.
 - intros t Bound. rewrite(Held 7752 rf_load_address_register t Bound). exact Address.
 - intros t Bound. rewrite(Held 9222 rf_load_raw_register t Bound). exact Raw.
 - exact Steps.
 - vm_compute;lia.
 - lia.
Qed.
Require Import CycleLoadResult RFModeInvariant MemoryPendingInvariant LoadTypeCorrespondence ReferenceLoadSemantics.
Theorem cycle_load_writeback_correspondence memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_memory_pending v ->cycle_writeback_mode v ->
 (lane<5)%coq_nat ->load_type_is_load(cv_commit_instruction v)lane ->
 VM.find(reference_load_output lane)(top_environment observed)=Some(Gval(Fuint 32)(cv_write_data v)).
Proof.
 intros Observe Legal Reset View Pending Mode Lane Load.
 destruct(cycle_load_result_correspondence memory inputs k observed v lane Observe Legal Reset View Pending Lane Load)as[result[Result Reference]].
 destruct(cycle_load_writeback_mode v lane Mode Lane Load)as[Low High].
 pose proof(cva_write_select _ _ View)as Select. rewrite Low High in Select.
 pose proof(rf_load_writeback_observed memory inputs k observed result Observe Legal Select Result)as Write.
 rewrite(cva_write_data _ _ View)in Write. inversion Write.
 rewrite Reference. congruence.
Qed.
