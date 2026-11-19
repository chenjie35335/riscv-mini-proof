Require Import RFLoadWriteback ReferencePCSequentialValues FormalGroundNodeEquation RFAluWritebackObserved RFWritebackSelection RFPreviewEffect JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation CoreSocModel ComparisonNodes RFReadForwarding.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_pc_writeback_history invalid history limit pc :
 (forall t,(t<=limit)%coq_nat ->VM.find 7756(history t)=Some(Gval(Fuint 2)[::false;true])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 7751(history t)=Some(Gval(Fuint 32)pc)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 786(history t)=Some(Gval(Fuint 32)(reference_pc_plus_four pc)).
Proof.
 intros Modes PCs Steps t Lower Upper.
 assert (Guards:forall u,(1<=u)%coq_nat ->(u<=limit)%coq_nat ->
 VM.find 7931(history u)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 7933(history u)=Some(Gval(Fuint 1)[::true]) /\
 VM.find 7935(history u)=Some(Gval(Fuint 1)[::false])).
 { intros [|u] Lo Hi;[lia|]. exact(rf_writeback_decode_step invalid(history u)(history u)(history(S u))false true(Modes u ltac:(lia))(Steps u ltac:(lia))). }
 assert(A:VM.find 7929(history(Nat.sub t 4)%nat)=Some(Gval(Fsint 33)(zext 1(reference_pc_plus_four pc)))).
 { replace(Nat.sub t 4)%nat with(S(S(S(Nat.sub t 7))))by lia.
   eapply(rf_writeback_return_pc_signed invalid(history(Nat.sub t 7))(history(S(Nat.sub t 7)))(history(S(S(Nat.sub t 7))))(history(S(S(S(Nat.sub t 7)))))pc);[apply PCs;lia|apply Steps;lia|apply Steps;lia|apply Steps;lia]. }
 assert(L:rf_signed_low_word(reference_pc_plus_four pc)(Gval(Fsint 33)(zext 1(reference_pc_plus_four pc)))).
 { exists 33%nat,(zext 1(reference_pc_plus_four pc)). split;[reflexivity|].
   assert(Size:size(reference_pc_plus_four pc)=32%nat)by(apply reference_pc_plus_four_size).
   split;[rewrite size_zext Size;reflexivity|]. split;[reflexivity|].
   unfold zext. rewrite take_cat Size ltnn subnn take0 cats0;reflexivity. }
 destruct(Guards(Nat.sub t 4)%nat ltac:(lia)ltac:(lia))as[_[G2 _]].
 destruct(rf_load_writeback_signed_selected 7934 7933 7929 7932 invalid(history(Nat.sub t 4)%nat)(history(S(Nat.sub t 4)))true _ (reference_pc_plus_four pc) ltac:(exact(rf_writeback_member 3 ltac:(lia)))G2 A L(Steps(Nat.sub t 4)%nat ltac:(lia)))as[v2[V2 L2]].
 replace(S(Nat.sub t 4))with(Nat.sub t 3)%nat in V2 by lia.
 destruct(Guards(Nat.sub t 3)%nat ltac:(lia)ltac:(lia))as[_[_ G3]].
 destruct(rf_writeback_signed_selected 7936 7935 7930 7934 invalid(history(Nat.sub t 3)%nat)(history(S(Nat.sub t 3)))_ (reference_pc_plus_four pc) ltac:(exact(rf_writeback_member 5 ltac:(lia)))G3 V2 L2(Steps(Nat.sub t 3)%nat ltac:(lia)))as[v3[V3[width[raw[Value[RawSize[Wide Low]]]]]]].
 subst v3. replace(S(Nat.sub t 3))with(Nat.sub t 2)%nat in V3 by lia.
 assert(Cast:VM.find 7937(history(Nat.sub t 1)%nat)=Some(Gval(Fuint width)raw)).
 { replace(Nat.sub t 1)%nat with(S(Nat.sub t 2))by lia.
 apply(rf_writeback_node_step invalid(history(Nat.sub t 2)%nat)(history(Nat.sub t 2)%nat)(history(S(Nat.sub t 2)))6 _ (Fuint width));[lia| |reflexivity|apply Steps;lia].
 cbn[rf_writeback_nodes nth snd joint_update_expr_7937 eval_hfexpr_with_memory eval_href_with_memory]. rewrite V3. reflexivity. }
 replace t with(S(Nat.sub t 1))at 1 by lia. rewrite -Low.
 apply(rf_preview_data_port_exact invalid(history(Nat.sub t 1)%nat)(history(Nat.sub t 1)%nat)(history(S(Nat.sub t 1)))width raw);[exact/leP|exact RawSize|exact Cast|apply Steps;lia].
Qed.
Require Import FormalObservedHistory FormalLocalHistory JointUpdateBoundaryHistory JointBoundaryRegisters RFNonAluBubbleHazard.
Theorem rf_pc_writeback_observed memory inputs k observed pc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7756(top_environment observed)=Some(Gval(Fuint 2)[::false;true]) ->
 VM.find 7751(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find 786(top_environment observed)=Some(Gval(Fuint 32)(reference_pc_plus_four pc)).
Proof.
 intros Observe Legal Mode PC.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Member:List.In(7751%nat,32%nat)joint_boundary_registers).
 { apply(List.nth_error_In joint_boundary_registers 56%nat). vm_compute;reflexivity. }
 assert(Modes:forall t,(t<=9259)%coq_nat ->VM.find 7756(history t)=Some(Gval(Fuint 2)[::false;true])).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7756 2 rf_nonalu_mode_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last;exact Mode. }
 assert(PCs:forall t,(t<=9259)%coq_nat ->VM.find 7751(history t)=Some(Gval(Fuint 32)pc)).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7751 32 Member Steps)as Hold.
 rewrite(Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last;exact PC. }
 rewrite <-Last. exact(rf_pc_writeback_history _ history 9259 pc Modes PCs Steps 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)).
Qed.
