Require Import StoreWidthKindHistory MemoryRequestWidth StoreWriteCompareNode.
Require Import StoreWidthZeroHistory StoreWriteCompareZero StoreNonStoreDecode.
Require Import StoreRequestMaskHistory StoreRequestMaskValues StoreTypeCorrespondence CoreSocModel ComparisonNodes
 FormalObservedHistory FormalLocalHistory StoreDataCycleCommit FormalCheckerResetConnections FormalStallHistory ALUInputStability
 ObservedJointRegisterConcrete JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem store_active_compare_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (lane<3)%coq_nat ->store_type_is_store instruction lane ->
 VM.find 8027(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset Instruction Lane Store.
 destruct(observed_history memory inputs k observed Observe Legal)as[bit[history[Last[Steps Resets]]]].
 assert(Stall:forall t,(6<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7765(history t)=Some(Gval(Fuint 1)[::bit])).
 { intros t Lower Upper. do 6(destruct t as[|t];[lia|]).
 eapply(stall_after_six _ (history t)(history(S t))(history(S(S t)))(history(S(S(S t))))(history(S(S(S(S t)))))(history(S(S(S(S(S t))))))(history(S(S(S(S(S(S t)))))))bit);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps];lia. }
 pose proof(store_observed_core_reset memory inputs k observed false Reset Observe)as CoreReset.
 assert(CoreBit:VM.find 65(history 9259%nat)=Some(Gval(Fuint 1)[::bit])).
 { eapply(reset_connection_65_transfer _ (history 9258%nat)(history 9258%nat)(history 9259%nat)bit);[|apply Steps;vm_compute;lia].
 eapply(reset_connection_24_transfer _ (history 9257%nat)(history 9257%nat)(history 9258%nat)bit);[apply Resets;vm_compute;lia|apply Steps;vm_compute;lia]. }
 rewrite Last CoreReset in CoreBit. inversion CoreBit;subst bit.
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member. destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[word[Size Value]].
 exists word;split;[exact Size|].
 rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)). rewrite Last. exact Value. }
 assert(Member:List.In(7754%nat,2%nat)joint_boundary_registers).
 { apply(List.nth_error_In joint_boundary_registers 59%nat). vm_compute;reflexivity. }
 destruct(Boundary 7754%nat 2%nat Member)as[previous[PreviousSize Previous]].
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[insn[Size Insn]].
 rewrite Instruction in Insn;inversion Insn;subst insn.
 assert(Width:VM.find 8002(history 9258%nat)=Some(Gval(Fuint 6)(from_N 6(memory_request_width true(N.to_nat(store_type_lane_kind lane)))))).
 { apply(store_width_kind_history _ history 9259 55 (N.to_nat(store_type_lane_kind lane)) ltac:(do 3(destruct lane as[|lane];[vm_compute;lia|]);lia) Steps).
   - intros t Lower Upper. apply Stall;lia.
   - intros t Lower Upper. exists(Gval(Fuint 2)previous). split;[|reflexivity].
     rewrite(joint_update_register_history_same _ history 9259 7754 2 Member Steps t Upper). exact Previous.
   - intros t Lower Upper.
     rewrite(store_type_decode_history (generated_observation_input inputs k)nil history 9259 instruction Steps ltac:(rewrite Last;exact Instruction)Size t Lower Upper).
     rewrite(store_type_decode_store (to_N instruction)lane Lane Store). rewrite N2Nat.id;reflexivity.
   - vm_compute;lia.
   - vm_compute;lia. }
 rewrite <-Last.
 eapply(store_write_compare_node_step 8027 store_write_compare_expr_8027 _ (history 9258%nat)(history 9258%nat)(history 9259%nat)).
 - unfold store_write_compare_nodes;left;reflexivity.
 - intro site. cbn[store_write_compare_expr_8027 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Width.
   do 3(destruct lane as[|lane];[reflexivity|]);lia.
 - apply Steps;vm_compute;lia.
Qed.
Theorem store_active_width_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (lane<3)%coq_nat ->store_type_is_store instruction lane ->
 VM.find 8002(top_environment observed)=Some(Gval(Fuint 6)(from_N 6(memory_request_width true(N.to_nat(store_type_lane_kind lane))))).
Proof.
 intros Observe Legal Reset Instruction Lane Store.
 destruct(observed_history memory inputs k observed Observe Legal)as[bit[history[Last[Steps Resets]]]].
 assert(Stall:forall t,(6<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7765(history t)=Some(Gval(Fuint 1)[::bit])).
 { intros t Lower Upper. do 6(destruct t as[|t];[lia|]).
 eapply(stall_after_six _ (history t)(history(S t))(history(S(S t)))(history(S(S(S t))))(history(S(S(S(S t)))))(history(S(S(S(S(S t))))))(history(S(S(S(S(S(S t)))))))bit);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps];lia. }
 pose proof(store_observed_core_reset memory inputs k observed false Reset Observe)as CoreReset.
 assert(CoreBit:VM.find 65(history 9259%nat)=Some(Gval(Fuint 1)[::bit])).
 { eapply(reset_connection_65_transfer _ (history 9258%nat)(history 9258%nat)(history 9259%nat)bit);[|apply Steps;vm_compute;lia].
 eapply(reset_connection_24_transfer _ (history 9257%nat)(history 9257%nat)(history 9258%nat)bit);[apply Resets;vm_compute;lia|apply Steps;vm_compute;lia]. }
 rewrite Last CoreReset in CoreBit. inversion CoreBit;subst bit.
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member. destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[word[Size Value]].
 exists word;split;[exact Size|].
 rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)). rewrite Last. exact Value. }
 assert(Member:List.In(7754%nat,2%nat)joint_boundary_registers).
 { apply(List.nth_error_In joint_boundary_registers 59%nat). vm_compute;reflexivity. }
 destruct(Boundary 7754%nat 2%nat Member)as[previous[PreviousSize Previous]].
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[insn[Size Insn]].
 rewrite Instruction in Insn;inversion Insn;subst insn.
 assert(Width:VM.find 8002(history 9259%nat)=Some(Gval(Fuint 6)(from_N 6(memory_request_width true(N.to_nat(store_type_lane_kind lane)))))).
 { apply(store_width_kind_history _ history 9259 55 (N.to_nat(store_type_lane_kind lane)) ltac:(do 3(destruct lane as[|lane];[vm_compute;lia|]);lia) Steps).
   - intros t Lower Upper. apply Stall;lia.
   - intros t Lower Upper. exists(Gval(Fuint 2)previous). split;[|reflexivity].
     rewrite(joint_update_register_history_same _ history 9259 7754 2 Member Steps t Upper). exact Previous.
   - intros t Lower Upper.
     rewrite(store_type_decode_history (generated_observation_input inputs k)nil history 9259 instruction Steps ltac:(rewrite Last;exact Instruction)Size t Lower Upper).
     rewrite(store_type_decode_store (to_N instruction)lane Lane Store). rewrite N2Nat.id;reflexivity.
   - vm_compute;lia.
   - vm_compute;lia. }
 rewrite <-Last;exact Width.
Qed.
