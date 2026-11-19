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
Theorem store_nonstore_compare_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) ->
 VM.find 8027(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset Instruction NonStore.
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
 assert(Width:VM.find 8002(history 9258%nat)=Some(Gval(Fuint 6)(from_N 6 0))).
 { apply(store_width_zero_history _ history 9259 55 Steps).
   - intros t Lower Upper. apply Stall;lia.
   - intros t Lower Upper. exists(Gval(Fuint 2)previous). split;[|reflexivity].
     rewrite(joint_update_register_history_same _ history 9259 7754 2 Member Steps t Upper). exact Previous.
   - intros t Lower Upper.
     rewrite(store_type_decode_history (generated_observation_input inputs k)nil history 9259 instruction Steps ltac:(rewrite Last;exact Instruction)Size t Lower Upper).
     rewrite(store_nonstore_instruction_decode instruction NonStore). reflexivity.
   - vm_compute;lia.
   - vm_compute;lia. }
 rewrite <-Last.
 exact(store_write_compare_zero _ (history 9258%nat)(history 9258%nat)(history 9259%nat)Width(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
