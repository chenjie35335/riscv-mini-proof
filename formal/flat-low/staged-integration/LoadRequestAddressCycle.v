Require Import LoadTypeCorrespondence LoadEffectiveAddress LoadImmediateSemantics EarlyControlStabilityHistory StoreAddressSelectObserved StoreAddressCycleUpdate StoreRequestDataObserved StoreEffectiveAddress StoreExecuteControl StoreTypeCorrespondence ReferenceStoreParts MemoryAddressInputs ALUInputStability FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete ObservedRFPortsConcrete JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization CoreSocModel ComparisonNodes ReferenceLoadSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem load_request_address_observed memory inputs k observed instruction lane left :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<5)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->load_type_is_load instruction lane ->
 size left=32%nat ->VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 1155(top_environment observed)=Some(Gval(Fuint 32)(reference_load_address left(load_i_immediate instruction))).
Proof.
 intros Observe Legal Lane Instruction Load LeftSize Left.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member.
 destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[bits[BitsSize Value]].
 exists bits. split;[exact BitsSize|].
 rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)).
 rewrite Last. exact Value. }
 assert(Forward:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)).
 { intros t Lower Upper. rewrite(early_control_stable_7816_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 pose proof(load_operand_inputs_history (generated_observation_input inputs k)nil history 9259 instruction lane left Lane Load Size LeftSize Boundary Steps ltac:(rewrite Last;exact Instruction)Forward)as Inputs.
 destruct(Inputs 9259%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))as[OperandLeft[OperandRight OperandMode]].
 pose proof(alu_sum_to_taken_history (generated_observation_input inputs k)nil history left(load_i_immediate instruction)Boundary Steps (load_i_immediate_size instruction Size)OperandLeft OperandRight OperandMode)as Sum.
 rewrite(proj2(alu_inputs_stable_history (generated_observation_input inputs k)nil history 9259 Boundary Steps 1155 ltac:(unfold alu_stability_targets;do 3 right;left;reflexivity) 9253 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)))Last in Sum.
 exact Sum.
Qed.
Lemma load_request_address_size left instruction :size(reference_load_address left(load_i_immediate instruction))=32%nat.
Proof. unfold reference_load_address. rewrite size_take size_from_N;reflexivity. Qed.
Theorem load_request_address_commit memory inputs k observed next instruction lane left :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<5)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->load_type_is_load instruction lane ->
 size left=32%nat ->VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 8004(top_environment next)=Some(Gval(Fuint 32)(reference_load_address left(load_i_immediate instruction))).
Proof.
 intros Observe Legal Next Reset Lane Instruction Load LeftSize Left.
 pose proof(load_request_address_observed memory inputs k observed instruction lane left Observe Legal Lane Instruction Load LeftSize Left)as Address.
 pose proof(load_request_address_size left instruction)as Size.
 pose proof(store_address_select_observed memory inputs k observed _ Observe Legal Reset Size Address)as Selected.
 exact(store_address_cycle_update memory inputs k observed next _ false Observe Next Reset Selected Size).
Qed.
