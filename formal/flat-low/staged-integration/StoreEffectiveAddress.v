Require Import CoreSocModel ComparisonNodes StoreExecuteControl StoreTypeCorrespondence ReferenceStoreParts ReferenceLoadSemantics MemoryAddressInputs LoadImmediateSemantics ObservedJointRegisterConcrete FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_run generated_observe generated_modules generated_top.
Theorem store_effective_address_from_immediate memory inputs k observed next instruction lane left :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 size left=32%nat ->VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 1308(top_environment observed)=Some(Gval(Fuint 32)(store_s_immediate instruction)) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(reference_load_address left(store_s_immediate instruction))).
Proof.
 intros Observe Legal Next Reset Lane Instruction Store LeftSize Left Imm.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(store_execute_control_observed memory inputs k observed instruction lane Observe Legal Lane Instruction Store)as[A[B[S Mode]]].
 exact(memory_effective_address_commit_observed memory inputs k observed next left(store_s_immediate instruction)Observe Legal Next Reset LeftSize(store_s_immediate_size instruction Size)A B Mode Left Imm).
Qed.
Require Import DUTImmediateModes.
Theorem store_immediate_dut_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 VM.find 1308(top_environment observed)=Some(Gval(Fuint 32)(store_s_immediate instruction)).
Proof.
 intros Observe Legal Lane Instruction Store.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(store_execute_control_observed memory inputs k observed instruction lane Observe Legal Lane Instruction Store)as[A[B[Select Mode]]].
 exact(dut_imm_observed 1 memory inputs k observed instruction ltac:(lia)Observe Legal Instruction Size Select).
Qed.
Theorem store_effective_address_commit memory inputs k observed next instruction lane left :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 size left=32%nat ->VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(reference_load_address left(store_s_immediate instruction))).
Proof.
 intros Observe Legal Next Reset Lane Instruction Store LeftSize Left.
 exact(store_effective_address_from_immediate memory inputs k observed next instruction lane left Observe Legal Next Reset Lane Instruction Store LeftSize Left (store_immediate_dut_observed memory inputs k observed instruction lane Observe Legal Lane Instruction Store)).
Qed.
