Require Import CoreSocModel ComparisonNodes MemoryRequestObservedSemantics ReferenceLoadSemantics LoadAddressAlignment LoadTypeCorrespondence FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_run generated_observe generated_modules generated_top.
Theorem memory_load_actual_address_aligned memory inputs k observed instruction lane address :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<5)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->load_type_is_load instruction lane ->
 size address=32%nat ->VM.find 7752(top_environment observed)=Some(Gval(Fuint 32)address) ->
 memory_request_load_aligned lane address=true.
Proof.
 intros Observe Legal Reset Lane Instruction Load Size Address.
 pose proof(load_type_instruction_observed memory inputs k observed instruction lane Observe Legal Lane Instruction Load)as Mode.
 destruct address as[|b0[|b1 rest]];try discriminate Size.
 destruct lane as[|lane].
 - pose proof(load_half_aligned_observed memory inputs k observed true b0 b1 rest Observe Legal Reset Size Mode Address)as Zero. subst b0;reflexivity.
 destruct lane as[|lane];[reflexivity|].
 destruct lane as[|lane].
 - destruct(load_word_aligned_observed memory inputs k observed b0 b1 rest Observe Legal Reset Size Mode Address)as[Z0 Z1]. subst b0 b1;reflexivity.
 destruct lane as[|lane].
 - pose proof(load_half_aligned_observed memory inputs k observed false b0 b1 rest Observe Legal Reset Size Mode Address)as Zero. subst b0;reflexivity.
 destruct lane as[|lane];[reflexivity|lia].
Qed.
Theorem memory_load_width_from_actual_address memory inputs k observed instruction lane rs1 immediate :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<5)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->load_type_is_load instruction lane ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)rs1) ->VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find 7752(top_environment observed)=Some(Gval(Fuint 32)(reference_load_address rs1 immediate)) ->
 VM.find 1476(top_environment observed)=VM.find 1521(top_environment observed) /\
 VM.find 1519(top_environment observed)=Some(Gval(Fuint 1)[::true]) /\ VM.find 1523(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset Lane Instruction Load Rs1 Immediate Address.
 eapply(memory_request_load_width_observed memory inputs k observed instruction lane rs1 immediate);[exact Observe|exact Legal|exact Reset|exact Lane|exact Instruction|exact Load|exact Rs1|exact Immediate|].
 eapply(memory_load_actual_address_aligned memory inputs k observed instruction lane _ Observe Legal Reset Lane Instruction Load);[|exact Address].
 unfold reference_load_address. rewrite size_take size_from_N;reflexivity.
Qed.
