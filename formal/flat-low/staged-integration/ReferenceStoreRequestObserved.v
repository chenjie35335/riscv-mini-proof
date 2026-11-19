Require Import CoreSocModel ComparisonNodes ReferenceStoreRequestData ReferenceRedirectSpine DUTRedirectDecode FormalDeclaredWireCheck FormalObservedHistory FormalLocalHistory ReferenceControlStabilityHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma reference_store_request_word_size guards word :size(reference_store_request_word guards word)=32%nat.
Proof. unfold reference_store_request_word. repeat match goal with |- context[if ?b then _ else _]=>destruct b end;try reflexivity;apply reference_store_request_piece_size. Qed.
Theorem reference_store_request_alias_history invalid history limit start word :size word=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7115(history t)=Some(Gval(Fuint 32)word)) ->
 forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1526(history t)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Steps Source [|[|[|t]]] Lower Upper;try lia.
 eapply declared_wire_checked_value;[exact reference_store_request_wire_1526| |apply dut_decode_adapt;exact Size|apply Steps;lia].
 change(VM.find 1716(history(S(S t)))=Some(Gval(Fuint 32)word)).
 eapply declared_wire_checked_value;[exact reference_store_request_wire_1716| |apply dut_decode_adapt;exact Size|apply Steps;lia].
 eapply(reference_redirect_ground_step reference_store_request_data_offsets reference_store_request_data_nodes 7190 (@Eref VarOrder.T(@Eid VarOrder.T 7115)));
 [exact reference_store_request_data_positions|exact reference_store_request_data_safety|apply(List.nth_error_In reference_store_request_data_nodes 7%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site;cbn[eval_hfexpr_validif_policy eval_href_validif_policy];apply Source;lia.
Qed.
Theorem reference_store_request_data_observed memory inputs k observed guards word :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)word) ->
 (forall node,List.In node reference_store_request_data_guards ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::guards node])) ->
 VM.find 1526(top_environment observed)=Some(Gval(Fuint 32)(reference_store_request_word guards word)).
Proof.
 intros Observe Legal Source Guards.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Sources:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 2804(history t)=Some(Gval(Fuint 32)word)).
 { intros t Lower Upper. rewrite(reference_control_stable_2804_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259 ltac:(lia)ltac:(lia)Upper ltac:(lia))Last. exact Source. }
 assert(AllGuards:forall node t,List.In node reference_store_request_data_guards ->(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::guards node])).
 { intros node t Member Lower Upper. assert(Same:VM.find node(history t)=VM.find node(history 9259%nat)).
 { cbn[reference_store_request_data_guards List.In]in Member. repeat destruct Member as[<-|Member];try contradiction.
 - apply(reference_control_stable_1951_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259);lia.
 - apply(reference_control_stable_2723_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259);lia.
 - apply(reference_control_stable_1946_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259);lia.
 - apply(reference_control_stable_2708_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259);lia.
 - apply(reference_control_stable_1941_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259);lia.
 - apply(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259);lia. }
 rewrite Same Last;apply Guards;exact Member. }
 rewrite <-Last. eapply(reference_store_request_alias_history _ history 9259 208);[apply reference_store_request_word_size|exact Steps| |vm_compute;lia|vm_compute;lia].
 intros t Lower Upper. exact(reference_store_request_data_history _ history 9259 200 guards word Steps Sources AllGuards t Lower Upper).
Qed.
Require Import ReferenceStoreData MemoryRequestObservedSemantics ReferenceMemoryAlignment ReferenceRequestSpine StoreTypeCorrespondence ReferenceStoreRs1 ReferenceStoreRs2 ReferenceStoreObserved ReferenceStoreParts StoreReferenceAlignment RFReadPorts RFReferenceNopHistory.
Definition reference_store_request_aligned lane address :=
 match lane with O=>negb(nth false address 0 || nth false address 1)|S O=>negb(nth false address 0)|_=>true end.
Lemma reference_store_request_word_selected instruction lane address word :
 (lane<3)%coq_nat ->store_type_is_store instruction lane ->reference_store_request_aligned lane address=true ->
 reference_store_request_word(memory_request_observed_guards instruction true address)word=
 reference_store_request_piece(reference_store_data_width lane)word.
Proof.
 intros Lane Store Aligned. unfold store_type_is_store in Store.
 unfold reference_store_request_word,memory_request_observed_guards,memory_reference_instruction.
 rewrite Store. do 3(destruct lane as[|lane];[cbn[store_type_lane_code reference_store_data_width nth N.eqb Pos.eqb Nat.eqb orb reference_alignment_test reference_store_request_aligned]in *;rewrite ?Aligned;reflexivity|]). lia.
Qed.
Theorem reference_store_request_data_bank_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 reference_store_request_aligned lane(store_reference_address bank instruction)=true ->
 VM.find 1526(top_environment observed)=Some(Gval(Fuint 32)(reference_store_request_piece(reference_store_data_width lane)(bank(to_nat(rf_instruction_address true instruction))))).
Proof.
 intros Observe Legal Reset Lane Instruction Store Bank Aligned.
 pose proof(reference_store_rs2_bank_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Store Bank)as Data.
 pose proof(store_reference_enabled_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Store)as Enabled.
 pose proof(reference_store_rs1_bank_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Store Bank)as Rs1.
 pose proof(reference_store_immediate_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Store)as Imm.
 pose proof(memory_request_all_guards_observed memory inputs k observed instruction true _ _ Observe Legal Instruction Enabled Rs1 Imm)as Guards.
 rewrite <-(reference_store_request_word_selected instruction lane(store_reference_address bank instruction)_ Lane Store Aligned).
 eapply(reference_store_request_data_observed memory inputs k observed);[exact Observe|exact Legal|exact Data|].
 intros node Member. apply Guards. cbn[reference_store_request_data_guards List.In]in Member.
 repeat destruct Member as[<-|Member];try contradiction;vm_compute;tauto.
Qed.
Lemma reference_store_request_alignment_from_address memory inputs k observed instruction half bank address :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction(if half then 1%nat else 0%nat) ->
 rf_reference_bank_at(top_environment observed)bank ->size address=32%nat ->
 VM.find 7752(top_environment observed)=Some(Gval(Fuint 32)address) ->take 2 address=take 2(store_reference_address bank instruction) ->
 reference_store_request_aligned(if half then 1%nat else 0%nat)(store_reference_address bank instruction)=true.
Proof.
 intros Observe Legal Reset Instruction Store Bank Size Address LowBits.
 pose proof(store_reference_alignment_from_address memory inputs k observed instruction half bank address Observe Legal Reset Instruction Store Bank Size Address LowBits)as Good.
 pose proof(store_reference_alignment_observed memory inputs k observed instruction half bank Observe Legal Reset Instruction Store Bank)as Normal.
 rewrite Good in Normal. pose proof(f_equal(fun value=>match value with Some(Gval _ (b::_))=>b|_=>false end)Normal)as Bits.
 destruct half;exact(Logic.eq_sym Bits).
Qed.
Theorem reference_store_request_data_from_address memory inputs k observed instruction lane bank address :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->size address=32%nat ->
 VM.find 7752(top_environment observed)=Some(Gval(Fuint 32)address) ->take 2 address=take 2(store_reference_address bank instruction) ->
 VM.find 1526(top_environment observed)=Some(Gval(Fuint 32)(reference_store_request_piece(reference_store_data_width lane)(bank(to_nat(rf_instruction_address true instruction))))).
Proof.
 intros Observe Legal Reset Lane Instruction Store Bank Size Address LowBits.
 apply(reference_store_request_data_bank_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Store Bank).
 destruct lane as[|[|[|lane]]];try lia;try reflexivity.
 - exact(reference_store_request_alignment_from_address memory inputs k observed instruction false bank address Observe Legal Reset Instruction Store Bank Size Address LowBits).
 - exact(reference_store_request_alignment_from_address memory inputs k observed instruction true bank address Observe Legal Reset Instruction Store Bank Size Address LowBits).
Qed.
