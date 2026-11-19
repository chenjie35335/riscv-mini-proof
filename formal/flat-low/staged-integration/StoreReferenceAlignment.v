Require Import FormalLocalHistory FormalObservedHistory CoreSocModel ComparisonNodes ReferenceStoreRs1 ReferenceStoreObserved ReferenceStoreParts ReferenceMemoryAlignment ReferenceLoadSemantics StoreTypeCorrespondence RFReadPorts RFReferenceNopHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition store_reference_address bank instruction :=
 reference_load_address (bank (to_nat (rf_instruction_address false instruction))) (store_s_immediate instruction).
Theorem store_reference_alignment_observed memory inputs k observed instruction half bank :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 store_type_is_store instruction (if half then 1%nat else 0%nat) ->
 rf_reference_bank_at (top_environment observed) bank ->
 VM.find (if half then 2723 else 2708) (top_environment observed) = Some (Gval (Fuint 1)
 [:: if half then negb (nth false (store_reference_address bank instruction) 0)
 else negb (nth false (store_reference_address bank instruction) 0 || nth false (store_reference_address bank instruction) 1)]).
Proof.
 intros Observe Legal Reset Instruction Store Bank.
 pose proof (reference_store_rs1_bank_observed memory inputs k observed instruction (if half then 1%nat else 0%nat) bank Observe Legal Reset ltac:(destruct half;lia) Instruction Store Bank) as Rs1.
 pose proof (reference_store_immediate_observed memory inputs k observed instruction (if half then 1%nat else 0%nat) Observe Legal Reset ltac:(destruct half;lia) Instruction Store) as Imm.
 pose proof (reference_alignment_observed memory inputs k observed (if half then 5%nat else 4%nat) _ _ Observe Legal ltac:(destruct half;lia) Rs1 Imm) as Align.
 destruct half;exact Align.
Qed.
Theorem store_reference_alignment_from_address memory inputs k observed instruction half bank address :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 store_type_is_store instruction (if half then 1%nat else 0%nat) ->
 rf_reference_bank_at (top_environment observed) bank ->
 size address = 32%nat ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) address) ->
 take 2 address = take 2 (store_reference_address bank instruction) ->
 VM.find (if half then 2723 else 2708) (top_environment observed) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Observe Legal Reset Instruction Store Bank Size Address LowBits.
 pose proof (store_reference_alignment_observed memory inputs k observed instruction half bank Observe Legal Reset Instruction Store Bank) as Align.
 destruct address as [|b0 [|b1 rest]];cbn in Size;try lia.
 destruct (store_instruction_aligned_observed memory inputs k observed instruction half b0 b1 rest Observe Legal Reset Size Instruction Store Address) as [Bit0 Bit1].
 assert (Low0 : nth false (store_reference_address bank instruction) 0 = b0).
 { pose proof (f_equal (fun bits => nth false bits 0) LowBits) as E. rewrite nth_take in E;[symmetry;exact E|reflexivity]. }
 assert (Low1 : nth false (store_reference_address bank instruction) 1 = b1).
 { pose proof (f_equal (fun bits => nth false bits 1) LowBits) as E. rewrite nth_take in E;[symmetry;exact E|reflexivity]. }
 rewrite Low0 Low1 Bit0 in Align. destruct half;[exact Align|]. rewrite (Bit1 (Logic.eq_refl false)) in Align. exact Align.
Qed.
