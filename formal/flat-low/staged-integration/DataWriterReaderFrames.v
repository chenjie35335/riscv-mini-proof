Require Import DataReaderEnableConnections RegisterInvariants MemoryWriteFrames ComparisonNodes DataMemoryConcrete.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma data_writer_bundle_preserves_readers invalid site mm old current result field rhs p2 p3 p4 p5 p1 p0 :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 p0) ->
 formal_connect_bundle invalid site mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) field)
 rhs old current = Some result ->
 exists updated, VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 updated).
Proof.
 intros Lookup Step. unfold formal_connect_bundle in Step.
 cbn [HiF.base_ref] in Step. rewrite Lookup in Step.
 destruct (eval_type_of_ref (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) field) current) as [typ|]; [|discriminate Step].
 destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid) site mm rhs old old) as [value|]; [|discriminate Step].
 destruct (adapt_hvalue_as_type value typ) as [written|]; [|discriminate Step].
 cbn [repl_val_part data_ports convert_to_bundle_value option_map] in Step.
 cbn in Step.
 repeat match type of Step with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Step; try discriminate Step
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Step; try discriminate Step
 end.
 repeat match goal with
 | H : option_map ?f ?scrut = Some ?value |- _ =>
   destruct scrut eqn:?; [cbn [option_map] in H; inversion H; subst; clear H|discriminate H]
 end.
 inversion Step; subst result.
 eexists. rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_writer_bundle_preserves_readers.
Lemma data_write_preserves_port_bundle phase old current result value :
 write_memory_data flat_memories 9178 0 value phase old current = Some result ->
 VM.find 9178 result = VM.find 9178 current.
Proof.
 intro Write. eapply write_memory_preserves_other; [|exact Write].
 unfold memory_storage_disjoint. rewrite data_memory_layout_exact. reflexivity.
Qed.
Theorem data_writer_connection_preserves_readers invalid site phase old current result field rhs p2 p3 p4 p5 p1 p0 :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 p0) ->
 formal_connect invalid site flat_memories phase
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) field)
 rhs old current = Some result ->
 exists updated, VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 updated).
Proof.
 intros Lookup Step. unfold formal_connect in Step.
 destruct (is_memory_data_port true flat_memories 9178 0 field).
 - destruct (formal_connect_bundle invalid site flat_memories
   (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) field)
   rhs old current) as [middle|] eqn:Bundle; [|discriminate Step].
   destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories rhs old old)
   as [value|]; [|discriminate Step].
   rewrite (data_write_preserves_port_bundle phase old middle result value Step).
   exact (data_writer_bundle_preserves_readers invalid site flat_memories old current middle field rhs p2 p3 p4 p5 p1 p0 Lookup Bundle).
 - exact (data_writer_bundle_preserves_readers invalid site flat_memories old current result field rhs p2 p3 p4 p5 p1 p0 Lookup Step).
Qed.
Print Assumptions data_writer_connection_preserves_readers.
