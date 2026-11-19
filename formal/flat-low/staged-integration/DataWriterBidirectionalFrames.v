Require Import DataReaderEnableConnections RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma writer_field_replacement_preserves_readers field replace old value result p2 p3 p4 p5 p1 p0 :
 repl_val_part (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) field)
 replace (data_ports p2 p3 p4 p5 p1 p0) value old = Some result ->
 exists updated, result = data_ports p2 p3 p4 p5 p1 updated.
Proof.
 intro Step. cbn [repl_val_part data_ports convert_to_bundle_value option_map] in Step. cbn in Step.
 repeat match goal with
 | H : option_map ?f ?scrut = Some ?value |- _ =>
   destruct scrut eqn:?; [cbn [option_map] in H; inversion H; subst; clear H|discriminate H]
 end.
 eexists. reflexivity.
Qed.
Theorem data_writer_bidirectional_preserves_readers mm old current result field source p2 p3 p4 p5 p1 p0 :
 9178 != source ->
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 p0) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) field)
 (@Eid VarOrder.T source) old current = Some result ->
 exists updated, VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 updated).
Proof.
 intros Different Lookup Step. unfold bidirectional_connect_with_memory in Step.
 cbn [HiF.base_ref] in Step. rewrite Lookup in Step.
 destruct (eval_type_of_ref (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) field) current) as [typ|]; [|discriminate Step].
 destruct (eval_href_with_memory mm (@Eid VarOrder.T source) old old) as [value|]; [|discriminate Step].
 destruct (adapt_hvalue_as_type value typ) as [written|]; [|discriminate Step].
 destruct (repl_val_part (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) field)
 (replace_writeable Sink) (data_ports p2 p3 p4 p5 p1 p0) written old) as [changed|] eqn:Replace; [|discriminate Step].
 destruct (writer_field_replacement_preserves_readers field (replace_writeable Sink) old written changed p2 p3 p4 p5 p1 p0 Replace)
 as [updated Changed]. subst changed.
 cbn [option_map] in Step.
 repeat match type of Step with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Step; try discriminate Step
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Step; try discriminate Step
 end.
 inversion Step; subst result. exists updated.
 rewrite RegisterMapFacts.find_add_neq; [|exact (elimT negP Different)].
 apply RegisterMapFacts.find_add_eq. reflexivity.
Qed.
Print Assumptions data_writer_bidirectional_preserves_readers.
