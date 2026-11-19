Require Import RegisterInvariants ScalarNodeFrames ScalarSinkTypes InstructionPortConnection.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma instruction_address_connection_typed mm old current result address enable clock mask data :
 VM.find 9176 current = Some (instruction_port_bundle address enable clock mask data) ->
 type_of_val address = Gtyp (Fuint 16) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 0)
 (@Eid VarOrder.T 9219) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fuint 16) /\
 VM.find 9176 result = Some (instruction_port_bundle written enable clock mask data).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [instruction_port_bundle option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9219) old old) as [source|]; [|discriminate Connect].
 cbn in Connect.
 destruct (adapt_hvalue_as_type source (Gtyp (Fuint 16))) as [written|] eqn:Adapt; [|discriminate Connect].
 pose proof (adapted_uint_is_passive source 16 written Adapt) as Passive.
 cbn [instruction_port_bundle repl_val_part convert_to_bundle_value option_map] in Connect.
 rewrite (passive_sink_replaced address written Passive) in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result. exists written. split.
 - exact (adapted_uint_result_type source 16 written Adapt).
 - rewrite RegisterMapFacts.find_add_neq; [|discriminate].
   rewrite (RegisterMapFacts.find_add_eq (eqxx 9176)). reflexivity.
Qed.
Print Assumptions instruction_address_connection_typed.
Lemma adapted_clock_properties source written :
 adapt_hvalue_as_type source (Gtyp Fclock) = Some written ->
 type_of_val written = Gtyp Fclock /\ is_passive_value written.
Proof.
 destruct source as [ground bits|element array|bundle|t|t|t];
 cbn [adapt_hvalue_as_type]; intro Adapt; try discriminate Adapt.
 - destruct ground; try discriminate Adapt; inversion Adapt; split; reflexivity.
 - destruct (ftype_mux false t (Gtyp Fclock)); inversion Adapt; split; reflexivity.
 - destruct (ftype_mux false t (Gtyp Fclock)); inversion Adapt; split; reflexivity.
 - destruct (ftype_mux false t (Gtyp Fclock)); inversion Adapt; split; reflexivity.
Qed.
Lemma instruction_clock_connection_typed mm old current result address enable clock mask data :
 VM.find 9176 current = Some (instruction_port_bundle address enable clock mask data) ->
 type_of_val clock = Gtyp (Fclock) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 2)
 (@Eid VarOrder.T 0) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fclock) /\
 VM.find 9176 result = Some (instruction_port_bundle address enable written mask data).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [instruction_port_bundle option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 0) old old) as [source|]; [|discriminate Connect].
 cbn in Connect.
 destruct (adapt_hvalue_as_type source (Gtyp (Fclock))) as [written|] eqn:Adapt; [|discriminate Connect].
 destruct (adapted_clock_properties source written Adapt) as [WrittenType Passive].
 cbn [instruction_port_bundle repl_val_part convert_to_bundle_value option_map] in Connect.
 rewrite (passive_sink_replaced clock written Passive) in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result. exists written. split.
 - exact WrittenType.
 - rewrite RegisterMapFacts.find_add_neq; [|discriminate].
   rewrite (RegisterMapFacts.find_add_eq (eqxx 9176)). reflexivity.
Qed.
Print Assumptions instruction_clock_connection_typed.
