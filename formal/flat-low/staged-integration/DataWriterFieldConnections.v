Require Import RegisterInvariants ScalarNodeFrames ScalarSinkTypes DataReaderEnableConnections InstructionPortShape.
From nbits Require Import NBits.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma data_writer_address_typed mm old current result p2 p3 p4 p5 p1 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable clock mask data)) ->
 type_of_val address = Gtyp (Fuint 16) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 0)
 (@Eid VarOrder.T 9230) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fuint 16) /\
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields written enable clock mask data)).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9230) old old) as [source|]; [|discriminate Connect].
 cbn in Connect.
 destruct (adapt_hvalue_as_type source (Gtyp (Fuint 16))) as [written|] eqn:Adapt; [|discriminate Connect].
 pose proof (adapted_uint_is_passive source 16 written Adapt) as Passive.
 cbn [data_ports data_port_fields repl_val_part convert_to_bundle_value option_map] in Connect.
 rewrite (passive_sink_replaced address written Passive) in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result. exists written. split.
 - exact (adapted_uint_result_type source 16 written Adapt).
 - rewrite RegisterMapFacts.find_add_neq; [|discriminate].
   rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_writer_address_typed.
Lemma data_writer_address_concrete mm old current result p2 p3 p4 p5 p1 address enable clock mask data source_width bits :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable clock mask data)) ->
 type_of_val address = Gtyp (Fuint 16) ->
 VM.find 9230 old = Some (Gval (Fuint source_width) bits) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 0)
 (@Eid VarOrder.T 9230) old current = Some result ->
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields (Gval (Fuint 16) (zext_to 16 (take 16 bits))) enable clock mask data)).
Proof.
 intros Lookup Typed Source Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_href_with_memory] in Connect.
 rewrite Lookup Source in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value replace_writeable option_map] in Connect.
 cbn [data_ports data_port_fields] in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result.
 rewrite RegisterMapFacts.find_add_neq; [|discriminate].
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_writer_address_concrete.
Lemma data_writer_enable_typed mm old current result p2 p3 p4 p5 p1 enable address clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable clock mask data)) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 1)
 (@Eid VarOrder.T 9232) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fuint 1) /\
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address written clock mask data)).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9232) old old) as [source|]; [|discriminate Connect].
 cbn in Connect.
 destruct (adapt_hvalue_as_type source (Gtyp (Fuint 1))) as [written|] eqn:Adapt; [|discriminate Connect].
 pose proof (adapted_uint_is_passive source 1 written Adapt) as Passive.
 cbn [data_ports data_port_fields repl_val_part convert_to_bundle_value option_map] in Connect.
 rewrite (passive_sink_replaced enable written Passive) in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result. exists written. split.
 - exact (adapted_uint_result_type source 1 written Adapt).
 - rewrite RegisterMapFacts.find_add_neq; [|discriminate].
   rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_writer_enable_typed.
Lemma data_writer_enable_concrete mm old current result p2 p3 p4 p5 p1 enable address clock mask data source_width bits :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable clock mask data)) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 VM.find 9232 old = Some (Gval (Fuint source_width) bits) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 1)
 (@Eid VarOrder.T 9232) old current = Some result ->
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address (Gval (Fuint 1) (zext_to 1 (take 1 bits))) clock mask data)).
Proof.
 intros Lookup Typed Source Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_href_with_memory] in Connect.
 rewrite Lookup Source in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value replace_writeable option_map] in Connect.
 cbn [data_ports data_port_fields] in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result.
 rewrite RegisterMapFacts.find_add_neq; [|discriminate].
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_writer_enable_concrete.
Lemma data_writer_mask_typed mm old current result p2 p3 p4 p5 p1 mask enable clock address data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable clock mask data)) ->
 type_of_val mask = Gtyp (Fuint 1) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 3)
 (@Eid VarOrder.T 9233) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fuint 1) /\
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable clock written data)).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9233) old old) as [source|]; [|discriminate Connect].
 cbn in Connect.
 destruct (adapt_hvalue_as_type source (Gtyp (Fuint 1))) as [written|] eqn:Adapt; [|discriminate Connect].
 pose proof (adapted_uint_is_passive source 1 written Adapt) as Passive.
 cbn [data_ports data_port_fields repl_val_part convert_to_bundle_value option_map] in Connect.
 rewrite (passive_sink_replaced mask written Passive) in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result. exists written. split.
 - exact (adapted_uint_result_type source 1 written Adapt).
 - rewrite RegisterMapFacts.find_add_neq; [|discriminate].
   rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_writer_mask_typed.
Lemma data_writer_mask_concrete mm old current result p2 p3 p4 p5 p1 mask enable clock address data source_width bits :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable clock mask data)) ->
 type_of_val mask = Gtyp (Fuint 1) ->
 VM.find 9233 old = Some (Gval (Fuint source_width) bits) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 3)
 (@Eid VarOrder.T 9233) old current = Some result ->
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable clock (Gval (Fuint 1) (zext_to 1 (take 1 bits))) data)).
Proof.
 intros Lookup Typed Source Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_href_with_memory] in Connect.
 rewrite Lookup Source in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value replace_writeable option_map] in Connect.
 cbn [data_ports data_port_fields] in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result.
 rewrite RegisterMapFacts.find_add_neq; [|discriminate].
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_writer_mask_concrete.
Lemma data_writer_clock_typed mm old current result p2 p3 p4 p5 p1 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable clock mask data)) ->
 type_of_val clock = Gtyp (Fclock) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 2)
 (@Eid VarOrder.T 9231) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fclock) /\
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 p1 (data_port_fields address enable written mask data)).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9231) old old) as [source|]; [|discriminate Connect].
 cbn in Connect.
 destruct (adapt_hvalue_as_type source (Gtyp (Fclock))) as [written|] eqn:Adapt; [|discriminate Connect].
 destruct (adapted_clock_properties source written Adapt) as [WrittenType Passive].
 cbn [data_ports data_port_fields repl_val_part convert_to_bundle_value option_map] in Connect.
 rewrite (passive_sink_replaced clock written Passive) in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result. exists written. split.
 - exact WrittenType.
 - rewrite RegisterMapFacts.find_add_neq; [|discriminate].
   rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_writer_clock_typed.
