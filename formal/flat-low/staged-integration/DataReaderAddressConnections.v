Require Import RegisterInvariants ScalarNodeFrames ScalarSinkTypes DataReaderEnableConnections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma data_reader_address_typed_1 mm old current result p2 p3 p4 p5 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 0)
 (@Eid VarOrder.T 9221) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fuint 16) /\
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 (data_port_fields written enable clock mask data) p0).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9221) old old) as [source|]; [|discriminate Connect].
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
Print Assumptions data_reader_address_typed_1.
Lemma data_reader_address_typed_2 mm old current result p3 p4 p5 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports (data_port_fields address enable clock mask data) p3 p4 p5 p1 p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 2) 0)
 (@Eid VarOrder.T 9186) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fuint 16) /\
 VM.find 9178 result = Some (data_ports (data_port_fields written enable clock mask data) p3 p4 p5 p1 p0).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9186) old old) as [source|]; [|discriminate Connect].
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
Print Assumptions data_reader_address_typed_2.
Lemma data_reader_address_typed_3 mm old current result p2 p4 p5 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 (data_port_fields address enable clock mask data) p4 p5 p1 p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 3) 0)
 (@Eid VarOrder.T 9194) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fuint 16) /\
 VM.find 9178 result = Some (data_ports p2 (data_port_fields written enable clock mask data) p4 p5 p1 p0).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9194) old old) as [source|]; [|discriminate Connect].
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
Print Assumptions data_reader_address_typed_3.
Lemma data_reader_address_typed_4 mm old current result p2 p3 p5 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 (data_port_fields address enable clock mask data) p5 p1 p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 4) 0)
 (@Eid VarOrder.T 9202) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fuint 16) /\
 VM.find 9178 result = Some (data_ports p2 p3 (data_port_fields written enable clock mask data) p5 p1 p0).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9202) old old) as [source|]; [|discriminate Connect].
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
Print Assumptions data_reader_address_typed_4.
Lemma data_reader_address_typed_5 mm old current result p2 p3 p4 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 (data_port_fields address enable clock mask data) p1 p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 5) 0)
 (@Eid VarOrder.T 9210) old current = Some result ->
 exists written, type_of_val written = Gtyp (Fuint 16) /\
 VM.find 9178 result = Some (data_ports p2 p3 p4 (data_port_fields written enable clock mask data) p1 p0).
Proof.
 intros Lookup Typed Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 destruct (eval_href_with_memory mm (@Eid VarOrder.T 9210) old old) as [source|]; [|discriminate Connect].
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
Print Assumptions data_reader_address_typed_5.
