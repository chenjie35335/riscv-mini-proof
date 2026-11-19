Require Import RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_port_fields address enable clock mask data := Bval
 (Bflips 0 Nflip address (Bflips 1 Nflip enable (Bflips 2 Nflip clock
 (Bflips 3 Nflip mask (Bflips 4 Nflip data Bnil))))).
Definition data_ports p2 p3 p4 p5 p1 p0 := Bval
 (Bflips 2 Nflip p2 (Bflips 3 Nflip p3 (Bflips 4 Nflip p4
 (Bflips 5 Nflip p5 (Bflips 1 Nflip p1 (Bflips 0 Nflip p0 Bnil)))))).
Lemma data_reader_enable_1 invalid site mm phase old current result p2 p3 p4 p5 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) p0) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 formal_connect invalid site mm phase (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result ->
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p0).
Proof.
 intros Lookup Typed Connect.
 unfold formal_connect in Connect.
 change (formal_connect_bundle invalid site mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result) in Connect.
 unfold formal_connect_bundle in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_hfexpr_validif_policy] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value option_map] in Connect.
 inversion Connect; subst result.
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_reader_enable_1.
Lemma data_reader_enable_2 invalid site mm phase old current result p3 p4 p5 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports (data_port_fields address enable clock mask data) p3 p4 p5 p1 p0) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 formal_connect invalid site mm phase (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 2) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result ->
 VM.find 9178 result = Some (data_ports (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p3 p4 p5 p1 p0).
Proof.
 intros Lookup Typed Connect.
 unfold formal_connect in Connect.
 change (formal_connect_bundle invalid site mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 2) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result) in Connect.
 unfold formal_connect_bundle in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_hfexpr_validif_policy] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value option_map] in Connect.
 inversion Connect; subst result.
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_reader_enable_2.
Lemma data_reader_enable_3 invalid site mm phase old current result p2 p4 p5 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 (data_port_fields address enable clock mask data) p4 p5 p1 p0) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 formal_connect invalid site mm phase (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 3) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result ->
 VM.find 9178 result = Some (data_ports p2 (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p4 p5 p1 p0).
Proof.
 intros Lookup Typed Connect.
 unfold formal_connect in Connect.
 change (formal_connect_bundle invalid site mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 3) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result) in Connect.
 unfold formal_connect_bundle in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_hfexpr_validif_policy] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value option_map] in Connect.
 inversion Connect; subst result.
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_reader_enable_3.
Lemma data_reader_enable_4 invalid site mm phase old current result p2 p3 p5 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 (data_port_fields address enable clock mask data) p5 p1 p0) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 formal_connect invalid site mm phase (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 4) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result ->
 VM.find 9178 result = Some (data_ports p2 p3 (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p5 p1 p0).
Proof.
 intros Lookup Typed Connect.
 unfold formal_connect in Connect.
 change (formal_connect_bundle invalid site mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 4) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result) in Connect.
 unfold formal_connect_bundle in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_hfexpr_validif_policy] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value option_map] in Connect.
 inversion Connect; subst result.
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_reader_enable_4.
Lemma data_reader_enable_5 invalid site mm phase old current result p2 p3 p4 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 (data_port_fields address enable clock mask data) p1 p0) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 formal_connect invalid site mm phase (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 5) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result ->
 VM.find 9178 result = Some (data_ports p2 p3 p4 (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p1 p0).
Proof.
 intros Lookup Typed Connect.
 unfold formal_connect in Connect.
 change (formal_connect_bundle invalid site mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 5) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result) in Connect.
 unfold formal_connect_bundle in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_hfexpr_validif_policy] in Connect.
 rewrite Lookup in Connect.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value option_map] in Connect.
 inversion Connect; subst result.
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_reader_enable_5.
Lemma data_reader_enabled_1 env p2 p3 p4 p5 p0 address clock mask data :
 VM.find 9178 env = Some (data_ports p2 p3 p4 p5 (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p0) ->
 read_memory_port_field env 9178 1 1 = Some (Gval (Fuint 1) [::true]).
Proof.
 intro Lookup. unfold read_memory_port_field. rewrite Lookup. reflexivity.
Qed.
Lemma data_reader_enabled_2 env p3 p4 p5 p1 p0 address clock mask data :
 VM.find 9178 env = Some (data_ports (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p3 p4 p5 p1 p0) ->
 read_memory_port_field env 9178 2 1 = Some (Gval (Fuint 1) [::true]).
Proof.
 intro Lookup. unfold read_memory_port_field. rewrite Lookup. reflexivity.
Qed.
Lemma data_reader_enabled_3 env p2 p4 p5 p1 p0 address clock mask data :
 VM.find 9178 env = Some (data_ports p2 (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p4 p5 p1 p0) ->
 read_memory_port_field env 9178 3 1 = Some (Gval (Fuint 1) [::true]).
Proof.
 intro Lookup. unfold read_memory_port_field. rewrite Lookup. reflexivity.
Qed.
Lemma data_reader_enabled_4 env p2 p3 p5 p1 p0 address clock mask data :
 VM.find 9178 env = Some (data_ports p2 p3 (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p5 p1 p0) ->
 read_memory_port_field env 9178 4 1 = Some (Gval (Fuint 1) [::true]).
Proof.
 intro Lookup. unfold read_memory_port_field. rewrite Lookup. reflexivity.
Qed.
Lemma data_reader_enabled_5 env p2 p3 p4 p1 p0 address clock mask data :
 VM.find 9178 env = Some (data_ports p2 p3 p4 (data_port_fields address (Gval (Fuint 1) [::true]) clock mask data) p1 p0) ->
 read_memory_port_field env 9178 5 1 = Some (Gval (Fuint 1) [::true]).
Proof.
 intro Lookup. unfold read_memory_port_field. rewrite Lookup. reflexivity.
Qed.
