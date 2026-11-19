Require Import RegisterInvariants.
From nbits Require Import NBits.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition instruction_port_bundle address enable clock mask data :=
 Bval (Bflips 0 Nflip (Bval
 (Bflips 0 Nflip address (Bflips 1 Nflip enable (Bflips 2 Nflip clock
 (Bflips 3 Nflip mask (Bflips 4 Nflip data Bnil)))))) Bnil).
Lemma instruction_enable_connection mm phase old current result address enable clock mask data :
 VM.find 9176 current = Some (instruction_port_bundle address enable clock mask data) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 unidirectional_connect_with_memory mm phase
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result ->
 VM.find 9176 result = Some (instruction_port_bundle address (Gval (Fuint 1) [::true]) clock mask data).
Proof.
 intros Lookup Typed Connect.
 unfold unidirectional_connect_with_memory in Connect.
 change (unidirectional_connect_bundle mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result) in Connect.
 unfold unidirectional_connect_bundle in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_hfexpr_with_memory] in Connect.
 rewrite Lookup in Connect.
 cbn [instruction_port_bundle option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value option_map] in Connect.
 inversion Connect; subst result.
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9176)). reflexivity.
Qed.
Print Assumptions instruction_enable_connection.
Lemma instruction_address_connection mm old current result address enable clock mask data bits :
 VM.find 9176 current = Some (instruction_port_bundle address enable clock mask data) ->
 type_of_val address = Gtyp (Fuint 16) ->
 VM.find 9219 old = Some (Gval (Fuint 4) bits) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 0)
 (@Eid VarOrder.T 9219) old current = Some result ->
 VM.find 9176 result = Some (instruction_port_bundle (Gval (Fuint 16) (zext_to 16 (take 16 bits))) enable clock mask data).
Proof.
 intros Lookup Typed Source Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_href_with_memory] in Connect.
 rewrite Lookup Source in Connect.
 cbn [instruction_port_bundle option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value replace_writeable option_map] in Connect.
 cbn [instruction_port_bundle] in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result.
 rewrite RegisterMapFacts.find_add_neq; [|discriminate].
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9176)). reflexivity.
Qed.
Lemma instruction_clock_connection mm old current result address enable clock mask data bits :
 VM.find 9176 current = Some (instruction_port_bundle address enable clock mask data) ->
 type_of_val clock = Gtyp (Fclock) ->
 VM.find 0 old = Some (Gval (Fclock) bits) ->
 bidirectional_connect_with_memory mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 2)
 (@Eid VarOrder.T 0) old current = Some result ->
 VM.find 9176 result = Some (instruction_port_bundle address enable (Gval Fclock bits) mask data).
Proof.
 intros Lookup Typed Source Connect.
 unfold bidirectional_connect_with_memory in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_href_with_memory] in Connect.
 rewrite Lookup Source in Connect.
 cbn [instruction_port_bundle option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value replace_writeable option_map] in Connect.
 cbn [instruction_port_bundle] in Connect.
 cbn in Connect.
 repeat match type of Connect with
 | (option_map ?f ?scrut = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 | (match ?scrut with _ => _ end = _) => destruct scrut eqn:?; cbn [option_map] in Connect; try discriminate Connect
 end.
 inversion Connect; subst result.
 rewrite RegisterMapFacts.find_add_neq; [|discriminate].
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9176)). reflexivity.
Qed.
Lemma instruction_port_address env address enable clock mask data :
 VM.find 9176 env = Some (instruction_port_bundle address enable clock mask data) ->
 read_memory_port_field env 9176 0 0 = Some address.
Proof. intro Value. unfold read_memory_port_field. rewrite Value. reflexivity. Qed.
Lemma instruction_port_enable env address enable clock mask data :
 VM.find 9176 env = Some (instruction_port_bundle address enable clock mask data) ->
 read_memory_port_field env 9176 0 1 = Some enable.
Proof. intro Value. unfold read_memory_port_field. rewrite Value. reflexivity. Qed.
Print Assumptions instruction_address_connection.
Print Assumptions instruction_clock_connection.
