Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceLoadSemantics.
From Coq Require Import ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition alu_address_expr_1156 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1153))).
Definition alu_address_expr_1157 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bsub (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Definition alu_address_expr_1158 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 1157))).
Definition alu_address_expr_1159 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1156)) (@Eref VarOrder.T (@Eid VarOrder.T 1158)) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Definition alu_address_expr_1160 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 1151)) (@Eref VarOrder.T (@Eid VarOrder.T 1159))).
Definition alu_address_expr_1161 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 1160))).
Definition alu_address_expr_7820 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 86)) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition alu_address_expr_7821 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7820)) (@Eref VarOrder.T (@Eid VarOrder.T 7816)) (@Eref VarOrder.T (@Eid VarOrder.T 7749))).
Definition alu_address_expr_7822 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 87)) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition alu_address_expr_7823 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7822)) (@Eref VarOrder.T (@Eid VarOrder.T 7819)) (@Eref VarOrder.T (@Eid VarOrder.T 1308))).
Definition alu_address_nodes := [::(1156,alu_address_expr_1156);(1157,alu_address_expr_1157);(1158,alu_address_expr_1158);(1159,alu_address_expr_1159);(1160,alu_address_expr_1160);(1161,alu_address_expr_1161);(7820,alu_address_expr_7820);(7821,alu_address_expr_7821);(7822,alu_address_expr_7822);(7823,alu_address_expr_7823)].
Definition alu_address_offsets := [::1231%nat;0%nat;0%nat;0%nat;0%nat;0%nat;7089%nat;0%nat;0%nat;0%nat].
Lemma alu_address_positions : select_node_offsets alu_address_offsets flat_statements = Some alu_address_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma alu_address_safety : selected_node_safety flat_memories flat_statements alu_address_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Actual ALU address proofs. *)
Theorem alu_address_add_history invalid s0 s1 s2 left right :
 VM.find 1151 s0 = Some (Gval (Fuint 32) left) ->
 VM.find 1159 s0 = Some (Gval (Fuint 32) right) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 1161 s2 = Some (Gval (Fuint 32) (reference_load_address left right)).
Proof.
 intros Left Right S1 S2.
 assert (Sum : VM.find 1160 s1 = Some (Gval (Fuint 33) (from_N 33 (to_N left + to_N right)))).
 { eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 1160 alu_address_expr_1160);
 [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 4%nat);reflexivity| |exact S1].
 intros site. cbn [alu_address_expr_1160 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left Right. reflexivity. }
 eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 1161 alu_address_expr_1161);
 [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 5%nat);reflexivity| |exact S2].
 intros site. cbn [alu_address_expr_1161 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Sum. reflexivity.
Qed.
Theorem alu_address_select_add invalid s0 s1 s2 right unused :
 size right = 32%nat ->
 VM.find 1153 s0 = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 VM.find 1152 s1 = Some (Gval (Fuint 32) right) ->
 VM.find 1158 s1 = Some (Gval (Fuint 32) unused) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 1159 s2 = Some (Gval (Fuint 32) right).
Proof.
 intros Size Mode Right Unused S1 S2.
 assert (Guard : VM.find 1156 s1 = Some (Gval (Fuint 1) [::false])).
 { eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 1156 alu_address_expr_1156);
 [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 0%nat);reflexivity| |exact S1].
 intros site. cbn [alu_address_expr_1156 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode. reflexivity. }
 eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 1159 alu_address_expr_1159);
 [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 3%nat);reflexivity| |exact S2].
 intros site. cbn [alu_address_expr_1159 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Guard Right Unused. cbn [is_zero]. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite Unused Right.
 change (is_zero [::false]) with true.
 cbn [option_map make_ftype_explicit extend_hvalue_as_type type_of_val ftype_mux fgtyp_mux adapt_hvalue_as_type].
 rewrite maxnn -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Theorem alu_address_negated_type invalid s0 s1 s2 right :
 VM.find 1152 s0 = Some (Gval (Fuint 32) right) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 exists unused, VM.find 1158 s2 = Some (Gval (Fuint 32) unused).
Proof.
 intros Right S1 S2.
 assert (Neg : exists word, VM.find 1157 s1 = Some (Gval (Fuint 33) word)).
 { eexists. eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 1157 alu_address_expr_1157);
 [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 1%nat);reflexivity| |exact S1].
 intros site. cbn [alu_address_expr_1157 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Right. reflexivity. }
 destruct Neg as [word Neg]. eexists.
 eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 1158 alu_address_expr_1158);
 [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 2%nat);reflexivity| |exact S2].
 intros site. cbn [alu_address_expr_1158 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Neg. reflexivity.
Qed.
Theorem alu_address_add_from_inputs invalid history left right :
 size right = 32%nat ->
 VM.find 1152 (history 0%nat) = Some (Gval (Fuint 32) right) ->
 VM.find 1153 (history 1%nat) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 VM.find 1152 (history 2%nat) = Some (Gval (Fuint 32) right) ->
 VM.find 1151 (history 3%nat) = Some (Gval (Fuint 32) left) ->
 (forall i, (i < 5)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 1161 (history 5%nat) = Some (Gval (Fuint 32) (reference_load_address left right)).
Proof.
 intros Size Right0 Mode Right2 Left Steps.
 destruct (alu_address_negated_type invalid (history 0%nat) (history 1%nat) (history 2%nat) right Right0 (Steps 0%nat ltac:(lia)) (Steps 1%nat ltac:(lia))) as [unused Neg].
 pose proof (alu_address_select_add invalid (history 1%nat) (history 2%nat) (history 3%nat) right unused Size Mode Right2 Neg (Steps 1%nat ltac:(lia)) (Steps 2%nat ltac:(lia))) as Selected.
 exact (alu_address_add_history invalid (history 3%nat) (history 4%nat) (history 5%nat) left right Left Selected (Steps 3%nat ltac:(lia)) (Steps 4%nat ltac:(lia))).
Qed.
Theorem alu_address_input_muxes invalid before after rs1 rs2 pc immediate :
 size rs1 = 32%nat -> size immediate = 32%nat ->
 VM.find 7820 before = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7822 before = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7816 before = Some (Gval (Fuint 32) rs1) ->
 VM.find 7819 before = Some (Gval (Fuint 32) rs2) ->
 VM.find 7749 before = Some (Gval (Fuint 32) pc) ->
 VM.find 1308 before = Some (Gval (Fuint 32) immediate) ->
 formal_value_iter invalid flat_memories before false before flat_statements = Some after ->
 VM.find 7821 after = Some (Gval (Fuint 32) rs1) /\
 VM.find 7823 after = Some (Gval (Fuint 32) immediate).
Proof.
 intros RsSize ImmSize A B Rs1 Rs2 Pc Imm Step. split.
 - eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 7821 alu_address_expr_7821);
   [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 7%nat);reflexivity| |exact Step].
   intros site. cbn [alu_address_expr_7821 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite A Rs1 Pc.
   unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Rs1 Pc.
   change (is_zero [::true]) with false.
   cbn [option_map make_ftype_explicit extend_hvalue_as_type type_of_val ftype_mux fgtyp_mux adapt_hvalue_as_type].
   rewrite maxnn -RsSize take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
 - eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 7823 alu_address_expr_7823);
   [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 9%nat);reflexivity| |exact Step].
   intros site. cbn [alu_address_expr_7823 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite B Rs2 Imm.
   unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Rs2 Imm.
   change (is_zero [::false]) with true.
   cbn [option_map make_ftype_explicit extend_hvalue_as_type type_of_val ftype_mux fgtyp_mux adapt_hvalue_as_type].
   rewrite maxnn -ImmSize take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Require Import DataAddressConnectionCertificates FormalDeclaredConnection RFWritebackSelection.
Theorem alu_address_input_connections invalid before after left right :
 size left = 32%nat -> size right = 32%nat ->
 VM.find 7821 before = Some (Gval (Fuint 32) left) ->
 VM.find 7823 before = Some (Gval (Fuint 32) right) ->
 formal_value_iter invalid flat_memories before false before flat_statements = Some after ->
 VM.find 1151 after = Some (Gval (Fuint 32) left) /\
 VM.find 1152 after = Some (Gval (Fuint 32) right).
Proof.
 intros LeftSize RightSize Left Right Step. split.
 - eapply (declared_connection_value 1226 flat_statements data_address_connection_1151_decl data_address_connection_1151_mid data_address_connection_1151_tail 1151 7821 32 (Gval (Fuint 32) left));
 [exact data_address_connection_1151_position|exact data_address_connection_1151_split|exact data_address_connection_1151_straight|exact data_address_connection_1151_mid_safe|exact data_address_connection_1151_tail_safe|exact data_address_connection_1151_nonregister|reflexivity|exact Left|apply rf_load_adapt32; exact LeftSize|exact Step].
 - eapply (declared_connection_value 1227 flat_statements data_address_connection_1152_decl data_address_connection_1152_mid data_address_connection_1152_tail 1152 7823 32 (Gval (Fuint 32) right));
 [exact data_address_connection_1152_position|exact data_address_connection_1152_split|exact data_address_connection_1152_straight|exact data_address_connection_1152_mid_safe|exact data_address_connection_1152_tail_safe|exact data_address_connection_1152_nonregister|reflexivity|exact Right|apply rf_load_adapt32; exact RightSize|exact Step].
Qed.
Theorem alu_address_input_guards invalid before after :
 VM.find 86 before = Some (Gval (Fuint 1) [::true]) ->
 VM.find 87 before = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories before false before flat_statements = Some after ->
 VM.find 7820 after = Some (Gval (Fuint 1) [::true]) /\
 VM.find 7822 after = Some (Gval (Fuint 1) [::false]).
Proof.
 intros A B Step. split.
 - eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 7820 alu_address_expr_7820);
   [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 6%nat);reflexivity| |exact Step].
   intros site. cbn [alu_address_expr_7820 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite A. reflexivity.
 - eapply (reference_redirect_ground_step alu_address_offsets alu_address_nodes 7822 alu_address_expr_7822);
   [exact alu_address_positions|exact alu_address_safety|apply (List.nth_error_In alu_address_nodes 8%nat);reflexivity| |exact Step].
   intros site. cbn [alu_address_expr_7822 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite B. reflexivity.
Qed.
Theorem alu_address_inputs_history invalid s0 s1 s2 s3 rs1 rs2 pc immediate :
 size rs1 = 32%nat -> size immediate = 32%nat ->
 VM.find 86 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 87 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7816 s1 = Some (Gval (Fuint 32) rs1) ->
 VM.find 7819 s1 = Some (Gval (Fuint 32) rs2) ->
 VM.find 7749 s1 = Some (Gval (Fuint 32) pc) ->
 VM.find 1308 s1 = Some (Gval (Fuint 32) immediate) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 1151 s3 = Some (Gval (Fuint 32) rs1) /\
 VM.find 1152 s3 = Some (Gval (Fuint 32) immediate).
Proof.
 intros RsSize ImmSize A B Rs1 Rs2 Pc Imm S1 S2 S3.
 destruct (alu_address_input_guards invalid s0 s1 A B S1) as [GA GB].
 destruct (alu_address_input_muxes invalid s1 s2 rs1 rs2 pc immediate RsSize ImmSize GA GB Rs1 Rs2 Pc Imm S2) as [Left Right].
 exact (alu_address_input_connections invalid s2 s3 rs1 immediate RsSize ImmSize Left Right S3).
Qed.
