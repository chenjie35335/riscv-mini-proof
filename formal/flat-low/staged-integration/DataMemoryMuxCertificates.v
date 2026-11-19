Require Import CoreSocModel ComparisonNodes ConcreteDataReaderMux ConcreteMemoryRead X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeConcreteEvaluation.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_memory_mux_expr_9187 : hfexpr VarOrder.T := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 9185)) (@Eref VarOrder.T (@Eid VarOrder.T 38)) (data_reader_expression 2).
Definition data_memory_mux_expr_9195 : hfexpr VarOrder.T := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 9193)) (@Eref VarOrder.T (@Eid VarOrder.T 38)) (data_reader_expression 3).
Definition data_memory_mux_expr_9203 : hfexpr VarOrder.T := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 9201)) (@Eref VarOrder.T (@Eid VarOrder.T 38)) (data_reader_expression 4).
Definition data_memory_mux_expr_9211 : hfexpr VarOrder.T := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 9209)) (@Eref VarOrder.T (@Eid VarOrder.T 38)) (data_reader_expression 5).
Definition data_memory_mux_offsets : seq nat := [::10016%nat;7%nat;7%nat;7%nat].
Definition data_memory_mux_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(9187,data_memory_mux_expr_9187);(9195,data_memory_mux_expr_9195);(9203,data_memory_mux_expr_9203);(9211,data_memory_mux_expr_9211)].
Lemma data_memory_mux_positions : select_node_offsets data_memory_mux_offsets flat_statements = Some data_memory_mux_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma data_memory_mux_safety : selected_node_safety flat_memories flat_statements data_memory_mux_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem data_memory_mux_output_9187 inputs path old current result values address width :
 VM.find 9179 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 read_memory_port_field old 9178 2 1 = Some (Gval (Fuint 1) [::true]) ->
 read_memory_port_field old 9178 2 0 = Some (Gval (Fuint width) address) ->
 (exists ground bits, VM.find 9185 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 38 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9187 result = Some (Gval ground bits).
Proof.
 intros Storage Concrete Enable Address [cg [cb Condition]] [sg [sb Source]] Step.
 eapply (selected_node_from_concrete_evaluation data_memory_mux_offsets flat_statements data_memory_mux_nodes 9187 data_memory_mux_expr_9187 inputs path flat_memories old current result).
 - exact data_memory_mux_positions.
 - exact data_memory_mux_safety.
 - apply (@List.nth_error_In _ data_memory_mux_nodes 0 (9187,data_memory_mux_expr_9187)). vm_compute. reflexivity.
 - intros location value Eval. unfold data_memory_mux_expr_9187 in Eval.
   eapply data_reader_mux_concrete; [|exact Storage|exact Concrete|exact Enable|exact Address|exact Condition|exact Source|exact Eval].
   do 1 right. left. reflexivity.
 - exact Step.
Qed.
Theorem data_memory_mux_output_9195 inputs path old current result values address width :
 VM.find 9179 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 read_memory_port_field old 9178 3 1 = Some (Gval (Fuint 1) [::true]) ->
 read_memory_port_field old 9178 3 0 = Some (Gval (Fuint width) address) ->
 (exists ground bits, VM.find 9193 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 38 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9195 result = Some (Gval ground bits).
Proof.
 intros Storage Concrete Enable Address [cg [cb Condition]] [sg [sb Source]] Step.
 eapply (selected_node_from_concrete_evaluation data_memory_mux_offsets flat_statements data_memory_mux_nodes 9195 data_memory_mux_expr_9195 inputs path flat_memories old current result).
 - exact data_memory_mux_positions.
 - exact data_memory_mux_safety.
 - apply (@List.nth_error_In _ data_memory_mux_nodes 1 (9195,data_memory_mux_expr_9195)). vm_compute. reflexivity.
 - intros location value Eval. unfold data_memory_mux_expr_9195 in Eval.
   eapply data_reader_mux_concrete; [|exact Storage|exact Concrete|exact Enable|exact Address|exact Condition|exact Source|exact Eval].
   do 2 right. left. reflexivity.
 - exact Step.
Qed.
Theorem data_memory_mux_output_9203 inputs path old current result values address width :
 VM.find 9179 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 read_memory_port_field old 9178 4 1 = Some (Gval (Fuint 1) [::true]) ->
 read_memory_port_field old 9178 4 0 = Some (Gval (Fuint width) address) ->
 (exists ground bits, VM.find 9201 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 38 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9203 result = Some (Gval ground bits).
Proof.
 intros Storage Concrete Enable Address [cg [cb Condition]] [sg [sb Source]] Step.
 eapply (selected_node_from_concrete_evaluation data_memory_mux_offsets flat_statements data_memory_mux_nodes 9203 data_memory_mux_expr_9203 inputs path flat_memories old current result).
 - exact data_memory_mux_positions.
 - exact data_memory_mux_safety.
 - apply (@List.nth_error_In _ data_memory_mux_nodes 2 (9203,data_memory_mux_expr_9203)). vm_compute. reflexivity.
 - intros location value Eval. unfold data_memory_mux_expr_9203 in Eval.
   eapply data_reader_mux_concrete; [|exact Storage|exact Concrete|exact Enable|exact Address|exact Condition|exact Source|exact Eval].
   do 3 right. left. reflexivity.
 - exact Step.
Qed.
Theorem data_memory_mux_output_9211 inputs path old current result values address width :
 VM.find 9179 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 read_memory_port_field old 9178 5 1 = Some (Gval (Fuint 1) [::true]) ->
 read_memory_port_field old 9178 5 0 = Some (Gval (Fuint width) address) ->
 (exists ground bits, VM.find 9209 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 38 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists ground bits, VM.find 9211 result = Some (Gval ground bits).
Proof.
 intros Storage Concrete Enable Address [cg [cb Condition]] [sg [sb Source]] Step.
 eapply (selected_node_from_concrete_evaluation data_memory_mux_offsets flat_statements data_memory_mux_nodes 9211 data_memory_mux_expr_9211 inputs path flat_memories old current result).
 - exact data_memory_mux_positions.
 - exact data_memory_mux_safety.
 - apply (@List.nth_error_In _ data_memory_mux_nodes 3 (9211,data_memory_mux_expr_9211)). vm_compute. reflexivity.
 - intros location value Eval. unfold data_memory_mux_expr_9211 in Eval.
   eapply data_reader_mux_concrete; [|exact Storage|exact Concrete|exact Enable|exact Address|exact Condition|exact Source|exact Eval].
   do 4 right. left. reflexivity.
 - exact Step.
Qed.
Print Assumptions data_memory_mux_output_9211.
