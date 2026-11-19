Require Import FormalUIntObservation ScalarSinkTypes RegisterInvariants ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalNodeEquation.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem formal_register_mux_observation count stmts declared_tail middle tail
 (node : VarOrder.T) reg cond yes no invalid mm old set_regs current result old_value width :
 straight_drop count stmts = Some (Qcons (Sreg node reg) declared_tail) ->
 declared_tail = statement_append middle (Qcons (Sfcnct (Eid node) (Emux cond yes no)) tail) ->
 straight_statements middle -> formal_typed_suffix_safe mm node middle ->
 formal_typed_suffix_safe mm node tail ->
 VM.find node old = Some old_value -> type_of_val old_value = Gtyp (Fuint width) ->
 formal_statements invalid nil 0 mm old set_regs current stmts = Some result ->
 exists source value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address nil (S (0 + count) + statement_count middle) 0 nil) mm (Emux cond yes no) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint width)) = Some value /\ VM.find node result = Some value.
Proof.
 intros Position Split Straight MiddleSafe TailSafe OldValue Typed Statements.
 destruct (formal_straight_prefix count stmts _ invalid nil 0 mm old set_regs current result Position Statements)
 as [at_declaration Decl].
 cbn [formal_statements] in Decl. rewrite OldValue Split in Decl.
 destruct (successful_straight_segment middle _ invalid nil (S (0 + count)) mm old set_regs
 (VM.add node old_value at_declaration) result Straight Decl) as [at_connection [Middle Connection]].
 assert (Before : VM.find node at_connection = Some old_value).
 { eapply formal_typed_suffix_preserves_value; [exact MiddleSafe|exact Typed| |exact Middle].
   apply RegisterMapFacts.find_add_eq. exact (eqxx node). }
 cbn [formal_statements is_memory_writer_ref] in Connection.
 destruct (formal_connect invalid (validif_raw_address nil (S (0 + count) + statement_count middle) 0 nil) mm set_regs (Eid node) (Emux cond yes no) old at_connection)
 as [next|] eqn:Connect; [|discriminate Connection].
 destruct (formal_uint_observation invalid (validif_raw_address nil (S (0 + count) + statement_count middle) 0 nil) mm set_regs node (Emux cond yes no) old at_connection next old_value width
 Before Typed Connect) as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 eapply formal_typed_suffix_preserves_value;
 [exact TailSafe|eapply adapted_uint_result_type; exact Adapt|exact Value|exact Connection].
Qed.
Print Assumptions formal_register_mux_observation.
