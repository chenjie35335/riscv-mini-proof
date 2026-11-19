Require Import FormalDeclaredConnection RegisterInvariants ScalarNodeFrames ScalarSinkTypes FormalStatementSegments FormalTypedNodeFrames FormalNodeEquation StagedRegisterHold FormalUIntObservation.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem unary_connection_tail_value invalid scope position mm old phase current result tail
 (node source : VarOrder.T) op width previous source_value value :
 node != source -> formal_typed_suffix_safe mm node tail ->
 VM.find node current = Some previous -> type_of_val previous = Gtyp (Fuint width) ->
 eval_hfexpr_with_memory mm (Eprim_unop op (Eref (Eid source))) old old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint width)) = Some value ->
 formal_statements invalid scope position mm old phase current
 (Qcons (Sfcnct (Eid node) (Eprim_unop op (Eref (Eid source)))) tail) = Some result ->
 VM.find node result = Some value.
Proof.
 intros Different Safe Current Typed Source Adapt Step.
 cbn [formal_statements] in Step.
 destruct (formal_connect invalid (validif_raw_address scope position 0 nil) mm phase
 (Eid node) (Eprim_unop op (Eref (Eid source))) old current) as [next|] eqn:Connect; [|discriminate Step].
 destruct (formal_uint_observation invalid (validif_raw_address scope position 0 nil) mm phase node
 (Eprim_unop op (Eref (Eid source))) old current next previous width Current Typed Connect)
 as [read [written [Read [Written Next]]]].
 change (eval_hfexpr_with_memory mm (Eprim_unop op (Eref (Eid source))) old old = Some read) in Read.
 rewrite Source in Read. inversion Read; subst read.
 rewrite Adapt in Written. inversion Written; subst written.
 eapply formal_typed_suffix_preserves_value;
 [exact Safe|eapply adapted_uint_result_type; exact Adapt|exact Next|exact Step].
Qed.
Theorem declared_unary_connection_value count stmts declared_tail middle tail
 (node source : VarOrder.T) op width source_value value invalid mm old current result :
 straight_drop count stmts = Some (Qcons (Swire node (Gtyp (Fuint width))) declared_tail) ->
 declared_tail = statement_append middle (Qcons (Sfcnct (Eid node) (Eprim_unop op (Eref (Eid source)))) tail) ->
 straight_statements middle ->
 formal_typed_suffix_safe mm node middle -> formal_typed_suffix_safe mm node tail ->
 has_register node stmts = false -> node != source ->
 eval_hfexpr_with_memory mm (Eprim_unop op (Eref (Eid source))) old old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint width)) = Some value ->
 formal_value_iter invalid mm old false current stmts = Some result ->
 VM.find node result = Some value.
Proof.
 intros Position Split Straight MiddleSafe TailSafe Nonregister Different Source Adapt Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid [::] 0 mm old false current stmts) as [proposed|] eqn:Statements;
 [|discriminate Step].
 rewrite (staged_finish_false_equal stmts invalid [::] 0 mm old proposed
   (fun e => eval_hfexpr_with_memory mm e old old)) in Step.
 pose proof (finish_registers_preserves_nonregister stmts _ old false proposed result node Nonregister Step) as Projection.
 destruct (formal_straight_prefix count stmts _ invalid nil 0 mm old false current proposed Position Statements)
   as [at_declaration Decl].
 cbn [formal_statements] in Decl.
 rewrite Split in Decl.
 destruct (successful_straight_segment middle _ invalid nil (S (0 + count)) mm old false
  (VM.add node (Needtobedefined (Gtyp (Fuint width))) at_declaration) proposed Straight Decl)
  as [at_connection [Middle Connection]].
 assert (Before : VM.find node at_connection = Some (Needtobedefined (Gtyp (Fuint width)))).
 { eapply formal_typed_suffix_preserves_value;
   [exact MiddleSafe|reflexivity| |exact Middle].
   apply RegisterMapFacts.find_add_eq. exact (eqxx node). }
 rewrite Projection.
 eapply unary_connection_tail_value;
 [exact Different|exact TailSafe|exact Before|reflexivity|exact Source|exact Adapt|exact Connection].
Qed.
Print Assumptions declared_unary_connection_value.
