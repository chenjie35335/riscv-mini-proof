Require Import RegisterInvariants ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalSymbolicInvalidWire FormalConnectionTail FormalNodeEquation StagedRegisterHold.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Require Import FormalDeclaredConnection.
Theorem declared_invalid_wire_value count stmts declared_tail middle tail
 (node : VarOrder.T) width inputs path mm old current result :
 straight_drop count stmts = Some (Qcons (Swire node (Gtyp (Fuint width))) declared_tail) ->
 declared_tail = statement_append middle (Qcons (Sinvalid (Eid node)) tail) ->
 straight_statements middle ->
 formal_typed_suffix_safe mm node middle -> formal_typed_suffix_safe mm node tail ->
 has_register node stmts = false ->
 formal_value_iter (formal_invalid_policy inputs path) mm old false current stmts = Some result ->
 exists bits, VM.find node result = Some (Gval (Fuint width) bits) /\ size bits = width.
Proof.
 intros Position Split Straight MiddleSafe TailSafe Nonregister Step.
 set (invalid := formal_invalid_policy inputs path) in *.
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
 cbn [formal_statements] in Connection.
 unfold invalid in Connection.
 rewrite (formal_invalid_uint_wire inputs path _ mm old at_connection node width Before) in Connection.
 destruct (formal_invalid_uint_word inputs path (rcons nil (S (0 + count) + statement_count middle)) width)
  as [bits [Word Width]].
 exists bits. split; [|exact Width].
 rewrite Projection.
 eapply formal_typed_suffix_preserves_value;
 [exact TailSafe|reflexivity| |].
 - rewrite <- Word. apply RegisterMapFacts.find_add_eq. exact (eqxx node).
 - exact Connection.
Qed.
Print Assumptions declared_invalid_wire_value.
