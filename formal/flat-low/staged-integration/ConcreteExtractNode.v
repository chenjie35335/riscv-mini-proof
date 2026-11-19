Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeConcreteOutput ConcreteExpressionClosure ConcreteScalarExpressions.
From Coq Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma extract_result_type hi lo value result :
 eval_unop (Uextr hi lo) value = Some result ->
 type_of_val result = Gtyp (Fuint (hi.+1 - lo)).
Proof.
 destruct value as [ground bits|element array|bundle|typ|typ|typ];
 try destruct typ; try destruct ground; try match goal with f : fgtyp |- _ => destruct f end; cbn [eval_unop]; intro Eval;
 try discriminate Eval.
 all: repeat match type of Eval with context [if ?condition then _ else _] => destruct condition end;
 try discriminate Eval; inversion Eval; reflexivity.
Qed.
Theorem selected_extract_node_concrete offsets stmts entries node source hi lo inputs path mm old current result :
 select_node_offsets offsets stmts = Some entries ->
 selected_node_safety mm stmts offsets stmts ->
 List.In (node, Eprim_unop (Uextr hi lo) (Eref (Eid source))) entries ->
 (exists ground bits, VM.find source old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) mm old false current stmts = Some result ->
 exists width bits, VM.find node result = Some (Gval (Fuint width) bits).
Proof.
 intros Selected Safe Member [ground [bits Source]] Step.
 eapply selected_node_concrete_output; [exact Selected|exact Safe|exact Member| | |exact Step].
 - apply closure_scalar. apply scalar_ready_unary. eapply scalar_ready_ref. exact Source.
 - intros site value Eval.
   cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval. rewrite Source in Eval.
   exists (hi.+1 - lo). eapply extract_result_type. exact Eval.
Qed.
Print Assumptions selected_extract_node_concrete.
