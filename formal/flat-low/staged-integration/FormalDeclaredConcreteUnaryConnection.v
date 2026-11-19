Require Import FormalUIntObservation ConcreteGroundOperations.
Require Import FormalDeclaredConnection.
Require Import ConcreteGroundAdapt ConcreteGroundOperations ScalarSinkObservation ScalarSinkTypes.
Require Import RegisterInvariants ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalConnectionTail FormalNodeEquation StagedRegisterHold.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem declared_unary_connection_concrete count stmts declared_tail middle tail
 (node source : VarOrder.T) op width ground bits invalid mm old current result :
 straight_drop count stmts = Some (Qcons (Swire node (Gtyp (Fuint width))) declared_tail) ->
 declared_tail = statement_append middle (Qcons (Sfcnct (Eid node) (Eprim_unop op (Eref (Eid source)))) tail) ->
 straight_statements middle ->
 formal_typed_suffix_safe mm node middle -> formal_typed_suffix_safe mm node tail ->
 has_register node stmts = false -> node != source ->
 VM.find source old = Some (Gval ground bits) ->
 formal_value_iter invalid mm old false current stmts = Some result ->
 exists word, VM.find node result = Some (Gval (Fuint width) word).
Proof.
 intros Position Split Straight MiddleSafe TailSafe Nonregister Different Source Step.
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
 match type of Connection with
 | context [formal_connect ?policy ?site ?mem ?phase ?lhs ?rhs ?prev ?cur] =>
 destruct (formal_connect policy site mem phase lhs rhs prev cur) as [next|] eqn:Connect;
 [|discriminate Connection]
 end.
 destruct (formal_uint_observation _ _ mm false node (Eprim_unop op (Eref (Eid source)))
 old at_connection next (Needtobedefined (Gtyp (Fuint width))) width Before (Logic.eq_refl _) Connect)
 as [read [written [Read [Written Next]]]].
 change (eval_hfexpr_with_memory mm (Eprim_unop op (Eref (Eid source))) old old = Some read) in Read.
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Read. rewrite Source in Read.
 destruct (concrete_unary_result op ground bits read Read) as [read_ground [read_bits Value]]. subst read.
 pose proof (adapted_uint_result_type _ width _ Written) as Typed.
 destruct (concrete_ground_adapt read_ground read_bits (Gtyp (Fuint width)) written Written)
 as [target [word Value]]. subst written.
 cbn [type_of_val] in Typed. inversion Typed; subst target.
 exists word. rewrite Projection.
 eapply formal_typed_suffix_preserves_value;
 [exact TailSafe|reflexivity|exact Next|exact Connection].
Qed.
Print Assumptions declared_unary_connection_concrete.
