Require Import FormalUIntObservation ScalarSinkTypes RegisterInvariants ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalNodeEquation StagedRegisterHold.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem declared_unary_observation count stmts declared_tail middle tail
 (node : VarOrder.T) op arg invalid mm old current result width :
 straight_drop count stmts = Some (Qcons (Swire node (Gtyp (Fuint width))) declared_tail) ->
 declared_tail = statement_append middle (Qcons (Sfcnct (Eid node) (Eprim_unop op arg)) tail) ->
 straight_statements middle -> formal_typed_suffix_safe mm node middle ->
 formal_typed_suffix_safe mm node tail ->
 has_register node stmts = false ->
 formal_value_iter invalid mm old false current stmts = Some result ->
 exists source value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address nil (S (0 + count) + statement_count middle) 0 nil) mm (Eprim_unop op arg) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint width)) = Some value /\ VM.find node result = Some value.
Proof.
 intros Position Split Straight MiddleSafe TailSafe Nonregister Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 mm old false current stmts) as [proposed|] eqn:Statements; [|discriminate Step].
 rewrite (staged_finish_false_equal stmts invalid nil 0 mm old proposed (fun e => eval_hfexpr_with_memory mm e old old)) in Step.
 pose proof (finish_registers_preserves_nonregister stmts _ old false proposed result node Nonregister Step) as Projection.
 destruct (formal_straight_prefix count stmts _ invalid nil 0 mm old false current proposed Position Statements)
 as [at_declaration Decl].
 cbn [formal_statements] in Decl. rewrite Split in Decl.
 destruct (successful_straight_segment middle _ invalid nil (S (0 + count)) mm old false
 (VM.add node (Needtobedefined (Gtyp (Fuint width))) at_declaration) proposed Straight Decl) as [at_connection [Middle Connection]].
 assert (Before : VM.find node at_connection = Some (Needtobedefined (Gtyp (Fuint width)))).
 { eapply formal_typed_suffix_preserves_value; [exact MiddleSafe|reflexivity| |exact Middle].
   apply RegisterMapFacts.find_add_eq. exact (eqxx node). }
 cbn [formal_statements is_memory_writer_ref] in Connection.
 destruct (formal_connect invalid (validif_raw_address nil (S (0 + count) + statement_count middle) 0 nil) mm false (Eid node) (Eprim_unop op arg) old at_connection)
 as [next|] eqn:Connect; [|discriminate Connection].
 destruct (formal_uint_observation invalid (validif_raw_address nil (S (0 + count) + statement_count middle) 0 nil) mm false node (Eprim_unop op arg) old at_connection next (Needtobedefined (Gtyp (Fuint width))) width
 Before (Logic.eq_refl _) Connect) as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 rewrite Projection. eapply formal_typed_suffix_preserves_value;
 [exact TailSafe|eapply adapted_uint_result_type; exact Adapt|exact Value|exact Connection].
Qed.
Print Assumptions declared_unary_observation.
