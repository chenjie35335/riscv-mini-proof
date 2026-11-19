Require Import FormalRegisterMuxObservation FormalRegisterCommitIdentity RegisterCommitCertificate ScalarNodeFrames CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem formal_committed_uint_register_mux_observation count stmts declared middle tail
 node reg cond yes no invalid mm old current result old_value width :
 straight_drop count stmts = Some (Qcons (Sreg node reg) declared) ->
 declared = statement_append middle (Qcons (Sfcnct (Eid node) (Emux cond yes no)) tail) ->
 straight_statements middle -> formal_typed_suffix_safe mm node middle -> formal_typed_suffix_safe mm node tail ->
 VM.find node old = Some old_value -> type_of_val old_value = Gtyp (Fuint width) ->
 register_identity_b node stmts ->
 formal_value_iter invalid mm old true current stmts = Some result ->
 exists source value,
 eval_hfexpr_validif_policy (isolated_validif_policy invalid)
 (validif_raw_address nil ((0 + count).+1 + statement_count middle)%nat 0 nil) mm (Emux cond yes no) old old = Some source /\
 adapt_hvalue_as_type source (Gtyp (Fuint width)) = Some value /\ VM.find node result = Some value.
Proof.
 intros Position Split Straight MiddleSafe TailSafe Old Typed Identity Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 mm old true current stmts) as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_mux_observation count stmts declared middle tail node reg cond yes no invalid mm old true current proposed old_value width
 Position Split Straight MiddleSafe TailSafe Old Typed Statements) as [source [value [Source [Adapt Value]]]].
 exists source, value. split; [exact Source|]. split; [exact Adapt|].
 rewrite (formal_finish_identity_preserves stmts invalid nil 0 mm old proposed result node Identity Step). exact Value.
Qed.
Print Assumptions formal_committed_uint_register_mux_observation.
