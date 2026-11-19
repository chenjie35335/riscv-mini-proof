Require Import ConcreteGroundUIntAdapt ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames RegisterCommitCertificate FormalUIntRegisterCommitSource ConcreteExpressionClosure ConcreteGroundAdapt ScalarSinkTypes.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem concrete_register_mux_commit count stmts declared middle tail
 node reg cond yes no inputs path mm old current result old_value width :
 straight_drop count stmts = Some (Qcons (Sreg node reg) declared) ->
 declared = statement_append middle (Qcons (Sfcnct (Eid node) (Emux cond yes no)) tail) ->
 straight_statements middle -> formal_typed_suffix_safe mm node middle -> formal_typed_suffix_safe mm node tail ->
 VM.find node old = Some old_value -> type_of_val old_value = Gtyp (Fuint width) ->
 register_identity_b node stmts ->
 concrete_expression_ready old (Emux cond yes no) ->
 formal_value_iter (formal_invalid_policy inputs path) mm old true current stmts = Some result ->
 exists word, size word = width /\ VM.find node result = Some (Gval (Fuint width) word).
Proof.
 intros Position Split Straight MiddleSafe TailSafe Old Typed Identity Ready Step.
 destruct (formal_committed_uint_register_mux_observation count stmts declared middle tail
 node reg cond yes no (formal_invalid_policy inputs path) mm old current result old_value width
 Position Split Straight MiddleSafe TailSafe Old Typed Identity Step)
 as [source [value [Source [Adapt Value]]]].
 destruct (concrete_expression_closure inputs path mm old (Emux cond yes no) Ready _ source Source)
 as [ground [bits Equal]]. subst source.
 destruct (concrete_ground_uint_adapt ground bits width value Adapt) as [word [Size Equal]].
 subst value. exists word. split; [exact Size|exact Value].
Qed.
Print Assumptions concrete_register_mux_commit.
