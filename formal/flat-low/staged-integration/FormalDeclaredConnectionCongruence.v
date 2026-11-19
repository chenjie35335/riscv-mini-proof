Require Import FormalDeclaredConnectionObservation.
Require Import FormalDeclaredConnection ScalarSinkTypes ScalarSinkObservation.
Require Import RegisterInvariants ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalConnectionTail FormalNodeEquation StagedRegisterHold.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem declared_connection_congruence count stmts declared_tail middle tail
 (node source : VarOrder.T) width invalid mm left right next_left next_right :
 straight_drop count stmts = Some (Qcons (Swire node (Gtyp (Fuint width))) declared_tail) ->
 declared_tail = statement_append middle (Qcons (Sfcnct (Eid node) (Eref (Eid source))) tail) ->
 straight_statements middle ->
 formal_typed_suffix_safe mm node middle -> formal_typed_suffix_safe mm node tail ->
 has_register node stmts = false -> node != source ->
 VM.find source left = VM.find source right ->
 formal_value_iter invalid mm left false left stmts = Some next_left ->
 formal_value_iter invalid mm right false right stmts = Some next_right ->
 VM.find node next_left = VM.find node next_right.
Proof.
 intros Position Split Straight MiddleSafe TailSafe Nonregister Different Equal Left Right.
 destruct (declared_connection_observation count stmts declared_tail middle tail node source width invalid mm left left next_left
 Position Split Straight MiddleSafe TailSafe Nonregister Different Left)
 as [source_left [value_left [SourceLeft [AdaptLeft ValueLeft]]]].
 destruct (declared_connection_observation count stmts declared_tail middle tail node source width invalid mm right right next_right
 Position Split Straight MiddleSafe TailSafe Nonregister Different Right)
 as [source_right [value_right [SourceRight [AdaptRight ValueRight]]]].
 rewrite <- Equal in SourceRight. rewrite SourceLeft in SourceRight. inversion SourceRight; subst source_right.
 rewrite AdaptLeft in AdaptRight. inversion AdaptRight; subst value_right.
 rewrite ValueLeft ValueRight. reflexivity.
Qed.
Print Assumptions declared_connection_congruence.
