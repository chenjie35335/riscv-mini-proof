Require Import FormalGroundNodeFrames.
Require Import RegisterInvariants ScalarNodeFrames ScalarSuffixCertificates MemoryWriteFrames FormalTypedNodeFrames FormalNodeEquation StagedRegisterHold.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem formal_combinational_known_ground_node count stmts tail node expression ground value
 invalid mm old current result :
 straight_drop count stmts = Some (Qcons (Snode node expression) tail) ->
 formal_typed_suffix_safe mm node tail -> has_register node stmts = false ->
 eval_hfexpr_validif_policy (isolated_validif_policy invalid)
   (validif_raw_address [::] count 0 [::]) mm expression old old = Some value ->
 type_of_val value = Gtyp ground ->
 formal_value_iter invalid mm old false current stmts = Some result ->
 VM.find node result = Some value.
Proof.
 intros Position Safe Nonregister Eval Typed Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid [::] 0 mm old false current stmts)
   as [proposed|] eqn:Statements; [|discriminate Step].
 rewrite (staged_finish_false_equal stmts invalid [::] 0 mm old proposed
   (fun e => eval_hfexpr_with_memory mm e old old)) in Step.
 rewrite (finish_registers_preserves_nonregister stmts _ old false proposed
   result node Nonregister Step).
 destruct (formal_straight_prefix count stmts (Qcons (Snode node expression) tail)
   invalid [::] 0 mm old false current proposed Position Statements) as [at_node NodeStep].
 rewrite add0n in NodeStep. cbn [formal_statements] in NodeStep. rewrite Eval in NodeStep.
 eapply formal_ground_suffix_preserves_value; [exact Safe|exact Typed| |exact NodeStep].
 apply RegisterMapFacts.find_add_eq. exact (eqxx node).
Qed.
Print Assumptions formal_combinational_known_ground_node.
