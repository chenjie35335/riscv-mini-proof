Require Import FormalNodeEquation ScalarNodeFrames.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem formal_successful_node count stmts tail node expression invalid mm old phase current result :
 straight_drop count stmts = Some (Qcons (Snode node expression) tail) ->
 formal_value_iter invalid mm old phase current stmts = Some result ->
 exists value, eval_hfexpr_validif_policy (isolated_validif_policy invalid)
 (validif_raw_address nil count 0 nil) mm expression old old = Some value.
Proof.
 intros Position Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 mm old phase current stmts) as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_straight_prefix count stmts _ invalid nil 0 mm old phase current proposed Position Statements) as [before Node].
 rewrite add0n in Node. cbn [formal_statements] in Node.
 destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address nil count 0 nil) mm expression old old) as [value|] eqn:Eval; [|discriminate Node].
 exists value. reflexivity.
Qed.
Print Assumptions formal_successful_node.
