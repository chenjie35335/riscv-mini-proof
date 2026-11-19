Require Import CoreSocModel ComparisonNodes FormalCheckerValidNodes FormalSuccessfulNode FormalComparisonBitShape NormalizedBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem checker_valid_comparison_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7952 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result checker_valid_position_7952 Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories checker_valid_expr_7952 old old = Some value) in Eval.
 exists value. split.
 - rewrite (checker_valid_equation_7952 invalid old current result Step). exact Eval.
 - cbn [checker_valid_expr_7952 eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 7951 old) as [source|]; [|discriminate Eval].
   exact (comparison_false_normalized source value Eval).
Qed.
Print Assumptions checker_valid_comparison_normalized.
