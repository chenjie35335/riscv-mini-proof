Require Import CoreSocModel ComparisonNodes EarlyBubbleInstructionControl.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem early_bubble_value_after_three invalid s0 s1 s2 s3 started kill branch exception :
 VM.find 7762 s0 = Some (Gval (Fuint 1) [::started]) ->
 VM.find 85 s0 = Some (Gval (Fuint 1) [::kill]) ->
 VM.find 1360 s1 = Some (Gval (Fuint 1) [::branch]) ->
 VM.find 128 s2 = Some (Gval (Fuint 1) [::exception]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 7944 s3 = Some (Gval (Fuint 1) [::((started || kill) || branch) || exception]).
Proof.
 intros Started Kill Branch Exception S1 S2 S3.
 assert (A : VM.find 7942 s1 = Some (Gval (Fuint 1) [::started || kill])).
 { rewrite (bubble_instruction_equation_7942 invalid s0 s0 s1 S1).
   cbn [bubble_instruction_expr_7942 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Started Kill. destruct started,kill; reflexivity. }
 assert (B : VM.find 7943 s2 = Some (Gval (Fuint 1) [::(started || kill) || branch])).
 { rewrite (bubble_instruction_equation_7943 invalid s1 s1 s2 S2).
   cbn [bubble_instruction_expr_7943 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite A Branch. destruct started,kill,branch; reflexivity. }
 rewrite (bubble_instruction_equation_7944 invalid s2 s2 s3 S3).
 cbn [bubble_instruction_expr_7944 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite B Exception. destruct started,kill,branch,exception; reflexivity.
Qed.
Print Assumptions early_bubble_value_after_three.
