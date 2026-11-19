Require Import CoreSocModel ComparisonNodes FormalCheckerValidNodes FormalCheckerValidOutput NormalizedBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem checker_valid_bits_after_six invalid s0 s1 s2 s3 s4 s5 s6 bubble stall reset :
 VM.find 7947 s0 = Some (Gval (Fuint 1) [::bubble]) ->
 VM.find 7765 s0 = Some (Gval (Fuint 1) [::stall]) ->
 VM.find 65 s0 = Some (Gval (Fuint 1) [::reset]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 VM.find 1395 s6 = Some (Gval (Fuint 1) [::~~ ((bubble || stall) || reset)]).
Proof.
 intros Bubble Stall Reset S1 S2 S3 S4 S5 S6.
 assert (A : VM.find 7948 s1 = Some (Gval (Fuint 1) [::bubble || stall])).
 { rewrite (checker_valid_equation_7948 invalid s0 s0 s1 S1).
   cbn [checker_valid_expr_7948 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Bubble Stall. destruct bubble, stall; reflexivity. }
 assert (B : VM.find 7949 s1 = Some (Gval (Fuint 1) [::reset])).
 { rewrite (checker_valid_equation_7949 invalid s0 s0 s1 S1).
   cbn [checker_valid_expr_7949 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Reset. destruct reset; reflexivity. }
 assert (C : VM.find 7950 s2 = Some (Gval (Fuint 1) [::(bubble || stall) || reset])).
 { rewrite (checker_valid_equation_7950 invalid s1 s1 s2 S2).
   cbn [checker_valid_expr_7950 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite A B. destruct bubble, stall, reset; reflexivity. }
 assert (D : VM.find 7951 s3 = Some (Gval (Fuint 1) [::(bubble || stall) || reset])).
 { rewrite (checker_valid_equation_7951 invalid s2 s2 s3 S3).
   cbn [checker_valid_expr_7951 eval_hfexpr_with_memory eval_href_with_memory]. exact C. }
 assert (E : VM.find 7952 s4 = Some (Gval (Fuint 1) [::~~ ((bubble || stall) || reset)])).
 { rewrite (checker_valid_equation_7952 invalid s3 s3 s4 S4).
   cbn [checker_valid_expr_7952 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite D. destruct bubble, stall, reset; reflexivity. }
 apply (checker_output_after_two invalid s4 s5 s6 _); try assumption. constructor.
Qed.
Print Assumptions checker_valid_bits_after_six.
Theorem checker_valid_true_bits_after_six invalid s0 s1 s2 s3 s4 s5 s6 bubble stall reset :
 VM.find 7947 s0 = Some (Gval (Fuint 1) [::bubble]) ->
 VM.find 7765 s0 = Some (Gval (Fuint 1) [::stall]) ->
 VM.find 65 s0 = Some (Gval (Fuint 1) [::reset]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 VM.find 1395 s6 = Some (Gval (Fuint 1) [::true]) ->
 bubble = false /\ stall = false /\ reset = false.
Proof.
 intros Bubble Stall Reset S1 S2 S3 S4 S5 S6 Valid.
 pose proof (checker_valid_bits_after_six invalid s0 s1 s2 s3 s4 s5 s6 bubble stall reset
 Bubble Stall Reset S1 S2 S3 S4 S5 S6) as Value.
 rewrite Valid in Value. destruct bubble, stall, reset; try discriminate Value.
 repeat split; reflexivity.
Qed.
Print Assumptions checker_valid_true_bits_after_six.
