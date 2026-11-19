Require Import CoreSocModel ComparisonNodes ExceptionPCShiftNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma exception_pc_round_down_identity (bits : seq bool) :
 take 2 bits = [::false;false] -> [::false;false] ++ drop 2 bits = bits.
Proof. intros Low. rewrite -Low cat_take_drop. reflexivity. Qed.
Lemma exception_pc_round_down_size (bits : seq bool) :
 size bits = 32%nat -> size ([::false;false] ++ drop 2 bits) = 32%nat.
Proof. intros Size. rewrite size_cat size_drop Size. reflexivity. Qed.
Lemma exception_pc_shift_right old bits :
 VM.find 121 old = Some (Gval (Fuint 32) bits) ->
 eval_hfexpr_with_memory flat_memories exception_pc_shift_771_expr old old =
 Some (Gval (Fuint 30) (drop 2 bits)).
Proof.
 intros Source. cbn [exception_pc_shift_771_expr eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Source. reflexivity.
Qed.
Lemma exception_pc_shift_left old bits :
 VM.find 771 old = Some (Gval (Fuint 30) bits) ->
 eval_hfexpr_with_memory flat_memories exception_pc_shift_772_expr old old =
 Some (Gval (Fuint 32) ([::false;false] ++ bits)).
Proof.
 intros Source. cbn [exception_pc_shift_772_expr eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Source. reflexivity.
Qed.
Theorem exception_pc_round_down_after_two invalid s0 s1 s2 bits :
 VM.find 121 s0 = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 772 s2 = Some (Gval (Fuint 32) ([::false;false] ++ drop 2 bits)).
Proof.
 intros Source S1 S2.
 pose proof (exception_pc_shift_771_value invalid s0 s0 s1 (drop 2 bits)
 (exception_pc_shift_right s0 bits Source) S1) as Right.
 exact (exception_pc_shift_772_value invalid s1 s1 s2 _
 (exception_pc_shift_left s1 (drop 2 bits) Right) S2).
Qed.
Print Assumptions exception_pc_round_down_after_two.
