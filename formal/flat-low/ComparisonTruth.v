Require Import CoreSocModel.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma uint_equal_comparison w1 w2 b1 b2 :
 to_N b1 = to_N b2 ->
 eval_binop (Bcomp Beq) (Gval (Fuint w1) b1) (Gval (Fuint w2) b2) =
 Some (Gval (Fuint 1) [::true]).
Proof.
 intro Same. unfold eval_binop, eval_binop_basic. rewrite Same eqxx.
 unfold refine_boolean_result. destruct (absorbing_bit _ _ _); reflexivity.
Qed.
Lemma equal_ref_comparison mm old (left right : VarOrder.T) w1 w2 b1 b2 :
 VM.find left old = Some (Gval (Fuint w1) b1) ->
 VM.find right old = Some (Gval (Fuint w2) b2) ->
 to_N b1 = to_N b2 ->
 eval_hfexpr_with_memory mm
  (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T left))
    (@Eref VarOrder.T (@Eid VarOrder.T right))) old old =
 Some (Gval (Fuint 1) [::true]).
Proof.
 intros Left Right Same. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Left Right. apply uint_equal_comparison. exact Same.
Qed.
Lemma known_true_node sem (node : VarOrder.T) :
 VM.find node sem = Some (Gval (Fuint 1) [::true]) ->
 generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T node)) sem.
Proof.
 intro Value. unfold generated_expr_true.
 cbn [eval_hfexpr eval_href]. rewrite Value. reflexivity.
Qed.
Print Assumptions equal_ref_comparison.
Print Assumptions known_true_node.
Definition comparison_inputs_agree (old : VM.t hvalue) (left right : VarOrder.T) : Prop :=
 exists w1 w2 b1 b2,
 VM.find left old = Some (Gval (Fuint w1) b1) /\
 VM.find right old = Some (Gval (Fuint w2) b2) /\ to_N b1 = to_N b2.
Lemma agreeing_ref_comparison mm old left right :
 comparison_inputs_agree old left right ->
 eval_hfexpr_with_memory mm
  (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T left))
    (@Eref VarOrder.T (@Eid VarOrder.T right))) old old =
 Some (Gval (Fuint 1) [::true]).
Proof.
 intros [w1 [w2 [b1 [b2 [Left [Right Same]]]]]].
 eapply equal_ref_comparison; eassumption.
Qed.
