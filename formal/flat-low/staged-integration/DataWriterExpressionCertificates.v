Require Import ConcreteExpressionClosure ConcreteScalarExpressions ConcreteGroundOperations.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Ltac solve_writer_ready :=
 first [apply closure_scalar; solve [repeat first [eapply scalar_ready_ref; eassumption | apply scalar_ready_const | apply scalar_ready_unary | apply scalar_ready_binary | apply scalar_ready_cast]]
 | apply closure_mux; solve_writer_ready | apply closure_unary; solve_writer_ready | apply closure_binary; solve_writer_ready].
Definition writer_expr_7827 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 1155))).
Lemma writer_ready_7827 old :
 (exists ground bits, VM.find 1155 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7827.
Proof.
 intros [g1155 [b1155 H1155]].
 unfold writer_expr_7827.
 solve_writer_ready.
Qed.
Definition writer_expr_7828 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7827)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Lemma writer_ready_7828 old :
 (exists ground bits, VM.find 7827 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7828.
Proof.
 intros [g7827 [b7827 H7827]].
 unfold writer_expr_7828.
 solve_writer_ready.
Qed.
Definition writer_expr_7829 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1155))).
Lemma writer_ready_7829 old :
 (exists ground bits, VM.find 1155 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7829.
Proof.
 intros [g1155 [b1155 H1155]].
 unfold writer_expr_7829.
 solve_writer_ready.
Qed.
Definition writer_expr_7830 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7829)) (@Econst VarOrder.T (Fuint 2) [::true; true])).
Lemma writer_ready_7830 old :
 (exists ground bits, VM.find 7829 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7830.
Proof.
 intros [g7829 [b7829 H7829]].
 unfold writer_expr_7830.
 solve_writer_ready.
Qed.
Definition writer_expr_7831 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7828)) (@Eref VarOrder.T (@Eid VarOrder.T 7830))).
Lemma writer_ready_7831 old :
 (exists ground bits, VM.find 7828 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7830 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7831.
Proof.
 intros [g7828 [b7828 H7828]].
 intros [g7830 [b7830 H7830]].
 unfold writer_expr_7831.
 solve_writer_ready.
Qed.
Definition writer_expr_7832 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma writer_ready_7832 old :
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7832.
Proof.
 intros [g7765 [b7765 H7765]].
 unfold writer_expr_7832.
 solve_writer_ready.
Qed.
Definition writer_expr_7833 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 91))).
Lemma writer_ready_7833 old :
 (exists ground bits, VM.find 91 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7833.
Proof.
 intros [g91 [b91 H91]].
 unfold writer_expr_7833.
 solve_writer_ready.
Qed.
Definition writer_expr_7834 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 92))).
Lemma writer_ready_7834 old :
 (exists ground bits, VM.find 92 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7834.
Proof.
 intros [g92 [b92 H92]].
 unfold writer_expr_7834.
 solve_writer_ready.
Qed.
Definition writer_expr_7835 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7833)) (@Eref VarOrder.T (@Eid VarOrder.T 7834))).
Lemma writer_ready_7835 old :
 (exists ground bits, VM.find 7833 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7834 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7835.
Proof.
 intros [g7833 [b7833 H7833]].
 intros [g7834 [b7834 H7834]].
 unfold writer_expr_7835.
 solve_writer_ready.
Qed.
Definition writer_expr_7836 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7832)) (@Eref VarOrder.T (@Eid VarOrder.T 7835))).
Lemma writer_ready_7836 old :
 (exists ground bits, VM.find 7832 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7835 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7836.
Proof.
 intros [g7832 [b7832 H7832]].
 intros [g7835 [b7835 H7835]].
 unfold writer_expr_7836.
 solve_writer_ready.
Qed.
Definition writer_expr_7837 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7819)) (@Eref VarOrder.T (@Eid VarOrder.T 7831))).
Lemma writer_ready_7837 old :
 (exists ground bits, VM.find 7819 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7831 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7837.
Proof.
 intros [g7819 [b7819 H7819]].
 intros [g7831 [b7831 H7831]].
 unfold writer_expr_7837.
 solve_writer_ready.
Qed.
Definition writer_expr_7838 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Eref VarOrder.T (@Eid VarOrder.T 7754)) (@Eref VarOrder.T (@Eid VarOrder.T 91))).
Lemma writer_ready_7838 old :
 (exists ground bits, VM.find 91 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7754 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7838.
Proof.
 intros [g91 [b91 H91]].
 intros [g7754 [b7754 H7754]].
 intros [g7765 [b7765 H7765]].
 unfold writer_expr_7838.
 solve_writer_ready.
Qed.
Definition writer_expr_7839 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 1155))).
Lemma writer_ready_7839 old :
 (exists ground bits, VM.find 1155 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7839.
Proof.
 intros [g1155 [b1155 H1155]].
 unfold writer_expr_7839.
 solve_writer_ready.
Qed.
Definition writer_expr_7840 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7839))).
Lemma writer_ready_7840 old :
 (exists ground bits, VM.find 7839 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7840.
Proof.
 intros [g7839 [b7839 H7839]].
 unfold writer_expr_7840.
 solve_writer_ready.
Qed.
Definition writer_expr_7841 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 1155))).
Lemma writer_ready_7841 old :
 (exists ground bits, VM.find 1155 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7841.
Proof.
 intros [g1155 [b1155 H1155]].
 unfold writer_expr_7841.
 solve_writer_ready.
Qed.
Definition writer_expr_7842 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7841))).
Lemma writer_ready_7842 old :
 (exists ground bits, VM.find 7841 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7842.
Proof.
 intros [g7841 [b7841 H7841]].
 unfold writer_expr_7842.
 solve_writer_ready.
Qed.
Definition writer_expr_7843 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7838))).
Lemma writer_ready_7843 old :
 (exists ground bits, VM.find 7838 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7843.
Proof.
 intros [g7838 [b7838 H7838]].
 unfold writer_expr_7843.
 solve_writer_ready.
Qed.
Definition writer_expr_7844 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7843)) (@Econst VarOrder.T (Fuint 4) [::true; true; true; true]) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma writer_ready_7844 old :
 (exists ground bits, VM.find 7843 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7844.
Proof.
 intros [g7843 [b7843 H7843]].
 unfold writer_expr_7844.
 solve_writer_ready.
Qed.
Definition writer_expr_7845 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7838))).
Lemma writer_ready_7845 old :
 (exists ground bits, VM.find 7838 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7845.
Proof.
 intros [g7838 [b7838 H7838]].
 unfold writer_expr_7845.
 solve_writer_ready.
Qed.
Definition writer_expr_7846 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7845)) (@Eref VarOrder.T (@Eid VarOrder.T 7840)) (@Eref VarOrder.T (@Eid VarOrder.T 7844))).
Lemma writer_ready_7846 old :
 (exists ground bits, VM.find 7840 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7844 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7845 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7846.
Proof.
 intros [g7840 [b7840 H7840]].
 intros [g7844 [b7844 H7844]].
 intros [g7845 [b7845 H7845]].
 unfold writer_expr_7846.
 solve_writer_ready.
Qed.
Definition writer_expr_7847 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7838))).
Lemma writer_ready_7847 old :
 (exists ground bits, VM.find 7838 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7847.
Proof.
 intros [g7838 [b7838 H7838]].
 unfold writer_expr_7847.
 solve_writer_ready.
Qed.
Definition writer_expr_7848 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7847)) (@Eref VarOrder.T (@Eid VarOrder.T 7842)) (@Eref VarOrder.T (@Eid VarOrder.T 7846))).
Lemma writer_ready_7848 old :
 (exists ground bits, VM.find 7842 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7846 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7847 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_7848.
Proof.
 intros [g7842 [b7842 H7842]].
 intros [g7846 [b7846 H7846]].
 intros [g7847 [b7847 H7847]].
 unfold writer_expr_7848.
 solve_writer_ready.
Qed.
Definition writer_expr_8704 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8360)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Lemma writer_ready_8704 old :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8704.
Proof.
 intros [g8360 [b8360 H8360]].
 unfold writer_expr_8704.
 solve_writer_ready.
Qed.
Definition writer_expr_8705 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8358)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8704))).
Lemma writer_ready_8705 old :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8704 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8705.
Proof.
 intros [g8358 [b8358 H8358]].
 intros [g8704 [b8704 H8704]].
 unfold writer_expr_8705.
 solve_writer_ready.
Qed.
Definition writer_expr_8706 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8356)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8705))).
Lemma writer_ready_8706 old :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8705 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8706.
Proof.
 intros [g8356 [b8356 H8356]].
 intros [g8705 [b8705 H8705]].
 unfold writer_expr_8706.
 solve_writer_ready.
Qed.
Definition writer_expr_8707 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8354)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8706))).
Lemma writer_ready_8707 old :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8706 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8707.
Proof.
 intros [g8354 [b8354 H8354]].
 intros [g8706 [b8706 H8706]].
 unfold writer_expr_8707.
 solve_writer_ready.
Qed.
Definition writer_expr_8708 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8352)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8707))).
Lemma writer_ready_8708 old :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8707 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8708.
Proof.
 intros [g8352 [b8352 H8352]].
 intros [g8707 [b8707 H8707]].
 unfold writer_expr_8708.
 solve_writer_ready.
Qed.
Definition writer_expr_8709 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8350)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8708))).
Lemma writer_ready_8709 old :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8708 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8709.
Proof.
 intros [g8350 [b8350 H8350]].
 intros [g8708 [b8708 H8708]].
 unfold writer_expr_8709.
 solve_writer_ready.
Qed.
Definition writer_expr_8710 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8348)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8709))).
Lemma writer_ready_8710 old :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8709 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8710.
Proof.
 intros [g8348 [b8348 H8348]].
 intros [g8709 [b8709 H8709]].
 unfold writer_expr_8710.
 solve_writer_ready.
Qed.
Definition writer_expr_8711 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8346)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8710))).
Lemma writer_ready_8711 old :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8710 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8711.
Proof.
 intros [g8346 [b8346 H8346]].
 intros [g8710 [b8710 H8710]].
 unfold writer_expr_8711.
 solve_writer_ready.
Qed.
Definition writer_expr_8712 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8344)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8711))).
Lemma writer_ready_8712 old :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8711 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8712.
Proof.
 intros [g8344 [b8344 H8344]].
 intros [g8711 [b8711 H8711]].
 unfold writer_expr_8712.
 solve_writer_ready.
Qed.
Definition writer_expr_8713 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8342)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8712))).
Lemma writer_ready_8713 old :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8712 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8713.
Proof.
 intros [g8342 [b8342 H8342]].
 intros [g8712 [b8712 H8712]].
 unfold writer_expr_8713.
 solve_writer_ready.
Qed.
Definition writer_expr_8714 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8340)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8713))).
Lemma writer_ready_8714 old :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8713 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8714.
Proof.
 intros [g8340 [b8340 H8340]].
 intros [g8713 [b8713 H8713]].
 unfold writer_expr_8714.
 solve_writer_ready.
Qed.
Definition writer_expr_8715 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8338)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8714))).
Lemma writer_ready_8715 old :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8714 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8715.
Proof.
 intros [g8338 [b8338 H8338]].
 intros [g8714 [b8714 H8714]].
 unfold writer_expr_8715.
 solve_writer_ready.
Qed.
Definition writer_expr_8716 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8336)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8715))).
Lemma writer_ready_8716 old :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8715 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8716.
Proof.
 intros [g8336 [b8336 H8336]].
 intros [g8715 [b8715 H8715]].
 unfold writer_expr_8716.
 solve_writer_ready.
Qed.
Definition writer_expr_8717 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8334)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8716))).
Lemma writer_ready_8717 old :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8716 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8717.
Proof.
 intros [g8334 [b8334 H8334]].
 intros [g8716 [b8716 H8716]].
 unfold writer_expr_8717.
 solve_writer_ready.
Qed.
Definition writer_expr_8718 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8332)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8717))).
Lemma writer_ready_8718 old :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8717 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8718.
Proof.
 intros [g8332 [b8332 H8332]].
 intros [g8717 [b8717 H8717]].
 unfold writer_expr_8718.
 solve_writer_ready.
Qed.
Definition writer_expr_8719 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8330)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8718))).
Lemma writer_ready_8719 old :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8718 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8719.
Proof.
 intros [g8330 [b8330 H8330]].
 intros [g8718 [b8718 H8718]].
 unfold writer_expr_8719.
 solve_writer_ready.
Qed.
Definition writer_expr_8720 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8328)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8719))).
Lemma writer_ready_8720 old :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8719 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8720.
Proof.
 intros [g8328 [b8328 H8328]].
 intros [g8719 [b8719 H8719]].
 unfold writer_expr_8720.
 solve_writer_ready.
Qed.
Definition writer_expr_8721 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8326)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8720))).
Lemma writer_ready_8721 old :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8720 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8721.
Proof.
 intros [g8326 [b8326 H8326]].
 intros [g8720 [b8720 H8720]].
 unfold writer_expr_8721.
 solve_writer_ready.
Qed.
Definition writer_expr_8722 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8324)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8721))).
Lemma writer_ready_8722 old :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8721 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8722.
Proof.
 intros [g8324 [b8324 H8324]].
 intros [g8721 [b8721 H8721]].
 unfold writer_expr_8722.
 solve_writer_ready.
Qed.
Definition writer_expr_8723 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8322)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8722))).
Lemma writer_ready_8723 old :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8722 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8723.
Proof.
 intros [g8322 [b8322 H8322]].
 intros [g8722 [b8722 H8722]].
 unfold writer_expr_8723.
 solve_writer_ready.
Qed.
Definition writer_expr_8724 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8320)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8723))).
Lemma writer_ready_8724 old :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8723 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8724.
Proof.
 intros [g8320 [b8320 H8320]].
 intros [g8723 [b8723 H8723]].
 unfold writer_expr_8724.
 solve_writer_ready.
Qed.
Definition writer_expr_8725 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8318)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8724))).
Lemma writer_ready_8725 old :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8724 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8725.
Proof.
 intros [g8318 [b8318 H8318]].
 intros [g8724 [b8724 H8724]].
 unfold writer_expr_8725.
 solve_writer_ready.
Qed.
Definition writer_expr_8726 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8316)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8725))).
Lemma writer_ready_8726 old :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8725 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8726.
Proof.
 intros [g8316 [b8316 H8316]].
 intros [g8725 [b8725 H8725]].
 unfold writer_expr_8726.
 solve_writer_ready.
Qed.
Definition writer_expr_8727 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8314)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8726))).
Lemma writer_ready_8727 old :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8726 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8727.
Proof.
 intros [g8314 [b8314 H8314]].
 intros [g8726 [b8726 H8726]].
 unfold writer_expr_8727.
 solve_writer_ready.
Qed.
Definition writer_expr_8728 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8312)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8727))).
Lemma writer_ready_8728 old :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8727 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8728.
Proof.
 intros [g8312 [b8312 H8312]].
 intros [g8727 [b8727 H8727]].
 unfold writer_expr_8728.
 solve_writer_ready.
Qed.
Definition writer_expr_8729 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8310)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8728))).
Lemma writer_ready_8729 old :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8728 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8729.
Proof.
 intros [g8310 [b8310 H8310]].
 intros [g8728 [b8728 H8728]].
 unfold writer_expr_8729.
 solve_writer_ready.
Qed.
Definition writer_expr_8730 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8308)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8729))).
Lemma writer_ready_8730 old :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8729 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8730.
Proof.
 intros [g8308 [b8308 H8308]].
 intros [g8729 [b8729 H8729]].
 unfold writer_expr_8730.
 solve_writer_ready.
Qed.
Definition writer_expr_8731 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8306)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8730))).
Lemma writer_ready_8731 old :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8730 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8731.
Proof.
 intros [g8306 [b8306 H8306]].
 intros [g8730 [b8730 H8730]].
 unfold writer_expr_8731.
 solve_writer_ready.
Qed.
Definition writer_expr_8732 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8304)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8731))).
Lemma writer_ready_8732 old :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8731 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8732.
Proof.
 intros [g8304 [b8304 H8304]].
 intros [g8731 [b8731 H8731]].
 unfold writer_expr_8732.
 solve_writer_ready.
Qed.
Definition writer_expr_8733 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8302)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8732))).
Lemma writer_ready_8733 old :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8732 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8733.
Proof.
 intros [g8302 [b8302 H8302]].
 intros [g8732 [b8732 H8732]].
 unfold writer_expr_8733.
 solve_writer_ready.
Qed.
Definition writer_expr_8734 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8300)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8733))).
Lemma writer_ready_8734 old :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8733 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8734.
Proof.
 intros [g8300 [b8300 H8300]].
 intros [g8733 [b8733 H8733]].
 unfold writer_expr_8734.
 solve_writer_ready.
Qed.
Definition writer_expr_8735 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8298)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8734))).
Lemma writer_ready_8735 old :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8734 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8735.
Proof.
 intros [g8298 [b8298 H8298]].
 intros [g8734 [b8734 H8734]].
 unfold writer_expr_8735.
 solve_writer_ready.
Qed.
Definition writer_expr_8736 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8296)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8735))).
Lemma writer_ready_8736 old :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8735 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8736.
Proof.
 intros [g8296 [b8296 H8296]].
 intros [g8735 [b8735 H8735]].
 unfold writer_expr_8736.
 solve_writer_ready.
Qed.
Definition writer_expr_8737 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8294)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8736))).
Lemma writer_ready_8737 old :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8736 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8737.
Proof.
 intros [g8294 [b8294 H8294]].
 intros [g8736 [b8736 H8736]].
 unfold writer_expr_8737.
 solve_writer_ready.
Qed.
Definition writer_expr_8738 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8292)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8737))).
Lemma writer_ready_8738 old :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8737 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8738.
Proof.
 intros [g8292 [b8292 H8292]].
 intros [g8737 [b8737 H8737]].
 unfold writer_expr_8738.
 solve_writer_ready.
Qed.
Definition writer_expr_8739 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8290)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8738))).
Lemma writer_ready_8739 old :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8738 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8739.
Proof.
 intros [g8290 [b8290 H8290]].
 intros [g8738 [b8738 H8738]].
 unfold writer_expr_8739.
 solve_writer_ready.
Qed.
Definition writer_expr_8740 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8288)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8739))).
Lemma writer_ready_8740 old :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8739 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8740.
Proof.
 intros [g8288 [b8288 H8288]].
 intros [g8739 [b8739 H8739]].
 unfold writer_expr_8740.
 solve_writer_ready.
Qed.
Definition writer_expr_8741 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8286)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8740))).
Lemma writer_ready_8741 old :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8740 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8741.
Proof.
 intros [g8286 [b8286 H8286]].
 intros [g8740 [b8740 H8740]].
 unfold writer_expr_8741.
 solve_writer_ready.
Qed.
Definition writer_expr_8742 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8284)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8741))).
Lemma writer_ready_8742 old :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8741 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8742.
Proof.
 intros [g8284 [b8284 H8284]].
 intros [g8741 [b8741 H8741]].
 unfold writer_expr_8742.
 solve_writer_ready.
Qed.
Definition writer_expr_8743 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8282)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8742))).
Lemma writer_ready_8743 old :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8742 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8743.
Proof.
 intros [g8282 [b8282 H8282]].
 intros [g8742 [b8742 H8742]].
 unfold writer_expr_8743.
 solve_writer_ready.
Qed.
Definition writer_expr_8744 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8280)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8743))).
Lemma writer_ready_8744 old :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8743 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8744.
Proof.
 intros [g8280 [b8280 H8280]].
 intros [g8743 [b8743 H8743]].
 unfold writer_expr_8744.
 solve_writer_ready.
Qed.
Definition writer_expr_8745 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8278)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8744))).
Lemma writer_ready_8745 old :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8744 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8745.
Proof.
 intros [g8278 [b8278 H8278]].
 intros [g8744 [b8744 H8744]].
 unfold writer_expr_8745.
 solve_writer_ready.
Qed.
Definition writer_expr_8746 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8276)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8745))).
Lemma writer_ready_8746 old :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8745 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8746.
Proof.
 intros [g8276 [b8276 H8276]].
 intros [g8745 [b8745 H8745]].
 unfold writer_expr_8746.
 solve_writer_ready.
Qed.
Definition writer_expr_8747 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8274)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8746))).
Lemma writer_ready_8747 old :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8746 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8747.
Proof.
 intros [g8274 [b8274 H8274]].
 intros [g8746 [b8746 H8746]].
 unfold writer_expr_8747.
 solve_writer_ready.
Qed.
Definition writer_expr_8748 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8272)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8747))).
Lemma writer_ready_8748 old :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8747 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8748.
Proof.
 intros [g8272 [b8272 H8272]].
 intros [g8747 [b8747 H8747]].
 unfold writer_expr_8748.
 solve_writer_ready.
Qed.
Definition writer_expr_8749 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8270)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8748))).
Lemma writer_ready_8749 old :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8748 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8749.
Proof.
 intros [g8270 [b8270 H8270]].
 intros [g8748 [b8748 H8748]].
 unfold writer_expr_8749.
 solve_writer_ready.
Qed.
Definition writer_expr_8750 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8268)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8749))).
Lemma writer_ready_8750 old :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8749 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8750.
Proof.
 intros [g8268 [b8268 H8268]].
 intros [g8749 [b8749 H8749]].
 unfold writer_expr_8750.
 solve_writer_ready.
Qed.
Definition writer_expr_8751 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8266)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8750))).
Lemma writer_ready_8751 old :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8750 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8751.
Proof.
 intros [g8266 [b8266 H8266]].
 intros [g8750 [b8750 H8750]].
 unfold writer_expr_8751.
 solve_writer_ready.
Qed.
Definition writer_expr_8752 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8264)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8751))).
Lemma writer_ready_8752 old :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8751 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8752.
Proof.
 intros [g8264 [b8264 H8264]].
 intros [g8751 [b8751 H8751]].
 unfold writer_expr_8752.
 solve_writer_ready.
Qed.
Definition writer_expr_8753 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8360)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Econst VarOrder.T (Fuint 3) [::false; false; false])).
Lemma writer_ready_8753 old :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8753.
Proof.
 intros [g8360 [b8360 H8360]].
 unfold writer_expr_8753.
 solve_writer_ready.
Qed.
Definition writer_expr_8754 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8358)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8753))).
Lemma writer_ready_8754 old :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8753 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8754.
Proof.
 intros [g8358 [b8358 H8358]].
 intros [g8753 [b8753 H8753]].
 unfold writer_expr_8754.
 solve_writer_ready.
Qed.
Definition writer_expr_8755 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8356)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8754))).
Lemma writer_ready_8755 old :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8754 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8755.
Proof.
 intros [g8356 [b8356 H8356]].
 intros [g8754 [b8754 H8754]].
 unfold writer_expr_8755.
 solve_writer_ready.
Qed.
Definition writer_expr_8756 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8354)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8755))).
Lemma writer_ready_8756 old :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8755 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8756.
Proof.
 intros [g8354 [b8354 H8354]].
 intros [g8755 [b8755 H8755]].
 unfold writer_expr_8756.
 solve_writer_ready.
Qed.
Definition writer_expr_8757 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8352)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8756))).
Lemma writer_ready_8757 old :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8756 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8757.
Proof.
 intros [g8352 [b8352 H8352]].
 intros [g8756 [b8756 H8756]].
 unfold writer_expr_8757.
 solve_writer_ready.
Qed.
Definition writer_expr_8758 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8350)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8757))).
Lemma writer_ready_8758 old :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8757 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8758.
Proof.
 intros [g8350 [b8350 H8350]].
 intros [g8757 [b8757 H8757]].
 unfold writer_expr_8758.
 solve_writer_ready.
Qed.
Definition writer_expr_8759 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8348)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8758))).
Lemma writer_ready_8759 old :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8758 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8759.
Proof.
 intros [g8348 [b8348 H8348]].
 intros [g8758 [b8758 H8758]].
 unfold writer_expr_8759.
 solve_writer_ready.
Qed.
Definition writer_expr_8760 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8346)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8759))).
Lemma writer_ready_8760 old :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8759 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8760.
Proof.
 intros [g8346 [b8346 H8346]].
 intros [g8759 [b8759 H8759]].
 unfold writer_expr_8760.
 solve_writer_ready.
Qed.
Definition writer_expr_8761 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8344)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8760))).
Lemma writer_ready_8761 old :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8760 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8761.
Proof.
 intros [g8344 [b8344 H8344]].
 intros [g8760 [b8760 H8760]].
 unfold writer_expr_8761.
 solve_writer_ready.
Qed.
Definition writer_expr_8762 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8342)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8761))).
Lemma writer_ready_8762 old :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8761 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8762.
Proof.
 intros [g8342 [b8342 H8342]].
 intros [g8761 [b8761 H8761]].
 unfold writer_expr_8762.
 solve_writer_ready.
Qed.
Definition writer_expr_8763 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8340)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8762))).
Lemma writer_ready_8763 old :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8762 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8763.
Proof.
 intros [g8340 [b8340 H8340]].
 intros [g8762 [b8762 H8762]].
 unfold writer_expr_8763.
 solve_writer_ready.
Qed.
Definition writer_expr_8764 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8338)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8763))).
Lemma writer_ready_8764 old :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8763 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8764.
Proof.
 intros [g8338 [b8338 H8338]].
 intros [g8763 [b8763 H8763]].
 unfold writer_expr_8764.
 solve_writer_ready.
Qed.
Definition writer_expr_8765 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8336)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8764))).
Lemma writer_ready_8765 old :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8764 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8765.
Proof.
 intros [g8336 [b8336 H8336]].
 intros [g8764 [b8764 H8764]].
 unfold writer_expr_8765.
 solve_writer_ready.
Qed.
Definition writer_expr_8766 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8334)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8765))).
Lemma writer_ready_8766 old :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8765 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8766.
Proof.
 intros [g8334 [b8334 H8334]].
 intros [g8765 [b8765 H8765]].
 unfold writer_expr_8766.
 solve_writer_ready.
Qed.
Definition writer_expr_8767 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8332)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8766))).
Lemma writer_ready_8767 old :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8766 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8767.
Proof.
 intros [g8332 [b8332 H8332]].
 intros [g8766 [b8766 H8766]].
 unfold writer_expr_8767.
 solve_writer_ready.
Qed.
Definition writer_expr_8768 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8330)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8767))).
Lemma writer_ready_8768 old :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8767 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8768.
Proof.
 intros [g8330 [b8330 H8330]].
 intros [g8767 [b8767 H8767]].
 unfold writer_expr_8768.
 solve_writer_ready.
Qed.
Definition writer_expr_8769 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8328)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8768))).
Lemma writer_ready_8769 old :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8768 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8769.
Proof.
 intros [g8328 [b8328 H8328]].
 intros [g8768 [b8768 H8768]].
 unfold writer_expr_8769.
 solve_writer_ready.
Qed.
Definition writer_expr_8770 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8326)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8769))).
Lemma writer_ready_8770 old :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8769 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8770.
Proof.
 intros [g8326 [b8326 H8326]].
 intros [g8769 [b8769 H8769]].
 unfold writer_expr_8770.
 solve_writer_ready.
Qed.
Definition writer_expr_8771 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8324)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8770))).
Lemma writer_ready_8771 old :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8770 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8771.
Proof.
 intros [g8324 [b8324 H8324]].
 intros [g8770 [b8770 H8770]].
 unfold writer_expr_8771.
 solve_writer_ready.
Qed.
Definition writer_expr_8772 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8322)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8771))).
Lemma writer_ready_8772 old :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8771 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8772.
Proof.
 intros [g8322 [b8322 H8322]].
 intros [g8771 [b8771 H8771]].
 unfold writer_expr_8772.
 solve_writer_ready.
Qed.
Definition writer_expr_8773 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8320)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8772))).
Lemma writer_ready_8773 old :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8772 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8773.
Proof.
 intros [g8320 [b8320 H8320]].
 intros [g8772 [b8772 H8772]].
 unfold writer_expr_8773.
 solve_writer_ready.
Qed.
Definition writer_expr_8774 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8318)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8773))).
Lemma writer_ready_8774 old :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8773 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8774.
Proof.
 intros [g8318 [b8318 H8318]].
 intros [g8773 [b8773 H8773]].
 unfold writer_expr_8774.
 solve_writer_ready.
Qed.
Definition writer_expr_8775 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8316)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8774))).
Lemma writer_ready_8775 old :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8774 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8775.
Proof.
 intros [g8316 [b8316 H8316]].
 intros [g8774 [b8774 H8774]].
 unfold writer_expr_8775.
 solve_writer_ready.
Qed.
Definition writer_expr_8776 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8314)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8775))).
Lemma writer_ready_8776 old :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8775 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8776.
Proof.
 intros [g8314 [b8314 H8314]].
 intros [g8775 [b8775 H8775]].
 unfold writer_expr_8776.
 solve_writer_ready.
Qed.
Definition writer_expr_8777 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8312)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8776))).
Lemma writer_ready_8777 old :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8776 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8777.
Proof.
 intros [g8312 [b8312 H8312]].
 intros [g8776 [b8776 H8776]].
 unfold writer_expr_8777.
 solve_writer_ready.
Qed.
Definition writer_expr_8778 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8310)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8777))).
Lemma writer_ready_8778 old :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8777 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8778.
Proof.
 intros [g8310 [b8310 H8310]].
 intros [g8777 [b8777 H8777]].
 unfold writer_expr_8778.
 solve_writer_ready.
Qed.
Definition writer_expr_8779 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8308)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8778))).
Lemma writer_ready_8779 old :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8778 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8779.
Proof.
 intros [g8308 [b8308 H8308]].
 intros [g8778 [b8778 H8778]].
 unfold writer_expr_8779.
 solve_writer_ready.
Qed.
Definition writer_expr_8780 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8306)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8779))).
Lemma writer_ready_8780 old :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8779 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8780.
Proof.
 intros [g8306 [b8306 H8306]].
 intros [g8779 [b8779 H8779]].
 unfold writer_expr_8780.
 solve_writer_ready.
Qed.
Definition writer_expr_8781 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8304)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8780))).
Lemma writer_ready_8781 old :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8780 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8781.
Proof.
 intros [g8304 [b8304 H8304]].
 intros [g8780 [b8780 H8780]].
 unfold writer_expr_8781.
 solve_writer_ready.
Qed.
Definition writer_expr_8782 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8302)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8781))).
Lemma writer_ready_8782 old :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8781 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8782.
Proof.
 intros [g8302 [b8302 H8302]].
 intros [g8781 [b8781 H8781]].
 unfold writer_expr_8782.
 solve_writer_ready.
Qed.
Definition writer_expr_8783 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8300)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8782))).
Lemma writer_ready_8783 old :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8782 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8783.
Proof.
 intros [g8300 [b8300 H8300]].
 intros [g8782 [b8782 H8782]].
 unfold writer_expr_8783.
 solve_writer_ready.
Qed.
Definition writer_expr_8784 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8298)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8783))).
Lemma writer_ready_8784 old :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8783 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8784.
Proof.
 intros [g8298 [b8298 H8298]].
 intros [g8783 [b8783 H8783]].
 unfold writer_expr_8784.
 solve_writer_ready.
Qed.
Definition writer_expr_8785 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8296)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8784))).
Lemma writer_ready_8785 old :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8784 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8785.
Proof.
 intros [g8296 [b8296 H8296]].
 intros [g8784 [b8784 H8784]].
 unfold writer_expr_8785.
 solve_writer_ready.
Qed.
Definition writer_expr_8786 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8294)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8785))).
Lemma writer_ready_8786 old :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8785 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8786.
Proof.
 intros [g8294 [b8294 H8294]].
 intros [g8785 [b8785 H8785]].
 unfold writer_expr_8786.
 solve_writer_ready.
Qed.
Definition writer_expr_8787 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8292)) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8786))).
Lemma writer_ready_8787 old :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8786 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8787.
Proof.
 intros [g8292 [b8292 H8292]].
 intros [g8786 [b8786 H8786]].
 unfold writer_expr_8787.
 solve_writer_ready.
Qed.
Definition writer_expr_8788 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8290)) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8787))).
Lemma writer_ready_8788 old :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8787 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8788.
Proof.
 intros [g8290 [b8290 H8290]].
 intros [g8787 [b8787 H8787]].
 unfold writer_expr_8788.
 solve_writer_ready.
Qed.
Definition writer_expr_8789 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8288)) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8788))).
Lemma writer_ready_8789 old :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8788 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8789.
Proof.
 intros [g8288 [b8288 H8288]].
 intros [g8788 [b8788 H8788]].
 unfold writer_expr_8789.
 solve_writer_ready.
Qed.
Definition writer_expr_8790 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8286)) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8789))).
Lemma writer_ready_8790 old :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8789 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8790.
Proof.
 intros [g8286 [b8286 H8286]].
 intros [g8789 [b8789 H8789]].
 unfold writer_expr_8790.
 solve_writer_ready.
Qed.
Definition writer_expr_8791 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8284)) (@Econst VarOrder.T (Fuint 3) [::true; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8790))).
Lemma writer_ready_8791 old :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8790 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8791.
Proof.
 intros [g8284 [b8284 H8284]].
 intros [g8790 [b8790 H8790]].
 unfold writer_expr_8791.
 solve_writer_ready.
Qed.
Definition writer_expr_8792 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8282)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8791))).
Lemma writer_ready_8792 old :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8791 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8792.
Proof.
 intros [g8282 [b8282 H8282]].
 intros [g8791 [b8791 H8791]].
 unfold writer_expr_8792.
 solve_writer_ready.
Qed.
Definition writer_expr_8793 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8280)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8792))).
Lemma writer_ready_8793 old :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8792 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8793.
Proof.
 intros [g8280 [b8280 H8280]].
 intros [g8792 [b8792 H8792]].
 unfold writer_expr_8793.
 solve_writer_ready.
Qed.
Definition writer_expr_8794 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8278)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8793))).
Lemma writer_ready_8794 old :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8793 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8794.
Proof.
 intros [g8278 [b8278 H8278]].
 intros [g8793 [b8793 H8793]].
 unfold writer_expr_8794.
 solve_writer_ready.
Qed.
Definition writer_expr_8795 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8276)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8794))).
Lemma writer_ready_8795 old :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8794 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8795.
Proof.
 intros [g8276 [b8276 H8276]].
 intros [g8794 [b8794 H8794]].
 unfold writer_expr_8795.
 solve_writer_ready.
Qed.
Definition writer_expr_8796 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8274)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8795))).
Lemma writer_ready_8796 old :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8795 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8796.
Proof.
 intros [g8274 [b8274 H8274]].
 intros [g8795 [b8795 H8795]].
 unfold writer_expr_8796.
 solve_writer_ready.
Qed.
Definition writer_expr_8797 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8272)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8796))).
Lemma writer_ready_8797 old :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8796 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8797.
Proof.
 intros [g8272 [b8272 H8272]].
 intros [g8796 [b8796 H8796]].
 unfold writer_expr_8797.
 solve_writer_ready.
Qed.
Definition writer_expr_8798 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8270)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8797))).
Lemma writer_ready_8798 old :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8797 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8798.
Proof.
 intros [g8270 [b8270 H8270]].
 intros [g8797 [b8797 H8797]].
 unfold writer_expr_8798.
 solve_writer_ready.
Qed.
Definition writer_expr_8799 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8268)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8798))).
Lemma writer_ready_8799 old :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8798 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8799.
Proof.
 intros [g8268 [b8268 H8268]].
 intros [g8798 [b8798 H8798]].
 unfold writer_expr_8799.
 solve_writer_ready.
Qed.
Definition writer_expr_8800 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8266)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8799))).
Lemma writer_ready_8800 old :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8799 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8800.
Proof.
 intros [g8266 [b8266 H8266]].
 intros [g8799 [b8799 H8799]].
 unfold writer_expr_8800.
 solve_writer_ready.
Qed.
Definition writer_expr_8801 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8264)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8800))).
Lemma writer_ready_8801 old :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8800 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_8801.
Proof.
 intros [g8264 [b8264 H8264]].
 intros [g8800 [b8800 H8800]].
 unfold writer_expr_8801.
 solve_writer_ready.
Qed.
Definition writer_expr_9183 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 39))).
Lemma writer_ready_9183 old :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9183.
Proof.
 intros [g39 [b39 H39]].
 unfold writer_expr_9183.
 solve_writer_ready.
Qed.
Definition writer_expr_9184 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 36)) (@Eref VarOrder.T (@Eid VarOrder.T 9183))).
Lemma writer_ready_9184 old :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9183 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9184.
Proof.
 intros [g36 [b36 H36]].
 intros [g9183 [b9183 H9183]].
 unfold writer_expr_9184.
 solve_writer_ready.
Qed.
Definition writer_expr_9185 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 9184))).
Lemma writer_ready_9185 old :
 (exists ground bits, VM.find 9184 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9185.
Proof.
 intros [g9184 [b9184 H9184]].
 unfold writer_expr_9185.
 solve_writer_ready.
Qed.
Definition writer_expr_9188 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 9187))).
Lemma writer_ready_9188 old :
 (exists ground bits, VM.find 9187 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9188.
Proof.
 intros [g9187 [b9187 H9187]].
 unfold writer_expr_9188.
 solve_writer_ready.
Qed.
Definition writer_expr_9189 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 9188)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma writer_ready_9189 old :
 (exists ground bits, VM.find 9188 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9189.
Proof.
 intros [g9188 [b9188 H9188]].
 unfold writer_expr_9189.
 solve_writer_ready.
Qed.
Definition writer_expr_9190 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 9189))).
Lemma writer_ready_9190 old :
 (exists ground bits, VM.find 9189 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9190.
Proof.
 intros [g9189 [b9189 H9189]].
 unfold writer_expr_9190.
 solve_writer_ready.
Qed.
Definition writer_expr_9191 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 39))).
Lemma writer_ready_9191 old :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9191.
Proof.
 intros [g39 [b39 H39]].
 unfold writer_expr_9191.
 solve_writer_ready.
Qed.
Definition writer_expr_9192 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 36)) (@Eref VarOrder.T (@Eid VarOrder.T 9191))).
Lemma writer_ready_9192 old :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9191 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9192.
Proof.
 intros [g36 [b36 H36]].
 intros [g9191 [b9191 H9191]].
 unfold writer_expr_9192.
 solve_writer_ready.
Qed.
Definition writer_expr_9193 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 9192))).
Lemma writer_ready_9193 old :
 (exists ground bits, VM.find 9192 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9193.
Proof.
 intros [g9192 [b9192 H9192]].
 unfold writer_expr_9193.
 solve_writer_ready.
Qed.
Definition writer_expr_9196 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 8) (@Eref VarOrder.T (@Eid VarOrder.T 9195))).
Lemma writer_ready_9196 old :
 (exists ground bits, VM.find 9195 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9196.
Proof.
 intros [g9195 [b9195 H9195]].
 unfold writer_expr_9196.
 solve_writer_ready.
Qed.
Definition writer_expr_9197 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 9196)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])).
Lemma writer_ready_9197 old :
 (exists ground bits, VM.find 9196 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9197.
Proof.
 intros [g9196 [b9196 H9196]].
 unfold writer_expr_9197.
 solve_writer_ready.
Qed.
Definition writer_expr_9198 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9190)) (@Eref VarOrder.T (@Eid VarOrder.T 9197))).
Lemma writer_ready_9198 old :
 (exists ground bits, VM.find 9190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9197 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9198.
Proof.
 intros [g9190 [b9190 H9190]].
 intros [g9197 [b9197 H9197]].
 unfold writer_expr_9198.
 solve_writer_ready.
Qed.
Definition writer_expr_9199 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 39))).
Lemma writer_ready_9199 old :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9199.
Proof.
 intros [g39 [b39 H39]].
 unfold writer_expr_9199.
 solve_writer_ready.
Qed.
Definition writer_expr_9200 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 36)) (@Eref VarOrder.T (@Eid VarOrder.T 9199))).
Lemma writer_ready_9200 old :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9199 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9200.
Proof.
 intros [g36 [b36 H36]].
 intros [g9199 [b9199 H9199]].
 unfold writer_expr_9200.
 solve_writer_ready.
Qed.
Definition writer_expr_9201 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 9200))).
Lemma writer_ready_9201 old :
 (exists ground bits, VM.find 9200 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9201.
Proof.
 intros [g9200 [b9200 H9200]].
 unfold writer_expr_9201.
 solve_writer_ready.
Qed.
Definition writer_expr_9204 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 23 16) (@Eref VarOrder.T (@Eid VarOrder.T 9203))).
Lemma writer_ready_9204 old :
 (exists ground bits, VM.find 9203 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9204.
Proof.
 intros [g9203 [b9203 H9203]].
 unfold writer_expr_9204.
 solve_writer_ready.
Qed.
Definition writer_expr_9205 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 9204)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true])).
Lemma writer_ready_9205 old :
 (exists ground bits, VM.find 9204 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9205.
Proof.
 intros [g9204 [b9204 H9204]].
 unfold writer_expr_9205.
 solve_writer_ready.
Qed.
Definition writer_expr_9206 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9198)) (@Eref VarOrder.T (@Eid VarOrder.T 9205))).
Lemma writer_ready_9206 old :
 (exists ground bits, VM.find 9198 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9205 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9206.
Proof.
 intros [g9198 [b9198 H9198]].
 intros [g9205 [b9205 H9205]].
 unfold writer_expr_9206.
 solve_writer_ready.
Qed.
Definition writer_expr_9207 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 39))).
Lemma writer_ready_9207 old :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9207.
Proof.
 intros [g39 [b39 H39]].
 unfold writer_expr_9207.
 solve_writer_ready.
Qed.
Definition writer_expr_9208 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 36)) (@Eref VarOrder.T (@Eid VarOrder.T 9207))).
Lemma writer_ready_9208 old :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9207 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9208.
Proof.
 intros [g36 [b36 H36]].
 intros [g9207 [b9207 H9207]].
 unfold writer_expr_9208.
 solve_writer_ready.
Qed.
Definition writer_expr_9209 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 9208))).
Lemma writer_ready_9209 old :
 (exists ground bits, VM.find 9208 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9209.
Proof.
 intros [g9208 [b9208 H9208]].
 unfold writer_expr_9209.
 solve_writer_ready.
Qed.
Definition writer_expr_9212 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 24) (@Eref VarOrder.T (@Eid VarOrder.T 9211))).
Lemma writer_ready_9212 old :
 (exists ground bits, VM.find 9211 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9212.
Proof.
 intros [g9211 [b9211 H9211]].
 unfold writer_expr_9212.
 solve_writer_ready.
Qed.
Definition writer_expr_9213 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 9212)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; true; true])).
Lemma writer_ready_9213 old :
 (exists ground bits, VM.find 9212 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9213.
Proof.
 intros [g9212 [b9212 H9212]].
 unfold writer_expr_9213.
 solve_writer_ready.
Qed.
Definition writer_expr_9214 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9206)) (@Eref VarOrder.T (@Eid VarOrder.T 9213))).
Lemma writer_ready_9214 old :
 (exists ground bits, VM.find 9206 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9213 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9214.
Proof.
 intros [g9206 [b9206 H9206]].
 intros [g9213 [b9213 H9213]].
 unfold writer_expr_9214.
 solve_writer_ready.
Qed.
Definition writer_expr_9223 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 39))).
Lemma writer_ready_9223 old :
 (exists ground bits, VM.find 39 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9223.
Proof.
 intros [g39 [b39 H39]].
 unfold writer_expr_9223.
 solve_writer_ready.
Qed.
Definition writer_expr_9224 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 9182))).
Lemma writer_ready_9224 old :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9224.
Proof.
 intros [g9182 [b9182 H9182]].
 unfold writer_expr_9224.
 solve_writer_ready.
Qed.
Definition writer_expr_9225 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 9223)) (@Eref VarOrder.T (@Eid VarOrder.T 9224))).
Lemma writer_ready_9225 old :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9224 old = Some (Gval (Fuint ground) bits)) ->
 concrete_expression_ready old writer_expr_9225.
Proof.
 intros [g9223 [b9223 H9223]].
 intros [g9224 [b9224 H9224]].
 unfold writer_expr_9225.
 eapply closure_validif with (width := g9224); [solve_writer_ready|solve_writer_ready|].
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9224. reflexivity.
Qed.
Definition writer_expr_9227 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 9223)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma writer_ready_9227 old :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9227.
Proof.
 intros [g9223 [b9223 H9223]].
 unfold writer_expr_9227.
 solve_writer_ready.
Qed.
Definition writer_expr_9228 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 9223)) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma writer_ready_9228 old :
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9228.
Proof.
 intros [g9223 [b9223 H9223]].
 unfold writer_expr_9228.
 eapply closure_validif with (width := 1%nat); [solve_writer_ready|solve_writer_ready|reflexivity].
Qed.
Definition writer_expr_9229 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 9223)) (@Eref VarOrder.T (@Eid VarOrder.T 9214))).
Lemma writer_ready_9229 old :
 (exists ground bits, VM.find 9214 old = Some (Gval (Fuint ground) bits)) ->
 (exists ground bits, VM.find 9223 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9229.
Proof.
 intros [g9214 [b9214 H9214]].
 intros [g9223 [b9223 H9223]].
 unfold writer_expr_9229.
 eapply closure_validif with (width := g9214); [solve_writer_ready|solve_writer_ready|].
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9214. reflexivity.
Qed.
Definition writer_expr_9230 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 36)) (@Eref VarOrder.T (@Eid VarOrder.T 9225))).
Lemma writer_ready_9230 old :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9225 old = Some (Gval (Fuint ground) bits)) ->
 concrete_expression_ready old writer_expr_9230.
Proof.
 intros [g36 [b36 H36]].
 intros [g9225 [b9225 H9225]].
 unfold writer_expr_9230.
 eapply closure_validif with (width := g9225); [solve_writer_ready|solve_writer_ready|].
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9225. reflexivity.
Qed.
Definition writer_expr_9232 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 36)) (@Eref VarOrder.T (@Eid VarOrder.T 9227)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma writer_ready_9232 old :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9227 old = Some (Gval ground bits)) ->
 concrete_expression_ready old writer_expr_9232.
Proof.
 intros [g36 [b36 H36]].
 intros [g9227 [b9227 H9227]].
 unfold writer_expr_9232.
 solve_writer_ready.
Qed.
Definition writer_expr_9233 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 36)) (@Eref VarOrder.T (@Eid VarOrder.T 9228))).
Lemma writer_ready_9233 old :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9228 old = Some (Gval (Fuint ground) bits)) ->
 concrete_expression_ready old writer_expr_9233.
Proof.
 intros [g36 [b36 H36]].
 intros [g9228 [b9228 H9228]].
 unfold writer_expr_9233.
 eapply closure_validif with (width := g9228); [solve_writer_ready|solve_writer_ready|].
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9228. reflexivity.
Qed.
Definition writer_expr_9234 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 36)) (@Eref VarOrder.T (@Eid VarOrder.T 9229))).
Lemma writer_ready_9234 old :
 (exists ground bits, VM.find 36 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 9229 old = Some (Gval (Fuint ground) bits)) ->
 concrete_expression_ready old writer_expr_9234.
Proof.
 intros [g36 [b36 H36]].
 intros [g9229 [b9229 H9229]].
 unfold writer_expr_9234.
 eapply closure_validif with (width := g9229); [solve_writer_ready|solve_writer_ready|].
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H9229. reflexivity.
Qed.
