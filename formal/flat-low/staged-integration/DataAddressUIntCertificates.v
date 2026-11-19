Require Import DataAddressExpressionCertificates ConcreteUIntOperations ConcreteUIntScalarExpressions ConcreteUIntValidIf.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Ltac solve_address_uint_ready :=
 repeat first [eapply uint_ready_ref; eassumption | apply uint_ready_const
 | apply uint_ready_unary; [reflexivity|] | apply uint_ready_binary].
Lemma address_uint_result_883 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_883 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 apply formal_uint_scalar_concrete. unfold address_expr_883. solve_address_uint_ready.
Qed.
Lemma address_uint_result_884 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 851 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_884 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w851 [b851 H851]].
 unfold address_expr_884. eapply formal_uint_validif_concrete with (width := w851); [solve_address_uint_ready|solve_address_uint_ready|].
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H851. reflexivity.
Qed.
Lemma address_uint_result_885 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 852 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 884 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_885 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w852 [b852 H852]].
 intros [w884 [b884 H884]].
 intro Eval. unfold address_expr_885 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H852 ?H884 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H852 ?H884 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_886 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 853 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 885 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_886 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w853 [b853 H853]].
 intros [w885 [b885 H885]].
 intro Eval. unfold address_expr_886 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H853 ?H885 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H853 ?H885 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_887 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 854 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 886 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_887 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w854 [b854 H854]].
 intros [w886 [b886 H886]].
 intro Eval. unfold address_expr_887 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H854 ?H886 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H854 ?H886 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_888 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 855 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 887 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_888 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w855 [b855 H855]].
 intros [w887 [b887 H887]].
 intro Eval. unfold address_expr_888 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H855 ?H887 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H855 ?H887 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_889 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 856 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 888 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_889 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w856 [b856 H856]].
 intros [w888 [b888 H888]].
 intro Eval. unfold address_expr_889 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H856 ?H888 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H856 ?H888 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_890 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 857 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 889 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_890 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w857 [b857 H857]].
 intros [w889 [b889 H889]].
 intro Eval. unfold address_expr_890 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H857 ?H889 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H857 ?H889 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_891 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 858 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 890 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_891 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w858 [b858 H858]].
 intros [w890 [b890 H890]].
 intro Eval. unfold address_expr_891 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H858 ?H890 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H858 ?H890 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_892 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 859 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 891 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_892 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w859 [b859 H859]].
 intros [w891 [b891 H891]].
 intro Eval. unfold address_expr_892 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H859 ?H891 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H859 ?H891 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_893 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 860 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 892 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_893 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w860 [b860 H860]].
 intros [w892 [b892 H892]].
 intro Eval. unfold address_expr_893 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H860 ?H892 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H860 ?H892 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_894 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 861 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 893 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_894 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w861 [b861 H861]].
 intros [w893 [b893 H893]].
 intro Eval. unfold address_expr_894 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H861 ?H893 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H861 ?H893 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_895 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 862 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 894 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_895 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w862 [b862 H862]].
 intros [w894 [b894 H894]].
 intro Eval. unfold address_expr_895 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H862 ?H894 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H862 ?H894 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_896 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 863 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 895 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_896 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w863 [b863 H863]].
 intros [w895 [b895 H895]].
 intro Eval. unfold address_expr_896 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H863 ?H895 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H863 ?H895 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_897 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 864 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 896 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_897 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w864 [b864 H864]].
 intros [w896 [b896 H896]].
 intro Eval. unfold address_expr_897 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H864 ?H896 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H864 ?H896 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_898 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 865 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 897 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_898 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w865 [b865 H865]].
 intros [w897 [b897 H897]].
 intro Eval. unfold address_expr_898 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H865 ?H897 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H865 ?H897 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_899 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 866 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 898 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_899 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w866 [b866 H866]].
 intros [w898 [b898 H898]].
 intro Eval. unfold address_expr_899 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H866 ?H898 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H866 ?H898 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_900 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 867 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 899 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_900 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w867 [b867 H867]].
 intros [w899 [b899 H899]].
 intro Eval. unfold address_expr_900 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H867 ?H899 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H867 ?H899 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_901 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 868 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 900 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_901 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w868 [b868 H868]].
 intros [w900 [b900 H900]].
 intro Eval. unfold address_expr_901 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H868 ?H900 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H868 ?H900 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_902 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 869 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 901 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_902 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w869 [b869 H869]].
 intros [w901 [b901 H901]].
 intro Eval. unfold address_expr_902 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H869 ?H901 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H869 ?H901 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_903 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 870 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 902 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_903 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w870 [b870 H870]].
 intros [w902 [b902 H902]].
 intro Eval. unfold address_expr_903 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H870 ?H902 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H870 ?H902 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_904 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 871 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 903 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_904 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w871 [b871 H871]].
 intros [w903 [b903 H903]].
 intro Eval. unfold address_expr_904 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H871 ?H903 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H871 ?H903 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_905 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 872 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 904 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_905 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w872 [b872 H872]].
 intros [w904 [b904 H904]].
 intro Eval. unfold address_expr_905 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H872 ?H904 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H872 ?H904 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_906 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 873 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 905 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_906 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w873 [b873 H873]].
 intros [w905 [b905 H905]].
 intro Eval. unfold address_expr_906 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H873 ?H905 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H873 ?H905 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_907 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 874 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 906 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_907 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w874 [b874 H874]].
 intros [w906 [b906 H906]].
 intro Eval. unfold address_expr_907 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H874 ?H906 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H874 ?H906 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_908 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 875 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 907 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_908 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w875 [b875 H875]].
 intros [w907 [b907 H907]].
 intro Eval. unfold address_expr_908 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H875 ?H907 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H875 ?H907 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_909 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 876 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 908 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_909 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w876 [b876 H876]].
 intros [w908 [b908 H908]].
 intro Eval. unfold address_expr_909 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H876 ?H908 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H876 ?H908 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_910 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 877 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 909 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_910 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w877 [b877 H877]].
 intros [w909 [b909 H909]].
 intro Eval. unfold address_expr_910 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H877 ?H909 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H877 ?H909 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_911 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 878 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 910 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_911 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w878 [b878 H878]].
 intros [w910 [b910 H910]].
 intro Eval. unfold address_expr_911 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H878 ?H910 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H878 ?H910 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_912 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 879 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 911 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_912 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w879 [b879 H879]].
 intros [w911 [b911 H911]].
 intro Eval. unfold address_expr_912 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H879 ?H911 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H879 ?H911 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_913 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 880 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 912 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_913 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w880 [b880 H880]].
 intros [w912 [b912 H912]].
 intro Eval. unfold address_expr_913 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H880 ?H912 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H880 ?H912 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_914 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 881 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 913 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_914 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w881 [b881 H881]].
 intros [w913 [b913 H913]].
 intro Eval. unfold address_expr_914 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H881 ?H913 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H881 ?H913 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_915 inputs path site mm old result :
 (exists width bits, VM.find 780 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 882 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 914 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_915 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w780 [b780 H780]].
 intros [w882 [b882 H882]].
 intros [w914 [b914 H914]].
 intro Eval. unfold address_expr_915 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H780 ?H882 ?H914 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H780 ?H882 ?H914 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_916 inputs path site mm old result :
 (exists width bits, VM.find 915 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_916 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w915 [b915 H915]].
 apply formal_uint_scalar_concrete. unfold address_expr_916. solve_address_uint_ready.
Qed.
Lemma address_uint_result_917 inputs path site mm old result :
 (exists width bits, VM.find 883 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 916 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_917 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w883 [b883 H883]].
 intros [w916 [b916 H916]].
 intro Eval. unfold address_expr_917 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H883 ?H916 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H883 ?H916 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_918 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_918 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 apply formal_uint_scalar_concrete. unfold address_expr_918. solve_address_uint_ready.
Qed.
Lemma address_uint_result_919 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 851 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_919 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w851 [b851 H851]].
 unfold address_expr_919. eapply formal_uint_validif_concrete with (width := w851); [solve_address_uint_ready|solve_address_uint_ready|].
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H851. reflexivity.
Qed.
Lemma address_uint_result_920 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 852 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 919 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_920 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w852 [b852 H852]].
 intros [w919 [b919 H919]].
 intro Eval. unfold address_expr_920 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H852 ?H919 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H852 ?H919 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_921 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 853 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 920 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_921 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w853 [b853 H853]].
 intros [w920 [b920 H920]].
 intro Eval. unfold address_expr_921 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H853 ?H920 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H853 ?H920 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_922 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 854 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 921 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_922 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w854 [b854 H854]].
 intros [w921 [b921 H921]].
 intro Eval. unfold address_expr_922 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H854 ?H921 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H854 ?H921 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_923 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 855 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 922 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_923 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w855 [b855 H855]].
 intros [w922 [b922 H922]].
 intro Eval. unfold address_expr_923 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H855 ?H922 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H855 ?H922 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_924 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 856 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 923 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_924 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w856 [b856 H856]].
 intros [w923 [b923 H923]].
 intro Eval. unfold address_expr_924 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H856 ?H923 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H856 ?H923 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_925 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 857 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 924 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_925 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w857 [b857 H857]].
 intros [w924 [b924 H924]].
 intro Eval. unfold address_expr_925 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H857 ?H924 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H857 ?H924 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_926 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 858 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 925 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_926 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w858 [b858 H858]].
 intros [w925 [b925 H925]].
 intro Eval. unfold address_expr_926 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H858 ?H925 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H858 ?H925 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_927 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 859 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 926 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_927 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w859 [b859 H859]].
 intros [w926 [b926 H926]].
 intro Eval. unfold address_expr_927 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H859 ?H926 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H859 ?H926 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_928 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 860 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 927 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_928 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w860 [b860 H860]].
 intros [w927 [b927 H927]].
 intro Eval. unfold address_expr_928 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H860 ?H927 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H860 ?H927 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_929 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 861 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 928 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_929 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w861 [b861 H861]].
 intros [w928 [b928 H928]].
 intro Eval. unfold address_expr_929 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H861 ?H928 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H861 ?H928 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_930 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 862 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 929 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_930 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w862 [b862 H862]].
 intros [w929 [b929 H929]].
 intro Eval. unfold address_expr_930 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H862 ?H929 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H862 ?H929 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_931 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 863 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 930 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_931 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w863 [b863 H863]].
 intros [w930 [b930 H930]].
 intro Eval. unfold address_expr_931 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H863 ?H930 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H863 ?H930 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_932 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 864 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 931 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_932 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w864 [b864 H864]].
 intros [w931 [b931 H931]].
 intro Eval. unfold address_expr_932 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H864 ?H931 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H864 ?H931 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_933 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 865 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 932 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_933 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w865 [b865 H865]].
 intros [w932 [b932 H932]].
 intro Eval. unfold address_expr_933 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H865 ?H932 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H865 ?H932 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_934 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 866 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 933 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_934 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w866 [b866 H866]].
 intros [w933 [b933 H933]].
 intro Eval. unfold address_expr_934 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H866 ?H933 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H866 ?H933 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_935 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 867 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 934 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_935 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w867 [b867 H867]].
 intros [w934 [b934 H934]].
 intro Eval. unfold address_expr_935 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H867 ?H934 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H867 ?H934 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_936 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 868 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 935 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_936 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w868 [b868 H868]].
 intros [w935 [b935 H935]].
 intro Eval. unfold address_expr_936 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H868 ?H935 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H868 ?H935 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_937 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 869 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 936 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_937 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w869 [b869 H869]].
 intros [w936 [b936 H936]].
 intro Eval. unfold address_expr_937 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H869 ?H936 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H869 ?H936 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_938 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 870 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 937 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_938 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w870 [b870 H870]].
 intros [w937 [b937 H937]].
 intro Eval. unfold address_expr_938 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H870 ?H937 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H870 ?H937 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_939 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 871 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 938 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_939 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w871 [b871 H871]].
 intros [w938 [b938 H938]].
 intro Eval. unfold address_expr_939 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H871 ?H938 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H871 ?H938 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_940 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 872 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 939 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_940 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w872 [b872 H872]].
 intros [w939 [b939 H939]].
 intro Eval. unfold address_expr_940 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H872 ?H939 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H872 ?H939 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_941 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 873 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 940 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_941 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w873 [b873 H873]].
 intros [w940 [b940 H940]].
 intro Eval. unfold address_expr_941 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H873 ?H940 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H873 ?H940 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_942 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 874 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 941 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_942 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w874 [b874 H874]].
 intros [w941 [b941 H941]].
 intro Eval. unfold address_expr_942 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H874 ?H941 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H874 ?H941 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_943 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 875 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 942 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_943 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w875 [b875 H875]].
 intros [w942 [b942 H942]].
 intro Eval. unfold address_expr_943 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H875 ?H942 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H875 ?H942 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_944 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 876 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 943 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_944 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w876 [b876 H876]].
 intros [w943 [b943 H943]].
 intro Eval. unfold address_expr_944 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H876 ?H943 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H876 ?H943 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_945 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 877 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 944 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_945 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w877 [b877 H877]].
 intros [w944 [b944 H944]].
 intro Eval. unfold address_expr_945 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H877 ?H944 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H877 ?H944 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_946 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 878 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 945 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_946 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w878 [b878 H878]].
 intros [w945 [b945 H945]].
 intro Eval. unfold address_expr_946 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H878 ?H945 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H878 ?H945 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_947 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 879 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 946 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_947 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w879 [b879 H879]].
 intros [w946 [b946 H946]].
 intro Eval. unfold address_expr_947 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H879 ?H946 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H879 ?H946 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_948 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 880 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 947 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_948 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w880 [b880 H880]].
 intros [w947 [b947 H947]].
 intro Eval. unfold address_expr_948 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H880 ?H947 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H880 ?H947 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_949 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 881 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 948 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_949 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w881 [b881 H881]].
 intros [w948 [b948 H948]].
 intro Eval. unfold address_expr_949 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H881 ?H948 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H881 ?H948 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_950 inputs path site mm old result :
 (exists width bits, VM.find 781 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 882 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 949 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_950 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w781 [b781 H781]].
 intros [w882 [b882 H882]].
 intros [w949 [b949 H949]].
 intro Eval. unfold address_expr_950 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H781 ?H882 ?H949 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H781 ?H882 ?H949 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_951 inputs path site mm old result :
 (exists width bits, VM.find 950 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_951 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w950 [b950 H950]].
 apply formal_uint_scalar_concrete. unfold address_expr_951. solve_address_uint_ready.
Qed.
Lemma address_uint_result_952 inputs path site mm old result :
 (exists width bits, VM.find 918 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 951 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_952 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w918 [b918 H918]].
 intros [w951 [b951 H951]].
 intro Eval. unfold address_expr_952 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H918 ?H951 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H918 ?H951 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_1156 inputs path site mm old result :
 (exists width bits, VM.find 1153 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1156 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1153 [b1153 H1153]].
 apply formal_uint_scalar_concrete. unfold address_expr_1156. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1157 inputs path site mm old result :
 (exists width bits, VM.find 1152 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1157 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1152 [b1152 H1152]].
 apply formal_uint_scalar_concrete. unfold address_expr_1157. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1159 inputs path site mm old result :
 (exists width bits, VM.find 1152 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1156 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1158 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1159 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1152 [b1152 H1152]].
 intros [w1156 [b1156 H1156]].
 intros [w1158 [b1158 H1158]].
 intro Eval. unfold address_expr_1159 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H1152 ?H1156 ?H1158 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H1152 ?H1156 ?H1158 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_1160 inputs path site mm old result :
 (exists width bits, VM.find 1151 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1159 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1160 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1151 [b1151 H1151]].
 intros [w1159 [b1159 H1159]].
 apply formal_uint_scalar_concrete. unfold address_expr_1160. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1309 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1309 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1309. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1311 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1311 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1311. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1312 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1312 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1312. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1313 inputs path site mm old result :
 (exists width bits, VM.find 1311 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1312 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1313 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1311 [b1311 H1311]].
 intros [w1312 [b1312 H1312]].
 apply formal_uint_scalar_concrete. unfold address_expr_1313. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1315 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1315 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1315. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1316 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1316 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1316. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1317 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1317 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1317. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1318 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1318 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1318. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1319 inputs path site mm old result :
 (exists width bits, VM.find 1318 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1319 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1318 [b1318 H1318]].
 apply formal_uint_scalar_concrete. unfold address_expr_1319. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1320 inputs path site mm old result :
 (exists width bits, VM.find 1315 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1316 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1320 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1315 [b1315 H1315]].
 intros [w1316 [b1316 H1316]].
 apply formal_uint_scalar_concrete. unfold address_expr_1320. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1321 inputs path site mm old result :
 (exists width bits, VM.find 1317 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1320 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1321 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1317 [b1317 H1317]].
 intros [w1320 [b1320 H1320]].
 apply formal_uint_scalar_concrete. unfold address_expr_1321. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1322 inputs path site mm old result :
 (exists width bits, VM.find 1319 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1321 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1322 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1319 [b1319 H1319]].
 intros [w1321 [b1321 H1321]].
 apply formal_uint_scalar_concrete. unfold address_expr_1322. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1324 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1324 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1324. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1325 inputs path site mm old result :
 (exists width bits, VM.find 1324 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1325 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1324 [b1324 H1324]].
 apply formal_uint_scalar_concrete. unfold address_expr_1325. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1327 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1327 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1327. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1328 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1328 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1328. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1329 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1329 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1329. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1330 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1330 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1330. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1331 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1331 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1331. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1332 inputs path site mm old result :
 (exists width bits, VM.find 1330 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1331 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1332 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1330 [b1330 H1330]].
 intros [w1331 [b1331 H1331]].
 apply formal_uint_scalar_concrete. unfold address_expr_1332. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1333 inputs path site mm old result :
 (exists width bits, VM.find 1332 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1333 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1332 [b1332 H1332]].
 apply formal_uint_scalar_concrete. unfold address_expr_1333. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1334 inputs path site mm old result :
 (exists width bits, VM.find 1327 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1328 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1334 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1327 [b1327 H1327]].
 intros [w1328 [b1328 H1328]].
 apply formal_uint_scalar_concrete. unfold address_expr_1334. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1335 inputs path site mm old result :
 (exists width bits, VM.find 1329 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1334 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1335 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1329 [b1329 H1329]].
 intros [w1334 [b1334 H1334]].
 apply formal_uint_scalar_concrete. unfold address_expr_1335. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1336 inputs path site mm old result :
 (exists width bits, VM.find 1333 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1335 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1336 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1333 [b1333 H1333]].
 intros [w1335 [b1335 H1335]].
 apply formal_uint_scalar_concrete. unfold address_expr_1336. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1338 inputs path site mm old result :
 (exists width bits, VM.find 1306 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1338 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1306 [b1306 H1306]].
 apply formal_uint_scalar_concrete. unfold address_expr_1338. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1342 inputs path site mm old result :
 (exists width bits, VM.find 1307 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1342 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1307 [b1307 H1307]].
 apply formal_uint_scalar_concrete. unfold address_expr_1342. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1343 inputs path site mm old result :
 (exists width bits, VM.find 1310 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1341 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1342 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1343 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1310 [b1310 H1310]].
 intros [w1341 [b1341 H1341]].
 intros [w1342 [b1342 H1342]].
 intro Eval. unfold address_expr_1343 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H1310 ?H1341 ?H1342 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H1310 ?H1341 ?H1342 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_1344 inputs path site mm old result :
 (exists width bits, VM.find 1307 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1344 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1307 [b1307 H1307]].
 apply formal_uint_scalar_concrete. unfold address_expr_1344. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1345 inputs path site mm old result :
 (exists width bits, VM.find 1314 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1343 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1344 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1345 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1314 [b1314 H1314]].
 intros [w1343 [b1343 H1343]].
 intros [w1344 [b1344 H1344]].
 intro Eval. unfold address_expr_1345 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H1314 ?H1343 ?H1344 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H1314 ?H1343 ?H1344 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_1346 inputs path site mm old result :
 (exists width bits, VM.find 1307 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1346 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1307 [b1307 H1307]].
 apply formal_uint_scalar_concrete. unfold address_expr_1346. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1347 inputs path site mm old result :
 (exists width bits, VM.find 1323 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1345 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1346 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1347 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1323 [b1323 H1323]].
 intros [w1345 [b1345 H1345]].
 intros [w1346 [b1346 H1346]].
 intro Eval. unfold address_expr_1347 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H1323 ?H1345 ?H1346 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H1323 ?H1345 ?H1346 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_1348 inputs path site mm old result :
 (exists width bits, VM.find 1307 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1348 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1307 [b1307 H1307]].
 apply formal_uint_scalar_concrete. unfold address_expr_1348. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1349 inputs path site mm old result :
 (exists width bits, VM.find 1326 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1347 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1348 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1349 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1326 [b1326 H1326]].
 intros [w1347 [b1347 H1347]].
 intros [w1348 [b1348 H1348]].
 intro Eval. unfold address_expr_1349 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H1326 ?H1347 ?H1348 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H1326 ?H1347 ?H1348 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_1350 inputs path site mm old result :
 (exists width bits, VM.find 1307 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1350 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1307 [b1307 H1307]].
 apply formal_uint_scalar_concrete. unfold address_expr_1350. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1351 inputs path site mm old result :
 (exists width bits, VM.find 1337 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1349 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1350 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1351 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1337 [b1337 H1337]].
 intros [w1349 [b1349 H1349]].
 intros [w1350 [b1350 H1350]].
 intro Eval. unfold address_expr_1351 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H1337 ?H1349 ?H1350 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H1337 ?H1349 ?H1350 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_1352 inputs path site mm old result :
 (exists width bits, VM.find 1307 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1352 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1307 [b1307 H1307]].
 apply formal_uint_scalar_concrete. unfold address_expr_1352. solve_address_uint_ready.
Qed.
Lemma address_uint_result_1353 inputs path site mm old result :
 (exists width bits, VM.find 1339 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1351 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 1352 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_1353 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1339 [b1339 H1339]].
 intros [w1351 [b1351 H1351]].
 intros [w1352 [b1352 H1352]].
 intro Eval. unfold address_expr_1353 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H1339 ?H1351 ?H1352 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H1339 ?H1351 ?H1352 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_7763 inputs path site mm old result :
 (exists width bits, VM.find 74 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7763 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w74 [b74 H74]].
 apply formal_uint_scalar_concrete. unfold address_expr_7763. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7764 inputs path site mm old result :
 (exists width bits, VM.find 81 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7764 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w81 [b81 H81]].
 apply formal_uint_scalar_concrete. unfold address_expr_7764. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7765 inputs path site mm old result :
 (exists width bits, VM.find 7763 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7764 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7765 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7763 [b7763 H7763]].
 intros [w7764 [b7764 H7764]].
 apply formal_uint_scalar_concrete. unfold address_expr_7765. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7803 inputs path site mm old result :
 (exists width bits, VM.find 7748 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7803 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7748 [b7748 H7748]].
 apply formal_uint_scalar_concrete. unfold address_expr_7803. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7804 inputs path site mm old result :
 (exists width bits, VM.find 7748 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7804 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7748 [b7748 H7748]].
 apply formal_uint_scalar_concrete. unfold address_expr_7804. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7805 inputs path site mm old result :
 (exists width bits, VM.find 7750 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7805 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7750 [b7750 H7750]].
 apply formal_uint_scalar_concrete. unfold address_expr_7805. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7806 inputs path site mm old result :
 (exists width bits, VM.find 7803 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7806 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7803 [b7803 H7803]].
 apply formal_uint_scalar_concrete. unfold address_expr_7806. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7807 inputs path site mm old result :
 (exists width bits, VM.find 7757 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7806 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7807 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7757 [b7757 H7757]].
 intros [w7806 [b7806 H7806]].
 apply formal_uint_scalar_concrete. unfold address_expr_7807. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7808 inputs path site mm old result :
 (exists width bits, VM.find 7803 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7805 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7808 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7803 [b7803 H7803]].
 intros [w7805 [b7805 H7805]].
 apply formal_uint_scalar_concrete. unfold address_expr_7808. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7809 inputs path site mm old result :
 (exists width bits, VM.find 7807 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7808 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7809 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7807 [b7807 H7807]].
 intros [w7808 [b7808 H7808]].
 apply formal_uint_scalar_concrete. unfold address_expr_7809. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7810 inputs path site mm old result :
 (exists width bits, VM.find 7804 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7810 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7804 [b7804 H7804]].
 apply formal_uint_scalar_concrete. unfold address_expr_7810. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7811 inputs path site mm old result :
 (exists width bits, VM.find 7757 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7810 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7811 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7757 [b7757 H7757]].
 intros [w7810 [b7810 H7810]].
 apply formal_uint_scalar_concrete. unfold address_expr_7811. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7812 inputs path site mm old result :
 (exists width bits, VM.find 7804 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7805 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7812 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7804 [b7804 H7804]].
 intros [w7805 [b7805 H7805]].
 apply formal_uint_scalar_concrete. unfold address_expr_7812. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7813 inputs path site mm old result :
 (exists width bits, VM.find 7811 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7812 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7813 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7811 [b7811 H7811]].
 intros [w7812 [b7812 H7812]].
 apply formal_uint_scalar_concrete. unfold address_expr_7813. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7814 inputs path site mm old result :
 (exists width bits, VM.find 7756 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7814 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7756 [b7756 H7756]].
 apply formal_uint_scalar_concrete. unfold address_expr_7814. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7815 inputs path site mm old result :
 (exists width bits, VM.find 7809 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7814 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7815 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7809 [b7809 H7809]].
 intros [w7814 [b7814 H7814]].
 apply formal_uint_scalar_concrete. unfold address_expr_7815. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7816 inputs path site mm old result :
 (exists width bits, VM.find 782 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7752 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7815 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7816 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w782 [b782 H782]].
 intros [w7752 [b7752 H7752]].
 intros [w7815 [b7815 H7815]].
 intro Eval. unfold address_expr_7816 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H782 ?H7752 ?H7815 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H782 ?H7752 ?H7815 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_7817 inputs path site mm old result :
 (exists width bits, VM.find 7756 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7817 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7756 [b7756 H7756]].
 apply formal_uint_scalar_concrete. unfold address_expr_7817. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7818 inputs path site mm old result :
 (exists width bits, VM.find 7813 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7817 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7818 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7813 [b7813 H7813]].
 intros [w7817 [b7817 H7817]].
 apply formal_uint_scalar_concrete. unfold address_expr_7818. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7819 inputs path site mm old result :
 (exists width bits, VM.find 783 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7752 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7818 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7819 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w783 [b783 H783]].
 intros [w7752 [b7752 H7752]].
 intros [w7818 [b7818 H7818]].
 intro Eval. unfold address_expr_7819 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H783 ?H7752 ?H7818 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H783 ?H7752 ?H7818 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_7820 inputs path site mm old result :
 (exists width bits, VM.find 86 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7820 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w86 [b86 H86]].
 apply formal_uint_scalar_concrete. unfold address_expr_7820. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7821 inputs path site mm old result :
 (exists width bits, VM.find 7749 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7816 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7820 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7821 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7749 [b7749 H7749]].
 intros [w7816 [b7816 H7816]].
 intros [w7820 [b7820 H7820]].
 intro Eval. unfold address_expr_7821 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H7749 ?H7816 ?H7820 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H7749 ?H7816 ?H7820 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_7822 inputs path site mm old result :
 (exists width bits, VM.find 87 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7822 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w87 [b87 H87]].
 apply formal_uint_scalar_concrete. unfold address_expr_7822. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7823 inputs path site mm old result :
 (exists width bits, VM.find 1308 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7819 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7822 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7823 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1308 [b1308 H1308]].
 intros [w7819 [b7819 H7819]].
 intros [w7822 [b7822 H7822]].
 intro Eval. unfold address_expr_7823 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H1308 ?H7819 ?H7822 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H1308 ?H7819 ?H7822 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_7824 inputs path site mm old result :
 (exists width bits, VM.find 1155 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7752 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7765 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7824 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1155 [b1155 H1155]].
 intros [w7752 [b7752 H7752]].
 intros [w7765 [b7765 H7765]].
 intro Eval. unfold address_expr_7824 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H1155 ?H7752 ?H7765 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H1155 ?H7752 ?H7765 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_7825 inputs path site mm old result :
 (exists width bits, VM.find 7824 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7825 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7824 [b7824 H7824]].
 apply formal_uint_scalar_concrete. unfold address_expr_7825. solve_address_uint_ready.
Qed.
Lemma address_uint_result_7826 inputs path site mm old result :
 (exists width bits, VM.find 7825 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_7826 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7825 [b7825 H7825]].
 apply formal_uint_scalar_concrete. unfold address_expr_7826. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8263 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8263 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8263. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8264 inputs path site mm old result :
 (exists width bits, VM.find 8263 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8264 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8263 [b8263 H8263]].
 apply formal_uint_scalar_concrete. unfold address_expr_8264. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8265 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8265 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8265. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8266 inputs path site mm old result :
 (exists width bits, VM.find 8265 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8266 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8265 [b8265 H8265]].
 apply formal_uint_scalar_concrete. unfold address_expr_8266. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8267 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8267 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8267. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8268 inputs path site mm old result :
 (exists width bits, VM.find 8267 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8268 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8267 [b8267 H8267]].
 apply formal_uint_scalar_concrete. unfold address_expr_8268. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8269 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8269 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8269. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8270 inputs path site mm old result :
 (exists width bits, VM.find 8269 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8270 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8269 [b8269 H8269]].
 apply formal_uint_scalar_concrete. unfold address_expr_8270. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8271 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8271 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8271. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8272 inputs path site mm old result :
 (exists width bits, VM.find 8271 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8272 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8271 [b8271 H8271]].
 apply formal_uint_scalar_concrete. unfold address_expr_8272. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8273 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8273 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8273. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8274 inputs path site mm old result :
 (exists width bits, VM.find 8273 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8274 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8273 [b8273 H8273]].
 apply formal_uint_scalar_concrete. unfold address_expr_8274. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8275 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8275 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8275. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8276 inputs path site mm old result :
 (exists width bits, VM.find 8275 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8276 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8275 [b8275 H8275]].
 apply formal_uint_scalar_concrete. unfold address_expr_8276. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8277 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8277 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8277. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8278 inputs path site mm old result :
 (exists width bits, VM.find 8277 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8278 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8277 [b8277 H8277]].
 apply formal_uint_scalar_concrete. unfold address_expr_8278. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8279 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8279 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8279. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8280 inputs path site mm old result :
 (exists width bits, VM.find 8279 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8280 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8279 [b8279 H8279]].
 apply formal_uint_scalar_concrete. unfold address_expr_8280. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8281 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8281 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8281. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8282 inputs path site mm old result :
 (exists width bits, VM.find 8281 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8282 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8281 [b8281 H8281]].
 apply formal_uint_scalar_concrete. unfold address_expr_8282. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8283 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8283 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8283. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8284 inputs path site mm old result :
 (exists width bits, VM.find 8283 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8284 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8283 [b8283 H8283]].
 apply formal_uint_scalar_concrete. unfold address_expr_8284. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8285 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8285 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8285. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8286 inputs path site mm old result :
 (exists width bits, VM.find 8285 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8286 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8285 [b8285 H8285]].
 apply formal_uint_scalar_concrete. unfold address_expr_8286. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8287 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8287 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8287. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8288 inputs path site mm old result :
 (exists width bits, VM.find 8287 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8288 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8287 [b8287 H8287]].
 apply formal_uint_scalar_concrete. unfold address_expr_8288. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8289 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8289 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8289. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8290 inputs path site mm old result :
 (exists width bits, VM.find 8289 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8290 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8289 [b8289 H8289]].
 apply formal_uint_scalar_concrete. unfold address_expr_8290. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8291 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8291 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8291. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8292 inputs path site mm old result :
 (exists width bits, VM.find 8291 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8292 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8291 [b8291 H8291]].
 apply formal_uint_scalar_concrete. unfold address_expr_8292. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8293 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8293 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8293. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8294 inputs path site mm old result :
 (exists width bits, VM.find 8293 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8294 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8293 [b8293 H8293]].
 apply formal_uint_scalar_concrete. unfold address_expr_8294. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8295 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8295 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8295. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8296 inputs path site mm old result :
 (exists width bits, VM.find 8295 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8296 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8295 [b8295 H8295]].
 apply formal_uint_scalar_concrete. unfold address_expr_8296. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8297 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8297 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8297. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8298 inputs path site mm old result :
 (exists width bits, VM.find 8297 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8298 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8297 [b8297 H8297]].
 apply formal_uint_scalar_concrete. unfold address_expr_8298. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8299 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8299 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8299. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8300 inputs path site mm old result :
 (exists width bits, VM.find 8299 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8300 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8299 [b8299 H8299]].
 apply formal_uint_scalar_concrete. unfold address_expr_8300. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8301 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8301 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8301. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8302 inputs path site mm old result :
 (exists width bits, VM.find 8301 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8302 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8301 [b8301 H8301]].
 apply formal_uint_scalar_concrete. unfold address_expr_8302. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8303 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8303 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8303. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8304 inputs path site mm old result :
 (exists width bits, VM.find 8303 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8304 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8303 [b8303 H8303]].
 apply formal_uint_scalar_concrete. unfold address_expr_8304. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8305 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8305 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8305. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8306 inputs path site mm old result :
 (exists width bits, VM.find 8305 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8306 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8305 [b8305 H8305]].
 apply formal_uint_scalar_concrete. unfold address_expr_8306. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8307 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8307 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8307. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8308 inputs path site mm old result :
 (exists width bits, VM.find 8307 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8308 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8307 [b8307 H8307]].
 apply formal_uint_scalar_concrete. unfold address_expr_8308. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8309 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8309 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8309. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8310 inputs path site mm old result :
 (exists width bits, VM.find 8309 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8310 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8309 [b8309 H8309]].
 apply formal_uint_scalar_concrete. unfold address_expr_8310. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8311 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8311 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8311. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8312 inputs path site mm old result :
 (exists width bits, VM.find 8311 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8312 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8311 [b8311 H8311]].
 apply formal_uint_scalar_concrete. unfold address_expr_8312. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8313 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8313 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8313. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8314 inputs path site mm old result :
 (exists width bits, VM.find 8313 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8314 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8313 [b8313 H8313]].
 apply formal_uint_scalar_concrete. unfold address_expr_8314. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8315 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8315 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8315. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8316 inputs path site mm old result :
 (exists width bits, VM.find 8315 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8316 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8315 [b8315 H8315]].
 apply formal_uint_scalar_concrete. unfold address_expr_8316. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8317 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8317 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8317. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8318 inputs path site mm old result :
 (exists width bits, VM.find 8317 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8318 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8317 [b8317 H8317]].
 apply formal_uint_scalar_concrete. unfold address_expr_8318. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8319 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8319 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8319. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8320 inputs path site mm old result :
 (exists width bits, VM.find 8319 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8320 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8319 [b8319 H8319]].
 apply formal_uint_scalar_concrete. unfold address_expr_8320. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8321 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8321 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8321. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8322 inputs path site mm old result :
 (exists width bits, VM.find 8321 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8322 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8321 [b8321 H8321]].
 apply formal_uint_scalar_concrete. unfold address_expr_8322. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8323 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8323 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8323. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8324 inputs path site mm old result :
 (exists width bits, VM.find 8323 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8324 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8323 [b8323 H8323]].
 apply formal_uint_scalar_concrete. unfold address_expr_8324. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8325 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8325 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8325. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8326 inputs path site mm old result :
 (exists width bits, VM.find 8325 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8326 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8325 [b8325 H8325]].
 apply formal_uint_scalar_concrete. unfold address_expr_8326. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8327 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8327 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8327. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8328 inputs path site mm old result :
 (exists width bits, VM.find 8327 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8328 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8327 [b8327 H8327]].
 apply formal_uint_scalar_concrete. unfold address_expr_8328. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8329 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8329 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8329. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8330 inputs path site mm old result :
 (exists width bits, VM.find 8329 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8330 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8329 [b8329 H8329]].
 apply formal_uint_scalar_concrete. unfold address_expr_8330. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8331 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8331 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8331. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8332 inputs path site mm old result :
 (exists width bits, VM.find 8331 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8332 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8331 [b8331 H8331]].
 apply formal_uint_scalar_concrete. unfold address_expr_8332. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8333 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8333 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8333. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8334 inputs path site mm old result :
 (exists width bits, VM.find 8333 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8334 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8333 [b8333 H8333]].
 apply formal_uint_scalar_concrete. unfold address_expr_8334. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8335 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8335 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8335. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8336 inputs path site mm old result :
 (exists width bits, VM.find 8335 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8336 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8335 [b8335 H8335]].
 apply formal_uint_scalar_concrete. unfold address_expr_8336. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8337 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8337 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8337. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8338 inputs path site mm old result :
 (exists width bits, VM.find 8337 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8338 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8337 [b8337 H8337]].
 apply formal_uint_scalar_concrete. unfold address_expr_8338. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8339 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8339 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8339. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8340 inputs path site mm old result :
 (exists width bits, VM.find 8339 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8340 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8339 [b8339 H8339]].
 apply formal_uint_scalar_concrete. unfold address_expr_8340. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8341 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8341 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8341. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8342 inputs path site mm old result :
 (exists width bits, VM.find 8341 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8342 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8341 [b8341 H8341]].
 apply formal_uint_scalar_concrete. unfold address_expr_8342. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8343 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8343 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8343. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8344 inputs path site mm old result :
 (exists width bits, VM.find 8343 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8344 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8343 [b8343 H8343]].
 apply formal_uint_scalar_concrete. unfold address_expr_8344. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8345 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8345 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8345. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8346 inputs path site mm old result :
 (exists width bits, VM.find 8345 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8346 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8345 [b8345 H8345]].
 apply formal_uint_scalar_concrete. unfold address_expr_8346. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8347 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8347 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8347. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8348 inputs path site mm old result :
 (exists width bits, VM.find 8347 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8348 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8347 [b8347 H8347]].
 apply formal_uint_scalar_concrete. unfold address_expr_8348. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8349 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8349 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8349. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8350 inputs path site mm old result :
 (exists width bits, VM.find 8349 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8350 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8349 [b8349 H8349]].
 apply formal_uint_scalar_concrete. unfold address_expr_8350. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8351 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8351 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8351. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8352 inputs path site mm old result :
 (exists width bits, VM.find 8351 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8352 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8351 [b8351 H8351]].
 apply formal_uint_scalar_concrete. unfold address_expr_8352. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8353 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8353 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8353. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8354 inputs path site mm old result :
 (exists width bits, VM.find 8353 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8354 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8353 [b8353 H8353]].
 apply formal_uint_scalar_concrete. unfold address_expr_8354. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8355 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8355 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8355. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8356 inputs path site mm old result :
 (exists width bits, VM.find 8355 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8356 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8355 [b8355 H8355]].
 apply formal_uint_scalar_concrete. unfold address_expr_8356. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8357 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8357 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8357. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8358 inputs path site mm old result :
 (exists width bits, VM.find 8357 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8358 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8357 [b8357 H8357]].
 apply formal_uint_scalar_concrete. unfold address_expr_8358. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8359 inputs path site mm old result :
 (exists width bits, VM.find 8249 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8359 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8249 [b8249 H8249]].
 apply formal_uint_scalar_concrete. unfold address_expr_8359. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8360 inputs path site mm old result :
 (exists width bits, VM.find 8359 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8360 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8359 [b8359 H8359]].
 apply formal_uint_scalar_concrete. unfold address_expr_8360. solve_address_uint_ready.
Qed.
Lemma address_uint_result_8410 inputs path site mm old result :
 (exists width bits, VM.find 8360 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8410 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8360 [b8360 H8360]].
 intro Eval. unfold address_expr_8410 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8360 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8360 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8411 inputs path site mm old result :
 (exists width bits, VM.find 8358 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8410 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8411 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8358 [b8358 H8358]].
 intros [w8410 [b8410 H8410]].
 intro Eval. unfold address_expr_8411 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8358 ?H8410 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8358 ?H8410 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8412 inputs path site mm old result :
 (exists width bits, VM.find 8356 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8411 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8412 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8356 [b8356 H8356]].
 intros [w8411 [b8411 H8411]].
 intro Eval. unfold address_expr_8412 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8356 ?H8411 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8356 ?H8411 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8413 inputs path site mm old result :
 (exists width bits, VM.find 8354 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8412 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8413 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8354 [b8354 H8354]].
 intros [w8412 [b8412 H8412]].
 intro Eval. unfold address_expr_8413 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8354 ?H8412 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8354 ?H8412 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8414 inputs path site mm old result :
 (exists width bits, VM.find 8352 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8413 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8414 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8352 [b8352 H8352]].
 intros [w8413 [b8413 H8413]].
 intro Eval. unfold address_expr_8414 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8352 ?H8413 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8352 ?H8413 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8415 inputs path site mm old result :
 (exists width bits, VM.find 8350 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8414 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8415 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8350 [b8350 H8350]].
 intros [w8414 [b8414 H8414]].
 intro Eval. unfold address_expr_8415 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8350 ?H8414 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8350 ?H8414 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8416 inputs path site mm old result :
 (exists width bits, VM.find 8348 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8415 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8416 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8348 [b8348 H8348]].
 intros [w8415 [b8415 H8415]].
 intro Eval. unfold address_expr_8416 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8348 ?H8415 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8348 ?H8415 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8417 inputs path site mm old result :
 (exists width bits, VM.find 8346 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8416 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8417 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8346 [b8346 H8346]].
 intros [w8416 [b8416 H8416]].
 intro Eval. unfold address_expr_8417 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8346 ?H8416 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8346 ?H8416 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8418 inputs path site mm old result :
 (exists width bits, VM.find 8344 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8417 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8418 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8344 [b8344 H8344]].
 intros [w8417 [b8417 H8417]].
 intro Eval. unfold address_expr_8418 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8344 ?H8417 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8344 ?H8417 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8419 inputs path site mm old result :
 (exists width bits, VM.find 8342 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8418 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8419 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8342 [b8342 H8342]].
 intros [w8418 [b8418 H8418]].
 intro Eval. unfold address_expr_8419 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8342 ?H8418 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8342 ?H8418 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8420 inputs path site mm old result :
 (exists width bits, VM.find 8340 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8419 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8420 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8340 [b8340 H8340]].
 intros [w8419 [b8419 H8419]].
 intro Eval. unfold address_expr_8420 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8340 ?H8419 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8340 ?H8419 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8421 inputs path site mm old result :
 (exists width bits, VM.find 8338 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8420 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8421 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8338 [b8338 H8338]].
 intros [w8420 [b8420 H8420]].
 intro Eval. unfold address_expr_8421 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8338 ?H8420 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8338 ?H8420 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8422 inputs path site mm old result :
 (exists width bits, VM.find 8336 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8421 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8422 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8336 [b8336 H8336]].
 intros [w8421 [b8421 H8421]].
 intro Eval. unfold address_expr_8422 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8336 ?H8421 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8336 ?H8421 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8423 inputs path site mm old result :
 (exists width bits, VM.find 8334 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8422 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8423 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8334 [b8334 H8334]].
 intros [w8422 [b8422 H8422]].
 intro Eval. unfold address_expr_8423 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8334 ?H8422 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8334 ?H8422 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8424 inputs path site mm old result :
 (exists width bits, VM.find 8332 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8423 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8424 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8332 [b8332 H8332]].
 intros [w8423 [b8423 H8423]].
 intro Eval. unfold address_expr_8424 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8332 ?H8423 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8332 ?H8423 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8425 inputs path site mm old result :
 (exists width bits, VM.find 8330 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8424 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8425 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8330 [b8330 H8330]].
 intros [w8424 [b8424 H8424]].
 intro Eval. unfold address_expr_8425 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8330 ?H8424 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8330 ?H8424 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8426 inputs path site mm old result :
 (exists width bits, VM.find 8328 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8425 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8426 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8328 [b8328 H8328]].
 intros [w8425 [b8425 H8425]].
 intro Eval. unfold address_expr_8426 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8328 ?H8425 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8328 ?H8425 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8427 inputs path site mm old result :
 (exists width bits, VM.find 8326 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8426 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8427 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8326 [b8326 H8326]].
 intros [w8426 [b8426 H8426]].
 intro Eval. unfold address_expr_8427 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8326 ?H8426 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8326 ?H8426 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8428 inputs path site mm old result :
 (exists width bits, VM.find 8324 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8427 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8428 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8324 [b8324 H8324]].
 intros [w8427 [b8427 H8427]].
 intro Eval. unfold address_expr_8428 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8324 ?H8427 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8324 ?H8427 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8429 inputs path site mm old result :
 (exists width bits, VM.find 8322 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8428 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8429 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8322 [b8322 H8322]].
 intros [w8428 [b8428 H8428]].
 intro Eval. unfold address_expr_8429 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8322 ?H8428 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8322 ?H8428 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8430 inputs path site mm old result :
 (exists width bits, VM.find 8320 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8429 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8430 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8320 [b8320 H8320]].
 intros [w8429 [b8429 H8429]].
 intro Eval. unfold address_expr_8430 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8320 ?H8429 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8320 ?H8429 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8431 inputs path site mm old result :
 (exists width bits, VM.find 8318 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8430 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8431 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8318 [b8318 H8318]].
 intros [w8430 [b8430 H8430]].
 intro Eval. unfold address_expr_8431 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8318 ?H8430 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8318 ?H8430 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8432 inputs path site mm old result :
 (exists width bits, VM.find 8316 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8431 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8432 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8316 [b8316 H8316]].
 intros [w8431 [b8431 H8431]].
 intro Eval. unfold address_expr_8432 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8316 ?H8431 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8316 ?H8431 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8433 inputs path site mm old result :
 (exists width bits, VM.find 8314 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8432 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8433 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8314 [b8314 H8314]].
 intros [w8432 [b8432 H8432]].
 intro Eval. unfold address_expr_8433 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8314 ?H8432 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8314 ?H8432 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8434 inputs path site mm old result :
 (exists width bits, VM.find 8312 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8433 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8434 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8312 [b8312 H8312]].
 intros [w8433 [b8433 H8433]].
 intro Eval. unfold address_expr_8434 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8312 ?H8433 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8312 ?H8433 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8435 inputs path site mm old result :
 (exists width bits, VM.find 8310 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8434 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8435 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8310 [b8310 H8310]].
 intros [w8434 [b8434 H8434]].
 intro Eval. unfold address_expr_8435 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8310 ?H8434 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8310 ?H8434 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8436 inputs path site mm old result :
 (exists width bits, VM.find 8308 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8435 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8436 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8308 [b8308 H8308]].
 intros [w8435 [b8435 H8435]].
 intro Eval. unfold address_expr_8436 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8308 ?H8435 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8308 ?H8435 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8437 inputs path site mm old result :
 (exists width bits, VM.find 8306 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8436 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8437 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8306 [b8306 H8306]].
 intros [w8436 [b8436 H8436]].
 intro Eval. unfold address_expr_8437 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8306 ?H8436 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8306 ?H8436 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8438 inputs path site mm old result :
 (exists width bits, VM.find 8304 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8437 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8438 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8304 [b8304 H8304]].
 intros [w8437 [b8437 H8437]].
 intro Eval. unfold address_expr_8438 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8304 ?H8437 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8304 ?H8437 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8439 inputs path site mm old result :
 (exists width bits, VM.find 8302 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8438 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8439 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8302 [b8302 H8302]].
 intros [w8438 [b8438 H8438]].
 intro Eval. unfold address_expr_8439 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8302 ?H8438 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8302 ?H8438 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8440 inputs path site mm old result :
 (exists width bits, VM.find 8300 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8439 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8440 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8300 [b8300 H8300]].
 intros [w8439 [b8439 H8439]].
 intro Eval. unfold address_expr_8440 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8300 ?H8439 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8300 ?H8439 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8441 inputs path site mm old result :
 (exists width bits, VM.find 8298 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8440 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8441 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8298 [b8298 H8298]].
 intros [w8440 [b8440 H8440]].
 intro Eval. unfold address_expr_8441 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8298 ?H8440 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8298 ?H8440 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8442 inputs path site mm old result :
 (exists width bits, VM.find 8296 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8441 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8442 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8296 [b8296 H8296]].
 intros [w8441 [b8441 H8441]].
 intro Eval. unfold address_expr_8442 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8296 ?H8441 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8296 ?H8441 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8443 inputs path site mm old result :
 (exists width bits, VM.find 8294 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8442 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8443 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8294 [b8294 H8294]].
 intros [w8442 [b8442 H8442]].
 intro Eval. unfold address_expr_8443 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8294 ?H8442 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8294 ?H8442 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8444 inputs path site mm old result :
 (exists width bits, VM.find 8292 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8443 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8444 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8292 [b8292 H8292]].
 intros [w8443 [b8443 H8443]].
 intro Eval. unfold address_expr_8444 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8292 ?H8443 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8292 ?H8443 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8445 inputs path site mm old result :
 (exists width bits, VM.find 8290 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8444 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8445 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8290 [b8290 H8290]].
 intros [w8444 [b8444 H8444]].
 intro Eval. unfold address_expr_8445 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8290 ?H8444 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8290 ?H8444 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8446 inputs path site mm old result :
 (exists width bits, VM.find 8288 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8445 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8446 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8288 [b8288 H8288]].
 intros [w8445 [b8445 H8445]].
 intro Eval. unfold address_expr_8446 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8288 ?H8445 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8288 ?H8445 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8447 inputs path site mm old result :
 (exists width bits, VM.find 8286 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8446 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8447 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8286 [b8286 H8286]].
 intros [w8446 [b8446 H8446]].
 intro Eval. unfold address_expr_8447 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8286 ?H8446 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8286 ?H8446 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8448 inputs path site mm old result :
 (exists width bits, VM.find 8284 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8447 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8448 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8284 [b8284 H8284]].
 intros [w8447 [b8447 H8447]].
 intro Eval. unfold address_expr_8448 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8284 ?H8447 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8284 ?H8447 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8449 inputs path site mm old result :
 (exists width bits, VM.find 8282 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8448 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8449 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8282 [b8282 H8282]].
 intros [w8448 [b8448 H8448]].
 intro Eval. unfold address_expr_8449 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8282 ?H8448 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8282 ?H8448 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8450 inputs path site mm old result :
 (exists width bits, VM.find 8280 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8449 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8450 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8280 [b8280 H8280]].
 intros [w8449 [b8449 H8449]].
 intro Eval. unfold address_expr_8450 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8280 ?H8449 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8280 ?H8449 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8451 inputs path site mm old result :
 (exists width bits, VM.find 8278 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8450 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8451 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8278 [b8278 H8278]].
 intros [w8450 [b8450 H8450]].
 intro Eval. unfold address_expr_8451 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8278 ?H8450 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8278 ?H8450 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8452 inputs path site mm old result :
 (exists width bits, VM.find 8276 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8451 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8452 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8276 [b8276 H8276]].
 intros [w8451 [b8451 H8451]].
 intro Eval. unfold address_expr_8452 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8276 ?H8451 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8276 ?H8451 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8453 inputs path site mm old result :
 (exists width bits, VM.find 8274 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8452 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8453 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8274 [b8274 H8274]].
 intros [w8452 [b8452 H8452]].
 intro Eval. unfold address_expr_8453 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8274 ?H8452 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8274 ?H8452 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8454 inputs path site mm old result :
 (exists width bits, VM.find 8272 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8453 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8454 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8272 [b8272 H8272]].
 intros [w8453 [b8453 H8453]].
 intro Eval. unfold address_expr_8454 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8272 ?H8453 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8272 ?H8453 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8455 inputs path site mm old result :
 (exists width bits, VM.find 8270 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8454 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8455 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8270 [b8270 H8270]].
 intros [w8454 [b8454 H8454]].
 intro Eval. unfold address_expr_8455 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8270 ?H8454 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8270 ?H8454 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8456 inputs path site mm old result :
 (exists width bits, VM.find 8268 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8455 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8456 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8268 [b8268 H8268]].
 intros [w8455 [b8455 H8455]].
 intro Eval. unfold address_expr_8456 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8268 ?H8455 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8268 ?H8455 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8457 inputs path site mm old result :
 (exists width bits, VM.find 8266 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8456 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8457 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8266 [b8266 H8266]].
 intros [w8456 [b8456 H8456]].
 intro Eval. unfold address_expr_8457 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8266 ?H8456 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8266 ?H8456 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8458 inputs path site mm old result :
 (exists width bits, VM.find 8264 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8457 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8458 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8264 [b8264 H8264]].
 intros [w8457 [b8457 H8457]].
 intro Eval. unfold address_expr_8458 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8264 ?H8457 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8264 ?H8457 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8459 inputs path site mm old result :
 (exists width bits, VM.find 8360 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8459 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8360 [b8360 H8360]].
 intro Eval. unfold address_expr_8459 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8360 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8360 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8460 inputs path site mm old result :
 (exists width bits, VM.find 8358 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8459 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8460 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8358 [b8358 H8358]].
 intros [w8459 [b8459 H8459]].
 intro Eval. unfold address_expr_8460 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8358 ?H8459 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8358 ?H8459 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8461 inputs path site mm old result :
 (exists width bits, VM.find 8356 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8460 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8461 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8356 [b8356 H8356]].
 intros [w8460 [b8460 H8460]].
 intro Eval. unfold address_expr_8461 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8356 ?H8460 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8356 ?H8460 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8462 inputs path site mm old result :
 (exists width bits, VM.find 8354 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8461 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8462 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8354 [b8354 H8354]].
 intros [w8461 [b8461 H8461]].
 intro Eval. unfold address_expr_8462 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8354 ?H8461 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8354 ?H8461 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8463 inputs path site mm old result :
 (exists width bits, VM.find 8352 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8462 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8463 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8352 [b8352 H8352]].
 intros [w8462 [b8462 H8462]].
 intro Eval. unfold address_expr_8463 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8352 ?H8462 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8352 ?H8462 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8464 inputs path site mm old result :
 (exists width bits, VM.find 8350 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8463 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8464 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8350 [b8350 H8350]].
 intros [w8463 [b8463 H8463]].
 intro Eval. unfold address_expr_8464 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8350 ?H8463 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8350 ?H8463 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8465 inputs path site mm old result :
 (exists width bits, VM.find 8348 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8464 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8465 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8348 [b8348 H8348]].
 intros [w8464 [b8464 H8464]].
 intro Eval. unfold address_expr_8465 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8348 ?H8464 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8348 ?H8464 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8466 inputs path site mm old result :
 (exists width bits, VM.find 8346 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8465 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8466 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8346 [b8346 H8346]].
 intros [w8465 [b8465 H8465]].
 intro Eval. unfold address_expr_8466 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8346 ?H8465 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8346 ?H8465 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8467 inputs path site mm old result :
 (exists width bits, VM.find 8344 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8466 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8467 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8344 [b8344 H8344]].
 intros [w8466 [b8466 H8466]].
 intro Eval. unfold address_expr_8467 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8344 ?H8466 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8344 ?H8466 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8468 inputs path site mm old result :
 (exists width bits, VM.find 8342 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8467 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8468 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8342 [b8342 H8342]].
 intros [w8467 [b8467 H8467]].
 intro Eval. unfold address_expr_8468 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8342 ?H8467 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8342 ?H8467 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8469 inputs path site mm old result :
 (exists width bits, VM.find 8340 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8468 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8469 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8340 [b8340 H8340]].
 intros [w8468 [b8468 H8468]].
 intro Eval. unfold address_expr_8469 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8340 ?H8468 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8340 ?H8468 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8470 inputs path site mm old result :
 (exists width bits, VM.find 8338 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8469 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8470 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8338 [b8338 H8338]].
 intros [w8469 [b8469 H8469]].
 intro Eval. unfold address_expr_8470 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8338 ?H8469 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8338 ?H8469 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8471 inputs path site mm old result :
 (exists width bits, VM.find 8336 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8470 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8471 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8336 [b8336 H8336]].
 intros [w8470 [b8470 H8470]].
 intro Eval. unfold address_expr_8471 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8336 ?H8470 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8336 ?H8470 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8472 inputs path site mm old result :
 (exists width bits, VM.find 8334 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8471 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8472 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8334 [b8334 H8334]].
 intros [w8471 [b8471 H8471]].
 intro Eval. unfold address_expr_8472 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8334 ?H8471 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8334 ?H8471 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8473 inputs path site mm old result :
 (exists width bits, VM.find 8332 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8472 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8473 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8332 [b8332 H8332]].
 intros [w8472 [b8472 H8472]].
 intro Eval. unfold address_expr_8473 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8332 ?H8472 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8332 ?H8472 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8474 inputs path site mm old result :
 (exists width bits, VM.find 8330 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8473 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8474 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8330 [b8330 H8330]].
 intros [w8473 [b8473 H8473]].
 intro Eval. unfold address_expr_8474 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8330 ?H8473 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8330 ?H8473 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8475 inputs path site mm old result :
 (exists width bits, VM.find 8328 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8474 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8475 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8328 [b8328 H8328]].
 intros [w8474 [b8474 H8474]].
 intro Eval. unfold address_expr_8475 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8328 ?H8474 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8328 ?H8474 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8476 inputs path site mm old result :
 (exists width bits, VM.find 8326 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8475 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8476 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8326 [b8326 H8326]].
 intros [w8475 [b8475 H8475]].
 intro Eval. unfold address_expr_8476 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8326 ?H8475 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8326 ?H8475 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8477 inputs path site mm old result :
 (exists width bits, VM.find 8324 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8476 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8477 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8324 [b8324 H8324]].
 intros [w8476 [b8476 H8476]].
 intro Eval. unfold address_expr_8477 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8324 ?H8476 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8324 ?H8476 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8478 inputs path site mm old result :
 (exists width bits, VM.find 8322 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8477 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8478 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8322 [b8322 H8322]].
 intros [w8477 [b8477 H8477]].
 intro Eval. unfold address_expr_8478 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8322 ?H8477 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8322 ?H8477 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8479 inputs path site mm old result :
 (exists width bits, VM.find 8320 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8478 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8479 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8320 [b8320 H8320]].
 intros [w8478 [b8478 H8478]].
 intro Eval. unfold address_expr_8479 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8320 ?H8478 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8320 ?H8478 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8480 inputs path site mm old result :
 (exists width bits, VM.find 8318 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8479 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8480 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8318 [b8318 H8318]].
 intros [w8479 [b8479 H8479]].
 intro Eval. unfold address_expr_8480 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8318 ?H8479 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8318 ?H8479 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8481 inputs path site mm old result :
 (exists width bits, VM.find 8316 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8480 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8481 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8316 [b8316 H8316]].
 intros [w8480 [b8480 H8480]].
 intro Eval. unfold address_expr_8481 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8316 ?H8480 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8316 ?H8480 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8482 inputs path site mm old result :
 (exists width bits, VM.find 8314 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8481 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8482 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8314 [b8314 H8314]].
 intros [w8481 [b8481 H8481]].
 intro Eval. unfold address_expr_8482 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8314 ?H8481 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8314 ?H8481 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8483 inputs path site mm old result :
 (exists width bits, VM.find 8312 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8482 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8483 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8312 [b8312 H8312]].
 intros [w8482 [b8482 H8482]].
 intro Eval. unfold address_expr_8483 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8312 ?H8482 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8312 ?H8482 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8484 inputs path site mm old result :
 (exists width bits, VM.find 8310 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8483 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8484 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8310 [b8310 H8310]].
 intros [w8483 [b8483 H8483]].
 intro Eval. unfold address_expr_8484 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8310 ?H8483 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8310 ?H8483 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8485 inputs path site mm old result :
 (exists width bits, VM.find 8308 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8484 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8485 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8308 [b8308 H8308]].
 intros [w8484 [b8484 H8484]].
 intro Eval. unfold address_expr_8485 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8308 ?H8484 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8308 ?H8484 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8486 inputs path site mm old result :
 (exists width bits, VM.find 8306 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8485 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8486 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8306 [b8306 H8306]].
 intros [w8485 [b8485 H8485]].
 intro Eval. unfold address_expr_8486 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8306 ?H8485 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8306 ?H8485 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8487 inputs path site mm old result :
 (exists width bits, VM.find 8304 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8486 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8487 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8304 [b8304 H8304]].
 intros [w8486 [b8486 H8486]].
 intro Eval. unfold address_expr_8487 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8304 ?H8486 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8304 ?H8486 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8488 inputs path site mm old result :
 (exists width bits, VM.find 8302 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8487 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8488 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8302 [b8302 H8302]].
 intros [w8487 [b8487 H8487]].
 intro Eval. unfold address_expr_8488 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8302 ?H8487 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8302 ?H8487 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8489 inputs path site mm old result :
 (exists width bits, VM.find 8300 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8488 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8489 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8300 [b8300 H8300]].
 intros [w8488 [b8488 H8488]].
 intro Eval. unfold address_expr_8489 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8300 ?H8488 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8300 ?H8488 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8490 inputs path site mm old result :
 (exists width bits, VM.find 8298 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8489 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8490 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8298 [b8298 H8298]].
 intros [w8489 [b8489 H8489]].
 intro Eval. unfold address_expr_8490 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8298 ?H8489 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8298 ?H8489 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8491 inputs path site mm old result :
 (exists width bits, VM.find 8296 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8490 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8491 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8296 [b8296 H8296]].
 intros [w8490 [b8490 H8490]].
 intro Eval. unfold address_expr_8491 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8296 ?H8490 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8296 ?H8490 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8492 inputs path site mm old result :
 (exists width bits, VM.find 8294 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8491 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8492 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8294 [b8294 H8294]].
 intros [w8491 [b8491 H8491]].
 intro Eval. unfold address_expr_8492 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8294 ?H8491 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8294 ?H8491 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8493 inputs path site mm old result :
 (exists width bits, VM.find 8292 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8492 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8493 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8292 [b8292 H8292]].
 intros [w8492 [b8492 H8492]].
 intro Eval. unfold address_expr_8493 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8292 ?H8492 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8292 ?H8492 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8494 inputs path site mm old result :
 (exists width bits, VM.find 8290 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8493 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8494 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8290 [b8290 H8290]].
 intros [w8493 [b8493 H8493]].
 intro Eval. unfold address_expr_8494 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8290 ?H8493 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8290 ?H8493 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8495 inputs path site mm old result :
 (exists width bits, VM.find 8288 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8494 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8495 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8288 [b8288 H8288]].
 intros [w8494 [b8494 H8494]].
 intro Eval. unfold address_expr_8495 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8288 ?H8494 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8288 ?H8494 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8496 inputs path site mm old result :
 (exists width bits, VM.find 8286 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8495 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8496 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8286 [b8286 H8286]].
 intros [w8495 [b8495 H8495]].
 intro Eval. unfold address_expr_8496 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8286 ?H8495 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8286 ?H8495 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8497 inputs path site mm old result :
 (exists width bits, VM.find 8284 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8496 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8497 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8284 [b8284 H8284]].
 intros [w8496 [b8496 H8496]].
 intro Eval. unfold address_expr_8497 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8284 ?H8496 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8284 ?H8496 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8498 inputs path site mm old result :
 (exists width bits, VM.find 8282 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8497 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8498 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8282 [b8282 H8282]].
 intros [w8497 [b8497 H8497]].
 intro Eval. unfold address_expr_8498 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8282 ?H8497 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8282 ?H8497 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8499 inputs path site mm old result :
 (exists width bits, VM.find 8280 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8498 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8499 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8280 [b8280 H8280]].
 intros [w8498 [b8498 H8498]].
 intro Eval. unfold address_expr_8499 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8280 ?H8498 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8280 ?H8498 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8500 inputs path site mm old result :
 (exists width bits, VM.find 8278 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8499 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8500 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8278 [b8278 H8278]].
 intros [w8499 [b8499 H8499]].
 intro Eval. unfold address_expr_8500 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8278 ?H8499 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8278 ?H8499 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8501 inputs path site mm old result :
 (exists width bits, VM.find 8276 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8500 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8501 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8276 [b8276 H8276]].
 intros [w8500 [b8500 H8500]].
 intro Eval. unfold address_expr_8501 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8276 ?H8500 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8276 ?H8500 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8502 inputs path site mm old result :
 (exists width bits, VM.find 8274 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8501 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8502 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8274 [b8274 H8274]].
 intros [w8501 [b8501 H8501]].
 intro Eval. unfold address_expr_8502 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8274 ?H8501 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8274 ?H8501 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8503 inputs path site mm old result :
 (exists width bits, VM.find 8272 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8502 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8503 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8272 [b8272 H8272]].
 intros [w8502 [b8502 H8502]].
 intro Eval. unfold address_expr_8503 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8272 ?H8502 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8272 ?H8502 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8504 inputs path site mm old result :
 (exists width bits, VM.find 8270 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8503 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8504 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8270 [b8270 H8270]].
 intros [w8503 [b8503 H8503]].
 intro Eval. unfold address_expr_8504 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8270 ?H8503 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8270 ?H8503 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8505 inputs path site mm old result :
 (exists width bits, VM.find 8268 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8504 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8505 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8268 [b8268 H8268]].
 intros [w8504 [b8504 H8504]].
 intro Eval. unfold address_expr_8505 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8268 ?H8504 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8268 ?H8504 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8506 inputs path site mm old result :
 (exists width bits, VM.find 8266 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8505 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8506 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8266 [b8266 H8266]].
 intros [w8505 [b8505 H8505]].
 intro Eval. unfold address_expr_8506 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8266 ?H8505 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8266 ?H8505 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8507 inputs path site mm old result :
 (exists width bits, VM.find 8264 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8506 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8507 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8264 [b8264 H8264]].
 intros [w8506 [b8506 H8506]].
 intro Eval. unfold address_expr_8507 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8264 ?H8506 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8264 ?H8506 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8508 inputs path site mm old result :
 (exists width bits, VM.find 8360 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8508 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8360 [b8360 H8360]].
 intro Eval. unfold address_expr_8508 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8360 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8360 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8509 inputs path site mm old result :
 (exists width bits, VM.find 8358 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8508 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8509 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8358 [b8358 H8358]].
 intros [w8508 [b8508 H8508]].
 intro Eval. unfold address_expr_8509 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8358 ?H8508 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8358 ?H8508 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8510 inputs path site mm old result :
 (exists width bits, VM.find 8356 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8509 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8510 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8356 [b8356 H8356]].
 intros [w8509 [b8509 H8509]].
 intro Eval. unfold address_expr_8510 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8356 ?H8509 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8356 ?H8509 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8511 inputs path site mm old result :
 (exists width bits, VM.find 8354 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8510 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8511 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8354 [b8354 H8354]].
 intros [w8510 [b8510 H8510]].
 intro Eval. unfold address_expr_8511 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8354 ?H8510 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8354 ?H8510 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8512 inputs path site mm old result :
 (exists width bits, VM.find 8352 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8511 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8512 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8352 [b8352 H8352]].
 intros [w8511 [b8511 H8511]].
 intro Eval. unfold address_expr_8512 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8352 ?H8511 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8352 ?H8511 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8513 inputs path site mm old result :
 (exists width bits, VM.find 8350 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8512 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8513 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8350 [b8350 H8350]].
 intros [w8512 [b8512 H8512]].
 intro Eval. unfold address_expr_8513 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8350 ?H8512 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8350 ?H8512 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8514 inputs path site mm old result :
 (exists width bits, VM.find 8348 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8513 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8514 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8348 [b8348 H8348]].
 intros [w8513 [b8513 H8513]].
 intro Eval. unfold address_expr_8514 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8348 ?H8513 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8348 ?H8513 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8515 inputs path site mm old result :
 (exists width bits, VM.find 8346 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8514 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8515 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8346 [b8346 H8346]].
 intros [w8514 [b8514 H8514]].
 intro Eval. unfold address_expr_8515 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8346 ?H8514 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8346 ?H8514 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8516 inputs path site mm old result :
 (exists width bits, VM.find 8344 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8515 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8516 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8344 [b8344 H8344]].
 intros [w8515 [b8515 H8515]].
 intro Eval. unfold address_expr_8516 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8344 ?H8515 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8344 ?H8515 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8517 inputs path site mm old result :
 (exists width bits, VM.find 8342 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8516 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8517 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8342 [b8342 H8342]].
 intros [w8516 [b8516 H8516]].
 intro Eval. unfold address_expr_8517 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8342 ?H8516 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8342 ?H8516 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8518 inputs path site mm old result :
 (exists width bits, VM.find 8340 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8517 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8518 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8340 [b8340 H8340]].
 intros [w8517 [b8517 H8517]].
 intro Eval. unfold address_expr_8518 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8340 ?H8517 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8340 ?H8517 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8519 inputs path site mm old result :
 (exists width bits, VM.find 8338 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8518 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8519 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8338 [b8338 H8338]].
 intros [w8518 [b8518 H8518]].
 intro Eval. unfold address_expr_8519 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8338 ?H8518 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8338 ?H8518 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8520 inputs path site mm old result :
 (exists width bits, VM.find 8336 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8519 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8520 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8336 [b8336 H8336]].
 intros [w8519 [b8519 H8519]].
 intro Eval. unfold address_expr_8520 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8336 ?H8519 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8336 ?H8519 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8521 inputs path site mm old result :
 (exists width bits, VM.find 8334 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8520 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8521 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8334 [b8334 H8334]].
 intros [w8520 [b8520 H8520]].
 intro Eval. unfold address_expr_8521 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8334 ?H8520 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8334 ?H8520 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8522 inputs path site mm old result :
 (exists width bits, VM.find 8332 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8521 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8522 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8332 [b8332 H8332]].
 intros [w8521 [b8521 H8521]].
 intro Eval. unfold address_expr_8522 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8332 ?H8521 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8332 ?H8521 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8523 inputs path site mm old result :
 (exists width bits, VM.find 8330 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8522 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8523 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8330 [b8330 H8330]].
 intros [w8522 [b8522 H8522]].
 intro Eval. unfold address_expr_8523 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8330 ?H8522 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8330 ?H8522 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8524 inputs path site mm old result :
 (exists width bits, VM.find 8328 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8523 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8524 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8328 [b8328 H8328]].
 intros [w8523 [b8523 H8523]].
 intro Eval. unfold address_expr_8524 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8328 ?H8523 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8328 ?H8523 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8525 inputs path site mm old result :
 (exists width bits, VM.find 8326 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8524 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8525 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8326 [b8326 H8326]].
 intros [w8524 [b8524 H8524]].
 intro Eval. unfold address_expr_8525 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8326 ?H8524 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8326 ?H8524 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8526 inputs path site mm old result :
 (exists width bits, VM.find 8324 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8525 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8526 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8324 [b8324 H8324]].
 intros [w8525 [b8525 H8525]].
 intro Eval. unfold address_expr_8526 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8324 ?H8525 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8324 ?H8525 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8527 inputs path site mm old result :
 (exists width bits, VM.find 8322 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8526 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8527 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8322 [b8322 H8322]].
 intros [w8526 [b8526 H8526]].
 intro Eval. unfold address_expr_8527 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8322 ?H8526 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8322 ?H8526 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8528 inputs path site mm old result :
 (exists width bits, VM.find 8320 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8527 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8528 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8320 [b8320 H8320]].
 intros [w8527 [b8527 H8527]].
 intro Eval. unfold address_expr_8528 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8320 ?H8527 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8320 ?H8527 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8529 inputs path site mm old result :
 (exists width bits, VM.find 8318 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8528 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8529 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8318 [b8318 H8318]].
 intros [w8528 [b8528 H8528]].
 intro Eval. unfold address_expr_8529 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8318 ?H8528 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8318 ?H8528 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8530 inputs path site mm old result :
 (exists width bits, VM.find 8316 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8529 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8530 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8316 [b8316 H8316]].
 intros [w8529 [b8529 H8529]].
 intro Eval. unfold address_expr_8530 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8316 ?H8529 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8316 ?H8529 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8531 inputs path site mm old result :
 (exists width bits, VM.find 8314 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8530 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8531 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8314 [b8314 H8314]].
 intros [w8530 [b8530 H8530]].
 intro Eval. unfold address_expr_8531 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8314 ?H8530 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8314 ?H8530 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8532 inputs path site mm old result :
 (exists width bits, VM.find 8312 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8531 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8532 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8312 [b8312 H8312]].
 intros [w8531 [b8531 H8531]].
 intro Eval. unfold address_expr_8532 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8312 ?H8531 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8312 ?H8531 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8533 inputs path site mm old result :
 (exists width bits, VM.find 8310 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8532 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8533 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8310 [b8310 H8310]].
 intros [w8532 [b8532 H8532]].
 intro Eval. unfold address_expr_8533 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8310 ?H8532 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8310 ?H8532 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8534 inputs path site mm old result :
 (exists width bits, VM.find 8308 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8533 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8534 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8308 [b8308 H8308]].
 intros [w8533 [b8533 H8533]].
 intro Eval. unfold address_expr_8534 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8308 ?H8533 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8308 ?H8533 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8535 inputs path site mm old result :
 (exists width bits, VM.find 8306 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8534 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8535 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8306 [b8306 H8306]].
 intros [w8534 [b8534 H8534]].
 intro Eval. unfold address_expr_8535 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8306 ?H8534 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8306 ?H8534 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8536 inputs path site mm old result :
 (exists width bits, VM.find 8304 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8535 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8536 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8304 [b8304 H8304]].
 intros [w8535 [b8535 H8535]].
 intro Eval. unfold address_expr_8536 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8304 ?H8535 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8304 ?H8535 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8537 inputs path site mm old result :
 (exists width bits, VM.find 8302 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8536 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8537 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8302 [b8302 H8302]].
 intros [w8536 [b8536 H8536]].
 intro Eval. unfold address_expr_8537 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8302 ?H8536 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8302 ?H8536 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8538 inputs path site mm old result :
 (exists width bits, VM.find 8300 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8537 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8538 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8300 [b8300 H8300]].
 intros [w8537 [b8537 H8537]].
 intro Eval. unfold address_expr_8538 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8300 ?H8537 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8300 ?H8537 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8539 inputs path site mm old result :
 (exists width bits, VM.find 8298 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8538 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8539 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8298 [b8298 H8298]].
 intros [w8538 [b8538 H8538]].
 intro Eval. unfold address_expr_8539 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8298 ?H8538 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8298 ?H8538 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8540 inputs path site mm old result :
 (exists width bits, VM.find 8296 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8539 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8540 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8296 [b8296 H8296]].
 intros [w8539 [b8539 H8539]].
 intro Eval. unfold address_expr_8540 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8296 ?H8539 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8296 ?H8539 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8541 inputs path site mm old result :
 (exists width bits, VM.find 8294 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8540 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8541 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8294 [b8294 H8294]].
 intros [w8540 [b8540 H8540]].
 intro Eval. unfold address_expr_8541 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8294 ?H8540 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8294 ?H8540 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8542 inputs path site mm old result :
 (exists width bits, VM.find 8292 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8541 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8542 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8292 [b8292 H8292]].
 intros [w8541 [b8541 H8541]].
 intro Eval. unfold address_expr_8542 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8292 ?H8541 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8292 ?H8541 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8543 inputs path site mm old result :
 (exists width bits, VM.find 8290 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8542 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8543 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8290 [b8290 H8290]].
 intros [w8542 [b8542 H8542]].
 intro Eval. unfold address_expr_8543 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8290 ?H8542 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8290 ?H8542 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8544 inputs path site mm old result :
 (exists width bits, VM.find 8288 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8543 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8544 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8288 [b8288 H8288]].
 intros [w8543 [b8543 H8543]].
 intro Eval. unfold address_expr_8544 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8288 ?H8543 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8288 ?H8543 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8545 inputs path site mm old result :
 (exists width bits, VM.find 8286 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8544 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8545 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8286 [b8286 H8286]].
 intros [w8544 [b8544 H8544]].
 intro Eval. unfold address_expr_8545 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8286 ?H8544 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8286 ?H8544 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8546 inputs path site mm old result :
 (exists width bits, VM.find 8284 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8545 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8546 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8284 [b8284 H8284]].
 intros [w8545 [b8545 H8545]].
 intro Eval. unfold address_expr_8546 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8284 ?H8545 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8284 ?H8545 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8547 inputs path site mm old result :
 (exists width bits, VM.find 8282 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8546 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8547 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8282 [b8282 H8282]].
 intros [w8546 [b8546 H8546]].
 intro Eval. unfold address_expr_8547 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8282 ?H8546 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8282 ?H8546 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8548 inputs path site mm old result :
 (exists width bits, VM.find 8280 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8547 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8548 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8280 [b8280 H8280]].
 intros [w8547 [b8547 H8547]].
 intro Eval. unfold address_expr_8548 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8280 ?H8547 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8280 ?H8547 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8549 inputs path site mm old result :
 (exists width bits, VM.find 8278 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8548 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8549 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8278 [b8278 H8278]].
 intros [w8548 [b8548 H8548]].
 intro Eval. unfold address_expr_8549 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8278 ?H8548 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8278 ?H8548 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8550 inputs path site mm old result :
 (exists width bits, VM.find 8276 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8549 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8550 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8276 [b8276 H8276]].
 intros [w8549 [b8549 H8549]].
 intro Eval. unfold address_expr_8550 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8276 ?H8549 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8276 ?H8549 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8551 inputs path site mm old result :
 (exists width bits, VM.find 8274 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8550 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8551 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8274 [b8274 H8274]].
 intros [w8550 [b8550 H8550]].
 intro Eval. unfold address_expr_8551 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8274 ?H8550 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8274 ?H8550 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8552 inputs path site mm old result :
 (exists width bits, VM.find 8272 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8551 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8552 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8272 [b8272 H8272]].
 intros [w8551 [b8551 H8551]].
 intro Eval. unfold address_expr_8552 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8272 ?H8551 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8272 ?H8551 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8553 inputs path site mm old result :
 (exists width bits, VM.find 8270 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8552 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8553 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8270 [b8270 H8270]].
 intros [w8552 [b8552 H8552]].
 intro Eval. unfold address_expr_8553 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8270 ?H8552 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8270 ?H8552 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8554 inputs path site mm old result :
 (exists width bits, VM.find 8268 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8553 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8554 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8268 [b8268 H8268]].
 intros [w8553 [b8553 H8553]].
 intro Eval. unfold address_expr_8554 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8268 ?H8553 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8268 ?H8553 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8555 inputs path site mm old result :
 (exists width bits, VM.find 8266 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8554 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8555 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8266 [b8266 H8266]].
 intros [w8554 [b8554 H8554]].
 intro Eval. unfold address_expr_8555 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8266 ?H8554 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8266 ?H8554 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8556 inputs path site mm old result :
 (exists width bits, VM.find 8264 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8555 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8556 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8264 [b8264 H8264]].
 intros [w8555 [b8555 H8555]].
 intro Eval. unfold address_expr_8556 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8264 ?H8555 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8264 ?H8555 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8557 inputs path site mm old result :
 (exists width bits, VM.find 8360 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8557 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8360 [b8360 H8360]].
 intro Eval. unfold address_expr_8557 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8360 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8360 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8558 inputs path site mm old result :
 (exists width bits, VM.find 8358 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8557 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8558 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8358 [b8358 H8358]].
 intros [w8557 [b8557 H8557]].
 intro Eval. unfold address_expr_8558 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8358 ?H8557 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8358 ?H8557 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8559 inputs path site mm old result :
 (exists width bits, VM.find 8356 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8558 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8559 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8356 [b8356 H8356]].
 intros [w8558 [b8558 H8558]].
 intro Eval. unfold address_expr_8559 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8356 ?H8558 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8356 ?H8558 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8560 inputs path site mm old result :
 (exists width bits, VM.find 8354 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8559 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8560 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8354 [b8354 H8354]].
 intros [w8559 [b8559 H8559]].
 intro Eval. unfold address_expr_8560 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8354 ?H8559 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8354 ?H8559 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8561 inputs path site mm old result :
 (exists width bits, VM.find 8352 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8560 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8561 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8352 [b8352 H8352]].
 intros [w8560 [b8560 H8560]].
 intro Eval. unfold address_expr_8561 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8352 ?H8560 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8352 ?H8560 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8562 inputs path site mm old result :
 (exists width bits, VM.find 8350 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8561 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8562 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8350 [b8350 H8350]].
 intros [w8561 [b8561 H8561]].
 intro Eval. unfold address_expr_8562 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8350 ?H8561 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8350 ?H8561 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8563 inputs path site mm old result :
 (exists width bits, VM.find 8348 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8562 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8563 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8348 [b8348 H8348]].
 intros [w8562 [b8562 H8562]].
 intro Eval. unfold address_expr_8563 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8348 ?H8562 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8348 ?H8562 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8564 inputs path site mm old result :
 (exists width bits, VM.find 8346 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8563 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8564 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8346 [b8346 H8346]].
 intros [w8563 [b8563 H8563]].
 intro Eval. unfold address_expr_8564 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8346 ?H8563 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8346 ?H8563 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8565 inputs path site mm old result :
 (exists width bits, VM.find 8344 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8564 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8565 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8344 [b8344 H8344]].
 intros [w8564 [b8564 H8564]].
 intro Eval. unfold address_expr_8565 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8344 ?H8564 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8344 ?H8564 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8566 inputs path site mm old result :
 (exists width bits, VM.find 8342 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8565 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8566 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8342 [b8342 H8342]].
 intros [w8565 [b8565 H8565]].
 intro Eval. unfold address_expr_8566 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8342 ?H8565 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8342 ?H8565 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8567 inputs path site mm old result :
 (exists width bits, VM.find 8340 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8566 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8567 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8340 [b8340 H8340]].
 intros [w8566 [b8566 H8566]].
 intro Eval. unfold address_expr_8567 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8340 ?H8566 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8340 ?H8566 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8568 inputs path site mm old result :
 (exists width bits, VM.find 8338 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8567 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8568 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8338 [b8338 H8338]].
 intros [w8567 [b8567 H8567]].
 intro Eval. unfold address_expr_8568 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8338 ?H8567 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8338 ?H8567 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8569 inputs path site mm old result :
 (exists width bits, VM.find 8336 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8568 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8569 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8336 [b8336 H8336]].
 intros [w8568 [b8568 H8568]].
 intro Eval. unfold address_expr_8569 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8336 ?H8568 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8336 ?H8568 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8570 inputs path site mm old result :
 (exists width bits, VM.find 8334 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8569 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8570 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8334 [b8334 H8334]].
 intros [w8569 [b8569 H8569]].
 intro Eval. unfold address_expr_8570 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8334 ?H8569 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8334 ?H8569 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8571 inputs path site mm old result :
 (exists width bits, VM.find 8332 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8570 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8571 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8332 [b8332 H8332]].
 intros [w8570 [b8570 H8570]].
 intro Eval. unfold address_expr_8571 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8332 ?H8570 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8332 ?H8570 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8572 inputs path site mm old result :
 (exists width bits, VM.find 8330 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8571 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8572 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8330 [b8330 H8330]].
 intros [w8571 [b8571 H8571]].
 intro Eval. unfold address_expr_8572 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8330 ?H8571 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8330 ?H8571 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8573 inputs path site mm old result :
 (exists width bits, VM.find 8328 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8572 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8573 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8328 [b8328 H8328]].
 intros [w8572 [b8572 H8572]].
 intro Eval. unfold address_expr_8573 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8328 ?H8572 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8328 ?H8572 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8574 inputs path site mm old result :
 (exists width bits, VM.find 8326 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8573 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8574 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8326 [b8326 H8326]].
 intros [w8573 [b8573 H8573]].
 intro Eval. unfold address_expr_8574 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8326 ?H8573 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8326 ?H8573 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8575 inputs path site mm old result :
 (exists width bits, VM.find 8324 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8574 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8575 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8324 [b8324 H8324]].
 intros [w8574 [b8574 H8574]].
 intro Eval. unfold address_expr_8575 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8324 ?H8574 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8324 ?H8574 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8576 inputs path site mm old result :
 (exists width bits, VM.find 8322 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8575 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8576 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8322 [b8322 H8322]].
 intros [w8575 [b8575 H8575]].
 intro Eval. unfold address_expr_8576 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8322 ?H8575 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8322 ?H8575 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8577 inputs path site mm old result :
 (exists width bits, VM.find 8320 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8576 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8577 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8320 [b8320 H8320]].
 intros [w8576 [b8576 H8576]].
 intro Eval. unfold address_expr_8577 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8320 ?H8576 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8320 ?H8576 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8578 inputs path site mm old result :
 (exists width bits, VM.find 8318 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8577 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8578 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8318 [b8318 H8318]].
 intros [w8577 [b8577 H8577]].
 intro Eval. unfold address_expr_8578 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8318 ?H8577 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8318 ?H8577 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8579 inputs path site mm old result :
 (exists width bits, VM.find 8316 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8578 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8579 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8316 [b8316 H8316]].
 intros [w8578 [b8578 H8578]].
 intro Eval. unfold address_expr_8579 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8316 ?H8578 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8316 ?H8578 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8580 inputs path site mm old result :
 (exists width bits, VM.find 8314 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8579 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8580 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8314 [b8314 H8314]].
 intros [w8579 [b8579 H8579]].
 intro Eval. unfold address_expr_8580 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8314 ?H8579 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8314 ?H8579 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8581 inputs path site mm old result :
 (exists width bits, VM.find 8312 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8580 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8581 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8312 [b8312 H8312]].
 intros [w8580 [b8580 H8580]].
 intro Eval. unfold address_expr_8581 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8312 ?H8580 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8312 ?H8580 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8582 inputs path site mm old result :
 (exists width bits, VM.find 8310 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8581 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8582 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8310 [b8310 H8310]].
 intros [w8581 [b8581 H8581]].
 intro Eval. unfold address_expr_8582 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8310 ?H8581 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8310 ?H8581 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8583 inputs path site mm old result :
 (exists width bits, VM.find 8308 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8582 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8583 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8308 [b8308 H8308]].
 intros [w8582 [b8582 H8582]].
 intro Eval. unfold address_expr_8583 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8308 ?H8582 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8308 ?H8582 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8584 inputs path site mm old result :
 (exists width bits, VM.find 8306 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8583 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8584 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8306 [b8306 H8306]].
 intros [w8583 [b8583 H8583]].
 intro Eval. unfold address_expr_8584 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8306 ?H8583 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8306 ?H8583 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8585 inputs path site mm old result :
 (exists width bits, VM.find 8304 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8584 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8585 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8304 [b8304 H8304]].
 intros [w8584 [b8584 H8584]].
 intro Eval. unfold address_expr_8585 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8304 ?H8584 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8304 ?H8584 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8586 inputs path site mm old result :
 (exists width bits, VM.find 8302 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8585 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8586 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8302 [b8302 H8302]].
 intros [w8585 [b8585 H8585]].
 intro Eval. unfold address_expr_8586 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8302 ?H8585 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8302 ?H8585 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8587 inputs path site mm old result :
 (exists width bits, VM.find 8300 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8586 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8587 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8300 [b8300 H8300]].
 intros [w8586 [b8586 H8586]].
 intro Eval. unfold address_expr_8587 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8300 ?H8586 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8300 ?H8586 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8588 inputs path site mm old result :
 (exists width bits, VM.find 8298 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8587 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8588 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8298 [b8298 H8298]].
 intros [w8587 [b8587 H8587]].
 intro Eval. unfold address_expr_8588 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8298 ?H8587 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8298 ?H8587 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8589 inputs path site mm old result :
 (exists width bits, VM.find 8296 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8588 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8589 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8296 [b8296 H8296]].
 intros [w8588 [b8588 H8588]].
 intro Eval. unfold address_expr_8589 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8296 ?H8588 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8296 ?H8588 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8590 inputs path site mm old result :
 (exists width bits, VM.find 8294 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8589 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8590 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8294 [b8294 H8294]].
 intros [w8589 [b8589 H8589]].
 intro Eval. unfold address_expr_8590 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8294 ?H8589 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8294 ?H8589 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8591 inputs path site mm old result :
 (exists width bits, VM.find 8292 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8590 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8591 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8292 [b8292 H8292]].
 intros [w8590 [b8590 H8590]].
 intro Eval. unfold address_expr_8591 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8292 ?H8590 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8292 ?H8590 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8592 inputs path site mm old result :
 (exists width bits, VM.find 8290 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8591 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8592 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8290 [b8290 H8290]].
 intros [w8591 [b8591 H8591]].
 intro Eval. unfold address_expr_8592 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8290 ?H8591 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8290 ?H8591 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8593 inputs path site mm old result :
 (exists width bits, VM.find 8288 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8592 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8593 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8288 [b8288 H8288]].
 intros [w8592 [b8592 H8592]].
 intro Eval. unfold address_expr_8593 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8288 ?H8592 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8288 ?H8592 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8594 inputs path site mm old result :
 (exists width bits, VM.find 8286 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8593 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8594 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8286 [b8286 H8286]].
 intros [w8593 [b8593 H8593]].
 intro Eval. unfold address_expr_8594 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8286 ?H8593 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8286 ?H8593 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8595 inputs path site mm old result :
 (exists width bits, VM.find 8284 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8594 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8595 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8284 [b8284 H8284]].
 intros [w8594 [b8594 H8594]].
 intro Eval. unfold address_expr_8595 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8284 ?H8594 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8284 ?H8594 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8596 inputs path site mm old result :
 (exists width bits, VM.find 8282 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8595 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8596 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8282 [b8282 H8282]].
 intros [w8595 [b8595 H8595]].
 intro Eval. unfold address_expr_8596 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8282 ?H8595 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8282 ?H8595 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8597 inputs path site mm old result :
 (exists width bits, VM.find 8280 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8596 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8597 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8280 [b8280 H8280]].
 intros [w8596 [b8596 H8596]].
 intro Eval. unfold address_expr_8597 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8280 ?H8596 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8280 ?H8596 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8598 inputs path site mm old result :
 (exists width bits, VM.find 8278 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8597 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8598 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8278 [b8278 H8278]].
 intros [w8597 [b8597 H8597]].
 intro Eval. unfold address_expr_8598 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8278 ?H8597 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8278 ?H8597 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8599 inputs path site mm old result :
 (exists width bits, VM.find 8276 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8598 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8599 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8276 [b8276 H8276]].
 intros [w8598 [b8598 H8598]].
 intro Eval. unfold address_expr_8599 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8276 ?H8598 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8276 ?H8598 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8600 inputs path site mm old result :
 (exists width bits, VM.find 8274 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8599 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8600 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8274 [b8274 H8274]].
 intros [w8599 [b8599 H8599]].
 intro Eval. unfold address_expr_8600 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8274 ?H8599 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8274 ?H8599 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8601 inputs path site mm old result :
 (exists width bits, VM.find 8272 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8600 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8601 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8272 [b8272 H8272]].
 intros [w8600 [b8600 H8600]].
 intro Eval. unfold address_expr_8601 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8272 ?H8600 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8272 ?H8600 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8602 inputs path site mm old result :
 (exists width bits, VM.find 8270 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8601 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8602 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8270 [b8270 H8270]].
 intros [w8601 [b8601 H8601]].
 intro Eval. unfold address_expr_8602 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8270 ?H8601 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8270 ?H8601 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8603 inputs path site mm old result :
 (exists width bits, VM.find 8268 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8602 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8603 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8268 [b8268 H8268]].
 intros [w8602 [b8602 H8602]].
 intro Eval. unfold address_expr_8603 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8268 ?H8602 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8268 ?H8602 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8604 inputs path site mm old result :
 (exists width bits, VM.find 8266 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8603 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8604 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8266 [b8266 H8266]].
 intros [w8603 [b8603 H8603]].
 intro Eval. unfold address_expr_8604 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8266 ?H8603 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8266 ?H8603 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_8605 inputs path site mm old result :
 (exists width bits, VM.find 8264 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 8604 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_8605 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w8264 [b8264 H8264]].
 intros [w8604 [b8604 H8604]].
 intro Eval. unfold address_expr_8605 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H8264 ?H8604 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H8264 ?H8604 in Eval.
 cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.
 try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.
 repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma address_uint_result_9182 inputs path site mm old result :
 (exists width bits, VM.find 37 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9182 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w37 [b37 H37]].
 apply formal_uint_scalar_concrete. unfold address_expr_9182. solve_address_uint_ready.
Qed.
Lemma address_uint_result_9186 inputs path site mm old result :
 (exists width bits, VM.find 9182 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9186 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w9182 [b9182 H9182]].
 apply formal_uint_scalar_concrete. unfold address_expr_9186. solve_address_uint_ready.
Qed.
Lemma address_uint_result_9194 inputs path site mm old result :
 (exists width bits, VM.find 9182 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9194 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w9182 [b9182 H9182]].
 apply formal_uint_scalar_concrete. unfold address_expr_9194. solve_address_uint_ready.
Qed.
Lemma address_uint_result_9202 inputs path site mm old result :
 (exists width bits, VM.find 9182 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9202 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w9182 [b9182 H9182]].
 apply formal_uint_scalar_concrete. unfold address_expr_9202. solve_address_uint_ready.
Qed.
Lemma address_uint_result_9210 inputs path site mm old result :
 (exists width bits, VM.find 9182 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9210 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w9182 [b9182 H9182]].
 apply formal_uint_scalar_concrete. unfold address_expr_9210. solve_address_uint_ready.
Qed.
Lemma address_uint_result_9215 inputs path site mm old result :
 (exists width bits, VM.find 1 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9215 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1 [b1 H1]].
 apply formal_uint_scalar_concrete. unfold address_expr_9215. solve_address_uint_ready.
Qed.
Lemma address_uint_result_9216 inputs path site mm old result :
 (exists width bits, VM.find 9215 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9216 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w9215 [b9215 H9215]].
 apply formal_uint_scalar_concrete. unfold address_expr_9216. solve_address_uint_ready.
Qed.
Lemma address_uint_result_9217 inputs path site mm old result :
 (exists width bits, VM.find 1 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9217 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1 [b1 H1]].
 apply formal_uint_scalar_concrete. unfold address_expr_9217. solve_address_uint_ready.
Qed.
Lemma address_uint_result_9218 inputs path site mm old result :
 (exists width bits, VM.find 9217 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9218 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w9217 [b9217 H9217]].
 apply formal_uint_scalar_concrete. unfold address_expr_9218. solve_address_uint_ready.
Qed.
Lemma address_uint_result_9221 inputs path site mm old result :
 (exists width bits, VM.find 9182 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_9221 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w9182 [b9182 H9182]].
 apply formal_uint_scalar_concrete. unfold address_expr_9221. solve_address_uint_ready.
Qed.
Print Assumptions address_uint_result_9221.
