Require Import FlatRegFileX0.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.

Lemma rf_selected_nonzero_address env b0 b1 b2 b3 b4 source :
 eval_href rf_addr_ref env env = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 VM.find (N.of_nat 988) env = Some source ->
 type_of_val source = Gtyp (Fuint 32) ->
 is_zero [::b0;b1;b2;b3;b4] = false ->
 eval_hfexpr rf_x0_selected_expr env env = Some rf_zero32.
Proof.
 intros Address Data Typed Nonzero.
 unfold rf_x0_selected_expr. cbn [eval_hfexpr]. rewrite Address.
 cbn [rf_zero_expr eval_hfexpr].
 destruct b0, b1, b2, b3, b4; try discriminate Nonzero;
 cbn [eval_binop eval_binop_basic absorbing_bit refine_boolean_result];
 cbn [is_zero eval_hfexpr eval_href];
 unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref];
 rewrite Data; cbn [option_map]; rewrite Typed; reflexivity.
Qed.
Print Assumptions rf_selected_nonzero_address.

Theorem rf_three_rounds_unknown_data first second third fourth enable b0 b1 b2 b3 b4 source :
 eval_href rf_addr_ref first first = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 eval_href rf_addr_ref second second = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 eval_href rf_enable_ref second second = Some (Gval (Fuint 1) [::enable]) ->
 VM.find (N.of_nat 988) second = Some source ->
 type_of_val source = Gtyp (Fuint 32) ->
 eval_type_of_ref (@Eid VarOrder.T (N.of_nat 989)) third = Some (Gtyp (Fuint 32)) ->
 rf_x0_round first second -> rf_x0_round second third -> rf_x0_round third fourth ->
 VM.find (N.of_nat 1053) fourth = Some rf_zero32.
Proof.
 intros AddressFirst AddressSecond Enable Data Typed ThirdType
   [Reduction _] [_ [Guard [Selected _]]] [_ [_ [_ Output]]].
 rewrite (rf_addr_value first _ AddressFirst) in Reduction.
 rewrite (rf_guard_value second enable _ Enable Reduction) in Guard.
 rewrite Output.
 destruct enable, b0, b1, b2, b3, b4;
 cbn [foldr andb orb] in Guard;
 first [apply rf_x0_output_disabled; [exact Guard|exact ThirdType] |
   apply rf_x0_output_enabled; [exact Guard|
     rewrite Selected; eapply rf_selected_nonzero_address; [exact AddressSecond|exact Data|exact Typed|reflexivity]]].
Qed.
Print Assumptions rf_three_rounds_unknown_data.
Lemma rf_selected_result_type env b0 b1 b2 b3 b4 source result :
 eval_href rf_addr_ref env env = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 VM.find (N.of_nat 988) env = Some source ->
 type_of_val source = Gtyp (Fuint 32) ->
 eval_hfexpr rf_x0_selected_expr env env = Some result ->
 type_of_val result = Gtyp (Fuint 32).
Proof.
 intros Address Data Typed.
 unfold rf_x0_selected_expr. cbn [eval_hfexpr]. rewrite Address.
 cbn [rf_zero_expr eval_hfexpr].
 destruct b0, b1, b2, b3, b4;
 cbn [eval_binop eval_binop_basic absorbing_bit refine_boolean_result];
 cbn [is_zero eval_hfexpr eval_href];
 unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref];
 rewrite Data; cbn [option_map]; try rewrite Typed.
 all: destruct source as [ground bits|element array|bundle|t|t|t];
 cbn [type_of_val] in Typed; try discriminate Typed; inversion Typed; subst;
 cbn [extend_hvalue_as_type adapt_hvalue_as_type ftype_mux];
 intro Step; inversion Step; reflexivity.
Qed.
Lemma rf_selected_total env b0 b1 b2 b3 b4 source :
 eval_href rf_addr_ref env env = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 VM.find (N.of_nat 988) env = Some source ->
 type_of_val source = Gtyp (Fuint 32) ->
 exists result, eval_hfexpr rf_x0_selected_expr env env = Some result /\
 type_of_val result = Gtyp (Fuint 32).
Proof.
 intros Address Data Typed.
 unfold rf_x0_selected_expr. cbn [eval_hfexpr]. rewrite Address.
 cbn [rf_zero_expr eval_hfexpr].
 destruct b0, b1, b2, b3, b4;
 cbn [eval_binop eval_binop_basic absorbing_bit refine_boolean_result];
 cbn [is_zero eval_hfexpr eval_href];
 unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref];
 rewrite Data; cbn [option_map]; try rewrite Typed.
 all: destruct source as [ground bits|element array|bundle|t|t|t];
 cbn [type_of_val] in Typed; try discriminate Typed; inversion Typed; subst;
 cbn [extend_hvalue_as_type adapt_hvalue_as_type ftype_mux];
 eexists; split; reflexivity.
Qed.
