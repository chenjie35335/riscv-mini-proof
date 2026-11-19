From nbits Require Import NBits.
Require Import ScalarSinkTypes.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma uint32_zero_mux_result_type mm old (condition : hfexpr VarOrder.T) (yes : VarOrder.T) left result :
 VM.find yes old = Some left -> type_of_val left = Gtyp (Fuint 32) ->
 eval_hfexpr_with_memory mm (Emux condition (Eref (Eid yes)) (@Econst VarOrder.T (Fuint 1) [::false])) old old = Some result ->
 type_of_val result = Gtyp (Fuint 32).
Proof.
 intros Left LeftType Eval.
 assert (YesType : eval_type_of_expr (Eref (Eid yes)) old = Some (Gtyp (Fuint 32))).
 { unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Left. cbn [option_map]. rewrite LeftType. reflexivity. }
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite Left YesType in Eval.
 destruct (eval_hfexpr_with_memory mm condition old old) as [value|] eqn:Condition; [|discriminate Eval].
 destruct value as [ground bits|element values|fields|typ|typ|typ]; try discriminate Eval.
 - destruct ground; try discriminate Eval. destruct (is_zero bits);
   unfold extend_hvalue_as_type in Eval; rewrite ?LeftType in Eval;
   cbn [eval_type_of_expr type_of_expr' type_of_val ftype_mux fgtyp_mux] in Eval;
   eapply adapted_uint_result_type; exact Eval.
 - destruct typ as [ground|element count|fields]; try discriminate Eval.
   destruct ground; try discriminate Eval; cbn [eval_type_of_expr type_of_expr' ftype_mux fgtyp_mux option_map] in Eval;
   inversion Eval; reflexivity.
 - destruct typ as [ground|element count|fields]; try discriminate Eval.
   destruct ground; try discriminate Eval; cbn [eval_type_of_expr type_of_expr' ftype_mux fgtyp_mux option_map] in Eval;
   inversion Eval; reflexivity.
 - destruct typ as [ground|element count|fields]; try discriminate Eval.
   destruct ground; try discriminate Eval; cbn [eval_type_of_expr type_of_expr' ftype_mux fgtyp_mux option_map] in Eval;
   inversion Eval; reflexivity.
Qed.
Print Assumptions uint32_zero_mux_result_type.
