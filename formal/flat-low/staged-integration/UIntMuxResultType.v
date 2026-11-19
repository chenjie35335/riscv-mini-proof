From nbits Require Import NBits.
Require Import ScalarSinkTypes.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma uint_mux_result_type mm old (condition : hfexpr VarOrder.T) (yes no : VarOrder.T) width left right result :
 VM.find yes old = Some left -> type_of_val left = Gtyp (Fuint width) ->
 VM.find no old = Some right -> type_of_val right = Gtyp (Fuint width) ->
 eval_hfexpr_with_memory mm (Emux condition (Eref (Eid yes)) (Eref (Eid no))) old old = Some result ->
 type_of_val result = Gtyp (Fuint width).
Proof.
 intros Left LeftType Right RightType Eval.
 assert (YesType : eval_type_of_expr (Eref (Eid yes)) old = Some (Gtyp (Fuint width))).
 { unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Left. cbn [option_map]. rewrite LeftType. reflexivity. }
 assert (NoType : eval_type_of_expr (Eref (Eid no)) old = Some (Gtyp (Fuint width))).
 { unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Right. cbn [option_map]. rewrite RightType. reflexivity. }
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite Left Right YesType NoType in Eval.
 destruct (eval_hfexpr_with_memory mm condition old old) as [value|] eqn:Condition; [|discriminate Eval].
 destruct value as [ground bits|element values|fields|typ|typ|typ]; try discriminate Eval.
 - destruct ground; try discriminate Eval. destruct (is_zero bits);
   unfold extend_hvalue_as_type in Eval; rewrite ?LeftType ?RightType in Eval;
   cbn [ftype_mux fgtyp_mux] in Eval; rewrite maxnn in Eval;
   eapply adapted_uint_result_type; exact Eval.
 - destruct typ as [ground|element count|fields]; try discriminate Eval.
   destruct ground; try discriminate Eval; cbn [ftype_mux fgtyp_mux option_map] in Eval;
   rewrite maxnn in Eval; inversion Eval; reflexivity.
 - destruct typ as [ground|element count|fields]; try discriminate Eval.
   destruct ground; try discriminate Eval; cbn [ftype_mux fgtyp_mux option_map] in Eval;
   rewrite maxnn in Eval; inversion Eval; reflexivity.
 - destruct typ as [ground|element count|fields]; try discriminate Eval.
   destruct ground; try discriminate Eval; cbn [ftype_mux fgtyp_mux option_map] in Eval;
   rewrite maxnn in Eval; inversion Eval; reflexivity.
Qed.
Print Assumptions uint_mux_result_type.
