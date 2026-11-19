From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma false_uint_mux_source_shape mm old (condition yes no : VarOrder.T) width bits source :
 VM.find condition old = Some (Gval (Fuint 1) [::false]) ->
 VM.find no old = Some (Gval (Fuint width) bits) ->
 eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source ->
 exists result_width, width <= result_width /\
 source = Gval (Fuint result_width) (zext_to result_width (take result_width bits)).
Proof.
 intros Condition No Eval.
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite Condition in Eval. cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite No in Eval.
 destruct (eval_type_of_expr (Eref (Eid yes)) old) as [ty|] eqn:OtherType; [|discriminate].
 unfold extend_hvalue_as_type in Eval.
 destruct ty as [ground|element count|fields]; try discriminate.
 destruct ground; cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval; try discriminate.
 inversion Eval; subst source. eexists. split; [apply leq_maxl|reflexivity].
Qed.
Print Assumptions false_uint_mux_source_shape.
