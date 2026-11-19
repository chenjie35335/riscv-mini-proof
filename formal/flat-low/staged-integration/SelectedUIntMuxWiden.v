Require Import UIntResizeRoundtrip.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma selected_uint_mux_widen mm old (condition yes no : VarOrder.T) input_width target_width bits source value :
 size bits = input_width -> input_width <= target_width ->
 VM.find condition old = Some (Gval (Fuint 1) [::true]) ->
 VM.find yes old = Some (Gval (Fuint input_width) bits) ->
 eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint target_width)) = Some value ->
 value = Gval (Fuint target_width) (zext_to target_width bits).
Proof.
 intros Size Target Condition Yes Eval Adapt.
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite Condition in Eval. cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite Yes in Eval.
 destruct (eval_type_of_expr (Eref (Eid no)) old) as [ty|]; [|discriminate].
 unfold extend_hvalue_as_type in Eval.
 destruct ty as [ground|element count|fields]; try discriminate.
 destruct ground; cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval; try discriminate.
 inversion Eval; subst source.
 cbn [adapt_hvalue_as_type] in Adapt. inversion Adapt; subst value.
 f_equal. apply (resize_uint_roundtrip_widen input_width target_width _ bits); [exact Size|exact Target|apply leq_maxl].
Qed.
Print Assumptions selected_uint_mux_widen.
