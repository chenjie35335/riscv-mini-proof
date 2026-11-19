Require Import SelectedUIntMuxIdentity.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma selected_bit_constant_mux_identity mm old (condition no : VarOrder.T) bit source value :
 VM.find condition old = Some (Gval (Fuint 1) [::true]) ->
 eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Econst VarOrder.T (Fuint 1) [::bit]) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint 1)) = Some value ->
 value = Gval (Fuint 1) [::bit].
Proof.
 intros Condition Eval Adapt.
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite Condition in Eval. cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 destruct (eval_type_of_expr (Eref (Eid no)) old) as [ty|]; [|discriminate].
 unfold extend_hvalue_as_type in Eval.
 destruct ty as [ground|element count|fields]; try discriminate.
 destruct ground; cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval; try discriminate.
 inversion Eval; subst source.
 cbn [adapt_hvalue_as_type] in Adapt. inversion Adapt; subst value.
 f_equal. apply resize_uint_roundtrip; [reflexivity|apply leq_maxl].
Qed.
Print Assumptions selected_bit_constant_mux_identity.
