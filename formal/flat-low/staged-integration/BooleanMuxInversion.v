Require Import NormalizedBit.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma normalized_booleanize_value mm env (condition : VarOrder.T) value :
 VM.find condition env = Some value -> normalized_bit value ->
 exists result, eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Econst VarOrder.T (Fuint 1) [::true]) (@Econst VarOrder.T (Fuint 1) [::false])) env env = Some result /\ normalized_bit result.
Proof.
 intros Lookup Normal.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Lookup.
 destruct Normal as [b| | |]; try destruct b.
 all: vm_compute; eexists; split; [reflexivity|first [exact (normalized_known true)|exact (normalized_known false)|exact normalized_pending|exact normalized_uninitialized|exact normalized_invalid]].
Qed.
Lemma normalized_mux_with_false_true mm env (condition yes no : VarOrder.T) control selected :
 VM.find condition env = Some control -> normalized_bit control ->
 VM.find yes env = Some selected -> normalized_bit selected ->
 VM.find no env = Some (Gval (Fuint 1) [::false]) ->
 eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) env env = Some (Gval (Fuint 1) [::true]) ->
 control = Gval (Fuint 1) [::true] /\ selected = Gval (Fuint 1) [::true].
Proof.
 intros Control NC Selected NS No.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Control.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite Selected No.
 destruct NC as [c| | |]; destruct NS as [s| | |]; try destruct c; try destruct s;
 vm_compute; intro Eval; try discriminate Eval; split; reflexivity.
Qed.
Print Assumptions normalized_mux_with_false_true.
