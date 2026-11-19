Require Import NormalizedBit.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma normalized_mux_with_false_result mm env (condition yes no : VarOrder.T) control selected :
 VM.find condition env = Some control -> normalized_bit control ->
 VM.find yes env = Some selected -> normalized_bit selected ->
 VM.find no env = Some (Gval (Fuint 1) [::false]) ->
 exists result, eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) env env = Some result /\ normalized_bit result.
Proof.
 intros Control NC Selected NS No.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Control.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
 rewrite Selected No.
 destruct NC as [c| | |]; destruct NS as [s| | |]; try destruct c; try destruct s.
 all: vm_compute; eexists; split; [reflexivity|first [exact (normalized_known true)|exact (normalized_known false)|exact normalized_pending|exact normalized_uninitialized|exact normalized_invalid]].
Qed.
Print Assumptions normalized_mux_with_false_result.
