Require Import CoreSocModel ComparisonNodes FormalRFResetSource FormalRFSourceAliases FormalRFResetConnections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma sized_uint_adapt_identity width word :
 size word = width ->
 adapt_hvalue_as_type (Gval (Fuint width) word) (Gtyp (Fuint width)) = Some (Gval (Fuint width) word).
Proof.
 intro Size. cbn [adapt_hvalue_as_type].
 rewrite -Size take_size /zext_to subnn /zext /= cats0. reflexivity.
Qed.
Definition formal_flat_step inputs path old next :=
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false old flat_statements = Some next.
Theorem rf_symbolic_reset_after_four inputs path s0 s1 s2 s3 s4 :
 formal_flat_step inputs path s0 s1 -> formal_flat_step inputs path s1 s2 ->
 formal_flat_step inputs path s2 s3 -> formal_flat_step inputs path s3 s4 ->
 VM.find 1086 s4 = Some (Gval (Fuint 32) (rf_symbolic_source_word inputs path)).
Proof.
 intros S1 S2 S3 S4.
 pose proof (rf_symbolic_reset_node inputs path s0 s0 s1 S1) as First.
 assert (Second : VM.find 8092 s2 = Some (Gval (Fuint 32) (rf_symbolic_source_word inputs path))).
 { eapply rf_source_node_8092; [|reflexivity|exact S2].
   cbn [rf_source_expr_8092 eval_hfexpr_with_memory eval_href_with_memory]. rewrite First. reflexivity. }
 assert (Third : VM.find 788 s3 = Some (Gval (Fuint 32) (rf_symbolic_source_word inputs path))).
 { eapply rf_reset_connection_788; [exact Second| |exact S3].
   apply sized_uint_adapt_identity. exact (rf_symbolic_source_width inputs path). }
 eapply rf_source_node_1086; [|reflexivity|exact S4].
 cbn [rf_source_expr_1086 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Third. reflexivity.
Qed.
Print Assumptions rf_symbolic_reset_after_four.
