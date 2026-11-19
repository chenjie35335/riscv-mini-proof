Require Import CoreSocModel ComparisonNodes ReferencePCUpdateNodes FalseUIntMuxShape UIntLowExtractRoundtrip.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_pc_stutter_selection_after_two invalid s0 s1 s2 bits :
 size bits = 32%nat ->
 VM.find 1707 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 2812 s0 = Some (Gval (Fuint 32) bits) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7149 s2 = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Disabled Source S1 S2.
 destruct (reference_pc_update_7109_evaluation invalid s0 s0 s1 S1) as [value Eval].
 destruct (false_uint_mux_source_shape flat_memories s0 1707 7094 2812 32 bits value Disabled Source Eval)
 as [larger [Bound Shape]]. subst value.
 pose proof (reference_pc_update_7109_value invalid s0 s0 s1 larger _ Eval S1) as Mux.
 apply (reference_pc_update_7149_value invalid s1 s1 s2 32 bits); [|exact S2].
 cbn [reference_pc_update_7149_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Mux.
 exact (uint32_low_extract_roundtrip larger bits Size Bound).
Qed.
Print Assumptions reference_pc_stutter_selection_after_two.
