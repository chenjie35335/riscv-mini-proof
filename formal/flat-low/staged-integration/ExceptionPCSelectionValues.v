Require Import CoreSocModel ComparisonNodes ExceptionPCSelectionNodes FormalRFResetPropagation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma exception_pc_selected_7087_nonzero old bits other control_width control_bits :
 size bits = 32%nat ->
 VM.find 6780 old = Some (Gval (Fuint control_width) control_bits) ->
 is_zero control_bits = false ->
 VM.find 2812 old = Some (Gval (Fuint 32) bits) ->
 VM.find 7086 old = Some (Gval (Fuint 32) other) ->
 eval_hfexpr_with_memory flat_memories exception_pc_selection_7087_expr old old = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Condition Nonzero Source Other.
 cbn [exception_pc_selection_7087_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Condition Nonzero.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Other.
 change (adapt_hvalue_as_type (Gval (Fuint 32) bits) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) bits)).
 exact (sized_uint_adapt_identity 32 bits Size).
Qed.
Print Assumptions exception_pc_selected_7087_nonzero.

Lemma exception_pc_selected_7119 old bits other :
 size bits = 32%nat ->
 VM.find 1707 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7087 old = Some (Gval (Fuint 32) bits) ->
 VM.find 7086 old = Some (Gval (Fuint 32) other) ->
 eval_hfexpr_with_memory flat_memories exception_pc_selection_7119_expr old old = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Condition Source Other.
 cbn [exception_pc_selection_7119_expr eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Condition. cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Other.
 change (adapt_hvalue_as_type (Gval (Fuint 32) bits) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) bits)).
 exact (sized_uint_adapt_identity 32 bits Size).
Qed.
Print Assumptions exception_pc_selected_7119.
