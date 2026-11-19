Require Import CoreSocModel ComparisonNodes ExceptionSelectionNodes FormalRFResetPropagation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma exception_instruction_input_selected old bits :
 size bits = 32%nat ->
 VM.find 1707 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1706 old = Some (Gval (Fuint 32) bits) ->
 eval_hfexpr_with_memory flat_memories exception_selection_1883_expr old old = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Condition Source.
 cbn [exception_selection_1883_expr eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Condition. cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
 change (adapt_hvalue_as_type (Gval (Fuint 32) bits) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) bits)).
 exact (sized_uint_adapt_identity 32 bits Size).
Qed.
Lemma exception_instruction_extract_identity old bits :
 size bits = 32%nat ->
 VM.find 1884 old = Some (Gval (Fuint 32) bits) ->
 eval_hfexpr_with_memory flat_memories exception_selection_6811_expr old old = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Source.
 cbn [exception_selection_6811_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
 cbn [eval_unop].
 assert (Bound : (0 <= 31 < 32)%nat = true) by (vm_compute; reflexivity).
 rewrite Bound subn0 drop0.
 change (Some (Gval (Fuint 32) (take 32 bits)) = Some (Gval (Fuint 32) bits)).
 rewrite -Size take_size. reflexivity.
Qed.
Lemma exception_instruction_selected_7089 old bits other :
 size bits = 32%nat ->
 VM.find 6780 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 6811 old = Some (Gval (Fuint 32) bits) ->
 VM.find 7088 old = Some (Gval (Fuint 32) other) ->
 eval_hfexpr_with_memory flat_memories exception_selection_7089_expr old old = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Condition Source Other.
 cbn [exception_selection_7089_expr eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Condition. cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Other.
 change (adapt_hvalue_as_type (Gval (Fuint 32) bits) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) bits)).
 exact (sized_uint_adapt_identity 32 bits Size).
Qed.
Lemma exception_instruction_selected_7120 old bits other :
 size bits = 32%nat ->
 VM.find 1707 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7089 old = Some (Gval (Fuint 32) bits) ->
 VM.find 7088 old = Some (Gval (Fuint 32) other) ->
 eval_hfexpr_with_memory flat_memories exception_selection_7120_expr old old = Some (Gval (Fuint 32) bits).
Proof.
 intros Size Condition Source Other.
 cbn [exception_selection_7120_expr eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Condition. cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Other.
 change (adapt_hvalue_as_type (Gval (Fuint 32) bits) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) bits)).
 exact (sized_uint_adapt_identity 32 bits Size).
Qed.
Print Assumptions exception_instruction_selected_7120.
