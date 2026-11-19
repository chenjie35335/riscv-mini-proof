Require Import FormalCheckerResetConnections.
Require Import CoreSocModel ComparisonNodes ReferenceEventNodes ReferenceEventConnections ExceptionEventConnections FormalDeclaredConnectionObservation NormalizedBit NormalizedOr.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition assertion44_enable := (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band
 (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727)))
 (@Eref VarOrder.T (@Eid VarOrder.T 7746))) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma implementation_event_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1469 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (declared_connection_observation 1548 flat_statements exception_event_1469_decl exception_event_1469_mid exception_event_1469_tail
 1469 8242 1 invalid flat_memories old current result
 exception_event_1469_position exception_event_1469_split exception_event_1469_straight exception_event_1469_mid_safe exception_event_1469_tail_safe exception_event_1469_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Lemma reference_event_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 1667 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (reference_event_connection_1667_observation invalid old current result Step)
 as [source [value [Source [Adapt Value]]]].
 exists value. split; [exact Value|exact (adapted_bit_normalized source value Adapt)].
Qed.
Lemma assertion44_or_normalized_after_two invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 exists value, VM.find 7727 s2 = Some value /\ normalized_bit value.
Proof.
 intros S1 S2.
 destruct (implementation_event_normalized invalid s0 s0 s1 S1) as [left [Left NL]].
 destruct (reference_event_normalized invalid s0 s0 s1 S1) as [right [Right NR]].
 exists (normalized_or_value left right). split.
 - rewrite (reference_event_equation_7727 invalid s1 s1 s2 S2).
   cbn [reference_event_expr_7727 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR).
 - exact (normalized_or_normal left right NL NR).
Qed.
Lemma assertion44_guard_after_two invalid s0 s1 s2 bit :
 VM.find 1394 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7746 s2 = Some (Gval (Fuint 1) [::negb bit]).
Proof.
 intros Reset S1 S2.
 assert (Extract : VM.find 7745 s1 = Some (Gval (Fuint 1) [::bit])).
 { rewrite (reference_event_equation_7745 invalid s0 s0 s1 S1).
   cbn [reference_event_expr_7745 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Reset. destruct bit; reflexivity. }
 rewrite (reference_event_equation_7746 invalid s1 s1 s2 S2).
 cbn [reference_event_expr_7746 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Extract. destruct bit; reflexivity.
Qed.
Lemma assertion44_enabled_parts env value guard :
 VM.find 7727 env = Some value -> normalized_bit value ->
 VM.find 7746 env = Some guard -> normalized_bit guard ->
 generated_expr_true assertion44_enable env ->
 value = Gval (Fuint 1) [::true] /\ guard = Gval (Fuint 1) [::true].
Proof.
 intros Value NV Guard NG Enabled.
 unfold generated_expr_true, assertion44_enable in Enabled.
 cbn [eval_hfexpr eval_href] in Enabled. rewrite Value Guard in Enabled.
 destruct NV as [v| | |]; destruct NG as [g| | |]; try destruct v; try destruct g;
 vm_compute in Enabled; try discriminate Enabled; try contradiction; split; reflexivity.
Qed.
Theorem assertion44_enabled_reset_and_or invalid s0 s1 s2 bit :
 VM.find 1394 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 generated_expr_true assertion44_enable s2 ->
 bit = false /\ VM.find 7727 s2 = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Reset S1 S2 Enabled.
 destruct (assertion44_or_normalized_after_two invalid s0 s1 s2 S1 S2) as [value [Value Normal]].
 pose proof (assertion44_guard_after_two invalid s0 s1 s2 bit Reset S1 S2) as Guard.
 destruct (assertion44_enabled_parts s2 value _ Value Normal Guard (normalized_known (negb bit)) Enabled) as [TrueOr TrueGuard].
 split; [destruct bit; [discriminate TrueGuard|reflexivity]|rewrite <- TrueOr; exact Value].
Qed.
Theorem assertion44_or_true_reference invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 1469 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7727 s2 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1667 s1 = Some (Gval (Fuint 1) [::true]).
Proof.
 intros S1 S2 Implementation OrTrue.
 destruct (reference_event_normalized invalid s0 s0 s1 S1) as [value [Value Normal]].
 rewrite (reference_event_equation_7727 invalid s1 s1 s2 S2) in OrTrue.
 cbn [reference_event_expr_7727 eval_hfexpr_with_memory eval_href_with_memory] in OrTrue.
 rewrite Implementation Value in OrTrue.
 destruct Normal as [b| | |]; try destruct b; vm_compute in OrTrue; try discriminate OrTrue; exact Value.
Qed.
Print Assumptions assertion44_enabled_reset_and_or.
Print Assumptions assertion44_or_true_reference.

Lemma assertion44_checker_reset_after_three invalid s0 s1 s2 s3 bit :
 VM.find 1 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 1394 s3 = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Reset S1 S2 S3.
 exact (reset_connection_1394_transfer invalid s2 s2 s3 bit
 (reset_connection_65_transfer invalid s1 s1 s2 bit
 (reset_connection_24_transfer invalid s0 s0 s1 bit Reset S1) S2) S3).
Qed.
Print Assumptions assertion44_checker_reset_after_three.
