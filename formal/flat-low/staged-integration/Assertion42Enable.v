Require Import Assertion44Enable Assertion42GuardNodes.
Require Import CoreSocModel ComparisonNodes ReferenceEventNodes ReferenceEventConnections ExceptionEventConnections FormalDeclaredConnectionObservation NormalizedBit NormalizedOr.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition assertion42_enable := (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band
 (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727)))
 (@Eref VarOrder.T (@Eid VarOrder.T 7738))) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma assertion42_guard_after_two invalid s0 s1 s2 bit :
 VM.find 1394 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7738 s2 = Some (Gval (Fuint 1) [::negb bit]).
Proof.
 intros Reset S1 S2.
 assert (Extract : VM.find 7737 s1 = Some (Gval (Fuint 1) [::bit])).
 { rewrite (reference_event_equation_7741 invalid s0 s0 s1 S1).
   cbn [reference_event_expr_7741 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Reset. destruct bit; reflexivity. }
 rewrite (reference_event_equation_7742 invalid s1 s1 s2 S2).
 cbn [reference_event_expr_7742 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Extract. destruct bit; reflexivity.
Qed.
Lemma assertion42_enabled_parts env value guard :
 VM.find 7727 env = Some value -> normalized_bit value ->
 VM.find 7738 env = Some guard -> normalized_bit guard ->
 generated_expr_true assertion42_enable env ->
 value = Gval (Fuint 1) [::true] /\ guard = Gval (Fuint 1) [::true].
Proof.
 intros Value NV Guard NG Enabled.
 unfold generated_expr_true, assertion42_enable in Enabled.
 cbn [eval_hfexpr eval_href] in Enabled. rewrite Value Guard in Enabled.
 destruct NV as [v| | |]; destruct NG as [g| | |]; try destruct v; try destruct g;
 vm_compute in Enabled; try discriminate Enabled; try contradiction; split; reflexivity.
Qed.
Theorem assertion42_enabled_reset_and_or invalid s0 s1 s2 bit :
 VM.find 1394 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 generated_expr_true assertion42_enable s2 ->
 bit = false /\ VM.find 7727 s2 = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Reset S1 S2 Enabled.
 destruct (assertion44_or_normalized_after_two invalid s0 s1 s2 S1 S2) as [value [Value Normal]].
 pose proof (assertion42_guard_after_two invalid s0 s1 s2 bit Reset S1 S2) as Guard.
 destruct (assertion42_enabled_parts s2 value _ Value Normal Guard (normalized_known (negb bit)) Enabled) as [TrueOr TrueGuard].
 split; [destruct bit; [discriminate TrueGuard|reflexivity]|rewrite <- TrueOr; exact Value].
Qed.
