Require Import CoreSocModel ComparisonNodes LegalAssumptionNodes NormalizedBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma assumption_reset_enable_after_two invalid s0 s1 s2 :
 VM.find 1 s0 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 9238 s2 = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Reset S1 S2.
 assert (Extract : VM.find 9237 s1 = Some (Gval (Fuint 1) [::false])).
 { rewrite (legal_equation_9237 invalid s0 s0 s1 S1).
   cbn [legal_expr_9237 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Reset. reflexivity. }
 rewrite (legal_equation_9238 invalid s1 s1 s2 S2).
 cbn [legal_expr_9238 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Extract. reflexivity.
Qed.
Lemma active_assumption_value env :
 generated_assume_m0_0_local env ->
 VM.find 9238 env = Some (Gval (Fuint 1) [::true]) ->
 generated_expr_true (@Eref VarOrder.T (@Eid VarOrder.T 9240)) env.
Proof.
 intros Assume Enabled. apply Assume.
 unfold generated_expr_true.
 cbn [eval_hfexpr eval_href]. rewrite Enabled. vm_compute. reflexivity.
Qed.
Lemma active_assumption_normalized_value env value :
 generated_assume_m0_0_local env ->
 VM.find 9238 env = Some (Gval (Fuint 1) [::true]) ->
 VM.find 9240 env = Some value -> normalized_bit value ->
 value = Gval (Fuint 1) [::true].
Proof.
 intros Assume Enabled Lookup Normal.
 pose proof (active_assumption_value env Assume Enabled) as TrueValue.
 unfold generated_expr_true in TrueValue.
 cbn [eval_hfexpr eval_href] in TrueValue. rewrite Lookup in TrueValue.
 destruct Normal as [bit| | |]; try destruct bit; try reflexivity; vm_compute in TrueValue; try contradiction; discriminate.
Qed.
Print Assumptions active_assumption_normalized_value.
