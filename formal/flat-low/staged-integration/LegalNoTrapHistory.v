Require Import CoreSocModel ComparisonNodes LegalAssumptionNodes LegalAssumptionTransport NormalizedBit BooleanControlFacts.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma legal_normalized_and_total left right :
 normalized_bit left -> normalized_bit right ->
 exists value, eval_binop Band left right = Some value /\ normalized_bit value.
Proof.
 intros Left Right. destruct Left as [a| | |]; destruct Right as [b| | |];
 try destruct a; try destruct b.
 all: vm_compute; eexists; split; [reflexivity|first [exact (normalized_known true)|exact (normalized_known false)|exact normalized_pending|exact normalized_uninitialized|exact normalized_invalid]].
Qed.
Lemma legal_normalized_eq_false_total source :
 normalized_bit source ->
 exists value, eval_binop (Bcomp Beq) source (Gval (Fuint 1) [::false]) = Some value /\ normalized_bit value.
Proof.
 intro Normal. destruct Normal as [b| | |]; try destruct b.
 all: vm_compute; eexists; split; [reflexivity|first [exact (normalized_known true)|exact (normalized_known false)|exact normalized_pending|exact normalized_uninitialized|exact normalized_invalid]].
Qed.
Lemma legal_normalized_eq_false_true source :
 normalized_bit source ->
 eval_binop (Bcomp Beq) source (Gval (Fuint 1) [::false]) = Some (Gval (Fuint 1) [::true]) ->
 source = Gval (Fuint 1) [::false].
Proof.
 intro Normal. destruct Normal as [b| | |]; try destruct b.
 all: vm_compute; intro Result; try discriminate Result; reflexivity.
Qed.
Theorem active_assumption_no_trap_after_five invalid s0 s1 s2 s3 s4 s5 left trap :
 VM.find 9139 s1 = Some left -> normalized_bit left ->
 VM.find 45 s0 = Some trap -> normalized_bit trap ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 generated_assume_m0_0_local s5 ->
 VM.find 9238 s5 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 45 s0 = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Left NL Trap NT S1 S2 S3 S4 S5 Assume Enabled.
 destruct (legal_normalized_eq_false_total trap NT) as [right [Eq NR]].
 assert (Right : VM.find 9140 s1 = Some right).
 { rewrite (legal_equation_9140 invalid s0 s0 s1 S1).
   cbn [legal_expr_9140 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Trap. exact Eq. }
 destruct (legal_normalized_and_total left right NL NR) as [value [And NV]].
 assert (Conjunction : VM.find 9141 s2 = Some value).
 { eapply legal_value_9141; [|destruct NV; reflexivity|exact S2].
   cbn [legal_expr_9141 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right. exact And. }
 destruct (active_assumption_source_adapts_true invalid s2 s3 s4 s5 S3 S4 S5 Assume Enabled)
 as [source [Source Adapt]].
 rewrite Conjunction in Source. inversion Source; subst source.
 pose proof (normalized_adaptation_recovers_bit value true NV Adapt) as ValueTrue.
 rewrite ValueTrue in And.
 destruct (normalized_and_true_sources left right NL NR And) as [_ RightTrue].
 rewrite RightTrue in Eq.
 pose proof (legal_normalized_eq_false_true trap NT Eq) as TrapFalse.
 rewrite <- TrapFalse. exact Trap.
Qed.
Print Assumptions active_assumption_no_trap_after_five.
