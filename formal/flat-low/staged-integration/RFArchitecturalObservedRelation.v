Require Import RFArchitecturalRelation RFArchitecturalResetRelation CoreSocModel ComparisonNodes StagedObservedRegister ObservedArchitecturalRegisters StagedCircuitRegisterHold FormalLocalHistory.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Lemma rf_architectural_pair_registers pair :
 List.In pair rf_architectural_register_pairs ->
 List.In (fst pair) rf_architectural_register_ids /\ List.In (snd pair) rf_architectural_register_ids.
Proof.
 intro Member.
 assert (Check : List.forallb (fun p =>
 List.existsb (Nat.eqb (fst p)) rf_architectural_register_ids &&
 List.existsb (Nat.eqb (snd p)) rf_architectural_register_ids) rf_architectural_register_pairs = true).
 { vm_compute. reflexivity. }
 rewrite List.forallb_forall in Check. specialize (Check pair Member).
 move/andP: Check => [Left Right].
 apply List.existsb_exists in Left. apply List.existsb_exists in Right.
 destruct Left as [left [Left EqLeft]]. destruct Right as [right [Right EqRight]].
 apply Nat.eqb_eq in EqLeft. apply Nat.eqb_eq in EqRight.
 rewrite EqLeft EqRight. split; assumption.
Qed.
Theorem rf_architectural_observe_preserves memory inputs k committed env observed :
 generated_run memory inputs k = Some committed ->
 SVM.find nil committed = Some env ->
 rf_architectural_relation env ->
 generated_observe memory inputs k = Some observed ->
 rf_architectural_relation (top_environment observed).
Proof.
 intros Run Env Relation Observe.
 unfold rf_architectural_relation in Relation. unfold rf_architectural_relation. rewrite List.Forall_forall in Relation. apply List.Forall_forall.
 intros pair Member.
 destruct (Relation pair Member) as [word [Size [Dut Reference]]].
 destruct (rf_architectural_pair_registers pair Member) as [DutMember RefMember].
 destruct (rf_architectural_register_properties _ DutMember) as [DutPresent [DutTyped DutSafe]].
 destruct (rf_architectural_register_properties _ RefMember) as [RefPresent [RefTyped RefSafe]].
 destruct (rf_architectural_nonexternal _ DutMember) as [DutClock DutReset].
 pose proof (staged_observed_register_copies memory inputs k committed env observed (N.of_nat (fst pair)) DutClock DutReset DutSafe DutPresent Run Env Observe) as DCopies.
 destruct (rf_architectural_nonexternal _ RefMember) as [RefClock RefReset].
 pose proof (staged_observed_register_copies memory inputs k committed env observed (N.of_nat (snd pair)) RefClock RefReset RefSafe RefPresent Run Env Observe) as RCopies.
 rewrite Dut in DCopies. rewrite Reference in RCopies.
 unfold staged_register_lookup in DCopies, RCopies. unfold top_environment.
 destruct (SVM.find nil observed) as [seen|]; [|discriminate DCopies].
 exists word. split; [exact Size|]. split; assumption.
Qed.
Theorem rf_architectural_observe_zero memory inputs observed :
 generated_observe memory inputs 0 = Some observed ->
 rf_architectural_relation (top_environment observed).
Proof.
 intro Observe. pose proof Observe as Origin. unfold generated_observe in Origin.
 destruct (generated_run memory inputs 0) as [committed|] eqn:Run; [|discriminate Origin].
 destruct (rf_architectural_run_zero memory inputs committed Run) as [env [Env Relation]].
 exact (rf_architectural_observe_preserves memory inputs 0 committed env observed Run Env Relation Observe).
Qed.
