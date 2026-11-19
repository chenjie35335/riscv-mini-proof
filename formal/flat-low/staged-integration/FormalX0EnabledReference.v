Require Import CoreSocModel ComparisonNodes FormalReferenceX0BeforeEnabled FormalX0Enable.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem x0_enabled_reference_previous invalid (history : nat -> VM.t hvalue) (n : nat) bit :
 (19 <= n)%coq_nat ->
 (forall i, (i < n)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= n)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::bit])) ->
 generated_expr_true x0_enable (history n) ->
 VM.find 1597 (history (Nat.pred n)) = Some (Gval (Fuint 32) (zeros 32)).
Proof.
 intros Bound Steps Resets Enabled.
 apply (reference_x0_before_enabled_end invalid history n bit Bound Steps Resets).
 destruct n as [|n]; [lia|].
 exact (formal_x0_enable_valid invalid (history n) (history n) (history (S n)) (Steps n ltac:(lia)) Enabled).
Qed.
Print Assumptions x0_enabled_reference_previous.
