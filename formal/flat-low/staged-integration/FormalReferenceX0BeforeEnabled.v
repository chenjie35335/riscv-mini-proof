Require Import CoreSocModel ComparisonNodes FormalCheckerValidStability FormalReferenceX0EnabledPath.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem reference_x0_before_enabled_end invalid (history : nat -> VM.t hvalue) (n : nat) bit :
 (19 <= n)%coq_nat ->
 (forall i, (i < n)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= n)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::bit])) ->
 VM.find 1395 (history n) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1597 (history (Nat.pred n)) = Some (Gval (Fuint 32) (zeros 32)).
Proof.
 intros Bound Steps Resets Enabled.
 pose proof (checker_valid_history_stable invalid history n (Nat.sub n 19) (Nat.sub n 12) bit Steps Resets ltac:(lia) ltac:(lia)) as Equal.
 replace (Nat.add (Nat.sub n 19) 12) with (Nat.sub n 7) in Equal by lia.
 replace (Nat.add (Nat.sub n 12) 12) with n in Equal by lia.
 assert (Early : VM.find 1395 (history (Nat.sub n 7)) = Some (Gval (Fuint 1) [::true])).
 { rewrite Equal. exact Enabled. }
 set (j := Nat.sub n 7).
 replace (Nat.pred n) with (S (S (S (S (S (S j)))))) by (unfold j; lia).
 eapply (formal_reference_x0_from_checker_valid invalid (history j) (history (S j)) (history (S (S j))) (history (S (S (S j)))) (history (S (S (S (S j))))) (history (S (S (S (S (S j)))))) (history (S (S (S (S (S (S j))))))));
 [exact Early| | | | | |]; apply Steps; unfold j; lia.
Qed.
Print Assumptions reference_x0_before_enabled_end.
