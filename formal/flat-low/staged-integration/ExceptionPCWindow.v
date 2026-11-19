Require Import CoreSocModel ComparisonNodes ComparisonTruth FormalLocalHistory ExceptionPCPayloadHistory ExceptionPCSourceRegisters.
From Coq Require Import ZArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem exception_pc_window_agreement invalid history limit start bits :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 (Nat.add start 8 <= limit)%coq_nat ->
 size bits = 32%nat ->
 take 2 bits = [::false;false] ->
 VM.find 7751 (history limit) = Some (Gval (Fuint 32) bits) ->
 VM.find 7331 (history limit) = Some (Gval (Fuint 32) bits) ->
 (exists cw cb, VM.find 6780 (history (Nat.add start 3)) = Some (Gval (Fuint cw) cb) /\ is_zero cb = false) ->
 VM.find 1707 (history (Nat.add start 4)) = Some (Gval (Fuint 1) [::true]) ->
 comparison_inputs_agree (history (Nat.add start 8)) 1472 1670.
Proof.
 intros Steps Bound Size Low Implementation Reference Raise Valid.
 set (h := fun j => history (Nat.add start j)).
 assert (LocalSteps : forall j, (j < 8)%coq_nat -> formal_flat_local_step invalid (h j) (h (S j))).
 { intros j Small. unfold h. rewrite Nat.add_succ_r. apply Steps. lia. }
 assert (Source0 : VM.find 7751 (h 0%nat) = Some (Gval (Fuint 32) bits)).
 { unfold h. rewrite (proj1 (exception_pc_sources_history_stable invalid history limit (Nat.add start 0) Steps ltac:(lia))). exact Implementation. }
 assert (Source1 : VM.find 7331 (h 1%nat) = Some (Gval (Fuint 32) bits)).
 { unfold h. rewrite (proj2 (exception_pc_sources_history_stable invalid history limit (Nat.add start 1) Steps ltac:(lia))). exact Reference. }
 assert (Left : VM.find 1472 (h 8%nat) = Some (Gval (Fuint 32) bits)).
 { apply (implementation_exception_pc_payload_after_eight invalid (h 0%nat) (h 1%nat) (h 2%nat) (h 3%nat) (h 4%nat) (h 5%nat) (h 6%nat) (h 7%nat) (h 8%nat) bits);
   try assumption; apply LocalSteps; lia. }
 assert (Right : VM.find 1670 (h 8%nat) = Some (Gval (Fuint 32) bits)).
 { apply (reference_exception_pc_payload_after_seven invalid (h 1%nat) (h 2%nat) (h 3%nat) (h 4%nat) (h 5%nat) (h 6%nat) (h 7%nat) (h 8%nat) bits);
   try assumption; apply LocalSteps; lia. }
 exists 32%nat, 32%nat, bits, bits.
 split; [exact Left|]. split; [exact Right|reflexivity].
Qed.
Print Assumptions exception_pc_window_agreement.
