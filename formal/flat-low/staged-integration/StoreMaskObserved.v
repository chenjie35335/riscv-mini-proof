Require Import StoreMaskValues CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory RegisterInvariants StagedRegisterHold.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_mask_register :has_register 7924 flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem store_mask_observed memory inputs k observed b0 b1 b2 b3 :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7924(top_environment observed)=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 VM.find 8018(top_environment observed)=Some(Gval(Fuint 32)(store_mask_word b0 b1 b2 b3)).
Proof.
 intros Observe Legal Mask.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Held:forall t,(t<=9259)%coq_nat ->VM.find 7924(history t)=VM.find 7924(history 0%nat)).
 { intros t. induction t as[|t IH];intro Bound;[reflexivity|].
 rewrite(staged_combinational_holds_registers _ flat_memories(history t)(history t)(history(S t))flat_statements 7924 store_mask_register(Steps t ltac:(lia))).
 apply IH;lia. }
 assert(Source:VM.find 7924(history 9255%nat)=Some(Gval(Fuint 4)[::b0;b1;b2;b3])).
 { rewrite(Held 9255%nat ltac:(vm_compute;lia)) -(Held 9259%nat ltac:(vm_compute;lia)) Last. exact Mask. }
 rewrite <-Last.
 exact(store_mask_four_steps _ (history 9255%nat)(history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)
 b0 b1 b2 b3 Source (Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia))(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
