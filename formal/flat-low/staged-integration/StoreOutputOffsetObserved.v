Require Import StoreOutputOffsetValues StoreOutputOffsetHistory CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory RegisterInvariants StagedRegisterHold.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_output_address_register :has_register 8004 flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem store_output_offset_observed memory inputs k observed b0 b1 tail :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 8004(top_environment observed)=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 VM.find 8037(top_environment observed)=Some(Gval(Fuint 5)(store_output_offset_word b0 b1)).
Proof.
 intros Observe Legal Mask.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Held:forall t,(t<=9259)%coq_nat ->VM.find 8004(history t)=VM.find 8004(history 0%nat)).
 { intros t. induction t as[|t IH];intro Bound;[reflexivity|].
 rewrite(staged_combinational_holds_registers _ flat_memories(history t)(history t)(history(S t))flat_statements 8004 store_output_address_register(Steps t ltac:(lia))).
 apply IH;lia. }
 rewrite <-Last.
 apply(store_output_offset_history _ history 9259 0 b0 b1 tail Steps).
 - intros t Lower Upper. rewrite(Held t Upper) -(Held 9259%nat ltac:(vm_compute;lia)) Last. exact Mask.
 - vm_compute;lia.
 - lia.
Qed.
