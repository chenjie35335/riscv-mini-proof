Require Import StoreOutputOffsetValues CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_output_offset_history invalid history limit start b0 b1 tail :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8004(history t)=Some(Gval(Fuint 32)(b0::b1::tail))) ->
 forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 8037(history t)=Some(Gval(Fuint 5)(store_output_offset_word b0 b1)).
Proof.
 intros Steps Source.
 assert(Low:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8031(history t)=Some(Gval(Fuint 2)[::b0;b1])).
 { intros [|t] Lo Hi;[lia|]. eapply (store_output_offset_value_8031 invalid (history t) (history t) (history(S t)) b0 b1 tail);[apply Source;lia|apply Steps;lia]. }
 assert(One:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8032(history t)=Some(Gval(Fuint 1)[::b0 && ~~b1])).
 { intros [|t] Lo Hi;[lia|]. eapply (store_output_offset_value_8032 invalid (history t) (history t) (history(S t)) b0 b1);[apply Low;lia|apply Steps;lia]. }
 assert(Two:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8034(history t)=Some(Gval(Fuint 1)[::~~b0 && b1])).
 { intros [|t] Lo Hi;[lia|]. eapply (store_output_offset_value_8034 invalid (history t) (history t) (history(S t)) b0 b1);[apply Low;lia|apply Steps;lia]. }
 assert(Three:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8036(history t)=Some(Gval(Fuint 1)[::b0 && b1])).
 { intros [|t] Lo Hi;[lia|]. eapply (store_output_offset_value_8036 invalid (history t) (history t) (history(S t)) b0 b1);[apply Low;lia|apply Steps;lia]. }
 assert(Byte:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8033(history t)=Some(Gval(Fuint 4)[::false;false;false;b0 && ~~b1])).
 { intros [|t] Lo Hi;[lia|]. eapply (store_output_offset_value_8033 invalid (history t) (history t) (history(S t)) b0 b1);[apply One;lia|apply Steps;lia]. }
 assert(Half:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8035(history t)=Some(Gval(Fuint 5)[::false;false;false;b0 && ~~b1;~~b0 && b1])).
 { intros [|t] Lo Hi;[lia|]. eapply (store_output_offset_value_8035 invalid (history t) (history t) (history(S t)) b0 b1);[apply Two;lia|apply Byte;lia|apply Steps;lia]. }
 intros [|t] Lo Hi;[lia|]. eapply (store_output_offset_value_8037 invalid (history t) (history t) (history(S t)) b0 b1);[apply Three;lia|apply Half;lia|apply Steps;lia].
Qed.
