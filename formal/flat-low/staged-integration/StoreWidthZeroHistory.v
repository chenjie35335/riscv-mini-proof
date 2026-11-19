Require Import StoreWidthSelectZero StoreWriteCompareZero MemoryRequestWidth CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_width_zero_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7765(history t)=Some(Gval(Fuint 1)[::false])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists previous,VM.find 7754(history t)=Some previous /\type_of_val previous=Gtyp(Fuint 2)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 91(history t)=Some(Gval(Fuint 2)(from_N 2 0))) ->
 forall t,(Nat.add start 13<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8002(history t)=Some(Gval(Fuint 6)(from_N 6 0)).
Proof.
 intros Steps Stall Previous Decode t Lower Upper.
 assert(Selected:forall u,(S start<=u)%coq_nat ->(u<=limit)%coq_nat ->VM.find 7996(history u)=Some(Gval(Fuint 2)(from_N 2 0))).
 { intros [|u] Low High;[lia|].
   destruct(Previous u ltac:(lia)ltac:(lia))as[previous[Value Typed]].
   exact(store_width_select_zero invalid (history u)(history u)(history(S u))previous
    (Stall u ltac:(lia)ltac:(lia))Value Typed(Decode u ltac:(lia)ltac:(lia))(Steps u ltac:(lia))). }
 pose proof(memory_width_decoder_history true 0%nat invalid
   (fun i=>history(Nat.add(S start)i)) (Nat.sub limit(S start)) ltac:(vm_compute;lia))as Width.
 assert(ShiftSteps:forall i,(i<Nat.sub limit(S start))%coq_nat ->formal_value_iter invalid flat_memories(history(Nat.add(S start)i))false(history(Nat.add(S start)i))flat_statements=Some(history(Nat.add(S start)(S i)))).
 { intros i Bound. replace(Nat.add(S start)(S i))with(S(Nat.add(S start)i))by lia. apply Steps;lia. }
 specialize(Width ShiftSteps ltac:(intros i Bound;apply Selected;lia)
 (Nat.sub t(S start)) ltac:(lia) ltac:(lia)).
 cbv beta in Width.
 replace(Nat.add(S start)(Nat.sub t(S start)))with t in Width by lia.
 exact Width.
Qed.
