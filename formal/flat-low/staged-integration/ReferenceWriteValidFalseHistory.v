Require Import ReferenceWriteValidFalse ReferenceWriteValidShapes ReferenceRequestSpine CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_write_false_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 1951(history t)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 1946(history t)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 1941(history t)=Some(Gval(Fuint 1)[::false]) /\
 exists enabled,VM.find 1707(history t)=Some(Gval(Fuint 1)[::enabled])) ->
 forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 7113(history t)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Steps Guards.
 assert(V0:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6641(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t] Lower Upper;[lia|]. apply(reference_write_false_6641 invalid (history t)(history t)(history(S t))). apply Steps;lia. }
 assert(V1:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6642(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t] Lower Upper;[lia|]. destruct(Guards t ltac:(lia)ltac:(lia))as[G1 Rest].
   exact(reference_write_false_6642 invalid (history t)(history t)(history(S t))G1(V0 t ltac:(lia)ltac:(lia))(Steps t ltac:(lia))). }
 assert(T2:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 6659(history t)=Some value /\type_of_val value=Gtyp(Fuint 1)).
 { intros[|t] Lower Upper;[lia|]. exact(reference_write_alignment_6659_type invalid (history t)(history t)(history(S t))(V1 t ltac:(lia)ltac:(lia))(Steps t ltac:(lia))). }
 assert(V3:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6668(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t] Lower Upper;[lia|]. destruct(Guards t ltac:(lia)ltac:(lia))as[G1[G2 Rest]].
   destruct(T2 t ltac:(lia)ltac:(lia))as[value[Value Typed]].
   exact(reference_write_false_6668 invalid (history t)(history t)(history(S t))value G2 Value Typed(V1 t ltac:(lia)ltac:(lia))(Steps t ltac:(lia))). }
 assert(T4:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 6683(history t)=Some value /\type_of_val value=Gtyp(Fuint 1)).
 { intros[|t] Lower Upper;[lia|]. exact(reference_write_alignment_6683_type invalid (history t)(history t)(history(S t))(V3 t ltac:(lia)ltac:(lia))(Steps t ltac:(lia))). }
 assert(V5:forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6692(history t)=Some(Gval(Fuint 1)[::false])).
 { intros[|t] Lower Upper;[lia|]. destruct(Guards t ltac:(lia)ltac:(lia))as[G1[G2[G3 Rest]]].
   destruct(T4 t ltac:(lia)ltac:(lia))as[value[Value Typed]].
   exact(reference_write_false_6692 invalid (history t)(history t)(history(S t))value G3 Value Typed(V3 t ltac:(lia)ltac:(lia))(Steps t ltac:(lia))). }
 intros[|t] Lower Upper;[lia|]. destruct(Guards t ltac:(lia)ltac:(lia))as[G1[G2[G3[enabled Enabled]]]].
 exact(reference_write_false_7113 invalid (history t)(history t)(history(S t))enabled Enabled(V5 t ltac:(lia)ltac:(lia))(V0 t ltac:(lia)ltac:(lia))(Steps t ltac:(lia))).
Qed.
