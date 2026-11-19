Require Import ReferenceEventSpine ReferenceEventConditions ReferenceEventSpineTypes SelectedZeroMux ReferenceRedirectSpine CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition reference_event_node_needed (g:VarOrder.T->bool)(node:VarOrder.T):Prop :=
 match node with
 | 6323 => g 2357=true
 | 6354 => g 2010=true
 | 6704 => False
 | 6705 => False
 | 6706 => False
 | 6376 => g 2004=true /\g 2912=true
 | 6380 => g 2004=true
 | 6400 => g 1998=true /\g 2892=true
 | 6404 => g 1998=true
 | 6424 => g 1992=true /\g 2872=true
 | 6428 => g 1992=true
 | 6448 => g 1986=true /\g 2850=true
 | 6452 => g 1986=true
 | 6472 => g 1980=true /\g 2830=true
 | 6476 => g 1980=true
 | 6496 => g 1974=true /\g 2806=true
 | 6500 => g 1974=true
 | 6523 => g 1970=true
 | 6548 => g 1966=true
 | 6573 => g 1962=true
 | 6589 => g 1958=true
 | 6614 => g 1886=true
 | 6630 => g 1951=true
 | 6663 => g 1946=true
 | 6687 => g 1941=true
 | _ => True
 end.
Definition reference_event_selected_guard i :VarOrder.T := nth 1707 [::2966;2357;2949;2010;2929;2912;2004;2909;2892;1998;2889;2872;1992;2867;2850;1986;2847;2830;1980;2825;2806;1974;2679;1970;2664;1966;2649;1962;2634;1958;2565;1886;2736;1951;2723;1946;2708;1941;1937;2751;2750;2748;1933;3042;1707;1707] i.
Theorem reference_event_selected_zero_history g invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 reference_event_safe g ->
 (forall i t,(i<45)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->
 reference_event_node_needed g(reference_event_spine_node i) ->
 VM.find(reference_event_selected_guard i)(history t)=Some(Gval(Fuint 1)[::g(reference_event_selected_guard i)])) ->
 forall t,(Nat.add start 46<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 6780(history t)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Steps Safe Guards.
 unfold reference_event_safe in Safe.
 assert(Z6323:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 2357=true) ->exists width,VM.find 6323(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 0%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2966(history t)=Some(Gval(Fuint 1)[::g 2966]))in Guard.
 destruct(g 2966)eqn:G.
 - assert(Zero:Some(Gval(Fuint 1)[::false])=Some(Gval(Fuint 1)(zeros 1)))by reflexivity.
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6323 _ _ _ invalid(history t)(history(S t))true 1);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 0%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6332:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6332(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 1%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2357(history t)=Some(Gval(Fuint 1)[::g 2357]))in Guard.
 destruct(g 2357)eqn:G.
 - destruct(Z6323 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6332 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 1%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - assert(Zero:Some(Gval(Fuint 1)[::false])=Some(Gval(Fuint 1)(zeros 1)))by reflexivity.
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6332 _ _ _ invalid(history t)(history(S t))false 1);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 1%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6354:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 2010=true) ->exists width,VM.find 6354(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 2%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2949(history t)=Some(Gval(Fuint 1)[::g 2949]))in Guard.
 destruct(g 2949)eqn:G.
 - destruct(Z6332 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6354 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 2%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6366:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6366(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 3%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2010(history t)=Some(Gval(Fuint 1)[::g 2010]))in Guard.
 destruct(g 2010)eqn:G.
 - destruct(Z6354 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6366 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 3%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6332 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6366 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 3%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6376:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 2004=true /\g 2912=true) ->exists width,VM.find 6376(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 4%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2929(history t)=Some(Gval(Fuint 1)[::g 2929]))in Guard.
 destruct(g 2929)eqn:G.
 - destruct(Z6366 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6376 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 4%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6380:forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 2004=true) ->exists width,VM.find 6380(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 5%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2912(history t)=Some(Gval(Fuint 1)[::g 2912]))in Guard.
 destruct(g 2912)eqn:G.
 - destruct(Z6376 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6380 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 5%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6366 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6380 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 5%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6390:forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6390(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 6%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2004(history t)=Some(Gval(Fuint 1)[::g 2004]))in Guard.
 destruct(g 2004)eqn:G.
 - destruct(Z6380 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6390 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 6%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6366 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6390 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 6%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6400:forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1998=true /\g 2892=true) ->exists width,VM.find 6400(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 7%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2909(history t)=Some(Gval(Fuint 1)[::g 2909]))in Guard.
 destruct(g 2909)eqn:G.
 - destruct(Z6390 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6400 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 7%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6404:forall t,(Nat.add start 9<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1998=true) ->exists width,VM.find 6404(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 8%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2892(history t)=Some(Gval(Fuint 1)[::g 2892]))in Guard.
 destruct(g 2892)eqn:G.
 - destruct(Z6400 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6404 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 8%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6390 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6404 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 8%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6414:forall t,(Nat.add start 10<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6414(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 9%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1998(history t)=Some(Gval(Fuint 1)[::g 1998]))in Guard.
 destruct(g 1998)eqn:G.
 - destruct(Z6404 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6414 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 9%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6390 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6414 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 9%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6424:forall t,(Nat.add start 11<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1992=true /\g 2872=true) ->exists width,VM.find 6424(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 10%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2889(history t)=Some(Gval(Fuint 1)[::g 2889]))in Guard.
 destruct(g 2889)eqn:G.
 - destruct(Z6414 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6424 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 10%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6428:forall t,(Nat.add start 12<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1992=true) ->exists width,VM.find 6428(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 11%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2872(history t)=Some(Gval(Fuint 1)[::g 2872]))in Guard.
 destruct(g 2872)eqn:G.
 - destruct(Z6424 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6428 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 11%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6414 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6428 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 11%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6438:forall t,(Nat.add start 13<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6438(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 12%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1992(history t)=Some(Gval(Fuint 1)[::g 1992]))in Guard.
 destruct(g 1992)eqn:G.
 - destruct(Z6428 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6438 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 12%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6414 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6438 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 12%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6448:forall t,(Nat.add start 14<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1986=true /\g 2850=true) ->exists width,VM.find 6448(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 13%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2867(history t)=Some(Gval(Fuint 1)[::g 2867]))in Guard.
 destruct(g 2867)eqn:G.
 - destruct(Z6438 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6448 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 13%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6452:forall t,(Nat.add start 15<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1986=true) ->exists width,VM.find 6452(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 14%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2850(history t)=Some(Gval(Fuint 1)[::g 2850]))in Guard.
 destruct(g 2850)eqn:G.
 - destruct(Z6448 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6452 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 14%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6438 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6452 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 14%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6462:forall t,(Nat.add start 16<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6462(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 15%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1986(history t)=Some(Gval(Fuint 1)[::g 1986]))in Guard.
 destruct(g 1986)eqn:G.
 - destruct(Z6452 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6462 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 15%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6438 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6462 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 15%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6472:forall t,(Nat.add start 17<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1980=true /\g 2830=true) ->exists width,VM.find 6472(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 16%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2847(history t)=Some(Gval(Fuint 1)[::g 2847]))in Guard.
 destruct(g 2847)eqn:G.
 - destruct(Z6462 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6472 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 16%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6476:forall t,(Nat.add start 18<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1980=true) ->exists width,VM.find 6476(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 17%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2830(history t)=Some(Gval(Fuint 1)[::g 2830]))in Guard.
 destruct(g 2830)eqn:G.
 - destruct(Z6472 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6476 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 17%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6462 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6476 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 17%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6486:forall t,(Nat.add start 19<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6486(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 18%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1980(history t)=Some(Gval(Fuint 1)[::g 1980]))in Guard.
 destruct(g 1980)eqn:G.
 - destruct(Z6476 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6486 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 18%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6462 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6486 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 18%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6496:forall t,(Nat.add start 20<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1974=true /\g 2806=true) ->exists width,VM.find 6496(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 19%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2825(history t)=Some(Gval(Fuint 1)[::g 2825]))in Guard.
 destruct(g 2825)eqn:G.
 - destruct(Z6486 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6496 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 19%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6500:forall t,(Nat.add start 21<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1974=true) ->exists width,VM.find 6500(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 20%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2806(history t)=Some(Gval(Fuint 1)[::g 2806]))in Guard.
 destruct(g 2806)eqn:G.
 - destruct(Z6496 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6500 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 20%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6486 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6500 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 20%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6510:forall t,(Nat.add start 22<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6510(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 21%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1974(history t)=Some(Gval(Fuint 1)[::g 1974]))in Guard.
 destruct(g 1974)eqn:G.
 - destruct(Z6500 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6510 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 21%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6486 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6510 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 21%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6523:forall t,(Nat.add start 23<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1970=true) ->exists width,VM.find 6523(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 22%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2679(history t)=Some(Gval(Fuint 1)[::g 2679]))in Guard.
 destruct(g 2679)eqn:G.
 - destruct(Z6510 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6523 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 22%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6533:forall t,(Nat.add start 24<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6533(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 23%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1970(history t)=Some(Gval(Fuint 1)[::g 1970]))in Guard.
 destruct(g 1970)eqn:G.
 - destruct(Z6523 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6533 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 23%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6510 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6533 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 23%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6548:forall t,(Nat.add start 25<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1966=true) ->exists width,VM.find 6548(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 24%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2664(history t)=Some(Gval(Fuint 1)[::g 2664]))in Guard.
 destruct(g 2664)eqn:G.
 - destruct(Z6533 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6548 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 24%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6557:forall t,(Nat.add start 26<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6557(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 25%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1966(history t)=Some(Gval(Fuint 1)[::g 1966]))in Guard.
 destruct(g 1966)eqn:G.
 - destruct(Z6548 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6557 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 25%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6533 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6557 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 25%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6573:forall t,(Nat.add start 27<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1962=true) ->exists width,VM.find 6573(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 26%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2649(history t)=Some(Gval(Fuint 1)[::g 2649]))in Guard.
 destruct(g 2649)eqn:G.
 - destruct(Z6557 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6573 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 26%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6582:forall t,(Nat.add start 28<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6582(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 27%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1962(history t)=Some(Gval(Fuint 1)[::g 1962]))in Guard.
 destruct(g 1962)eqn:G.
 - destruct(Z6573 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6582 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 27%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6557 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6582 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 27%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6589:forall t,(Nat.add start 29<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1958=true) ->exists width,VM.find 6589(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 28%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2634(history t)=Some(Gval(Fuint 1)[::g 2634]))in Guard.
 destruct(g 2634)eqn:G.
 - exfalso;intuition congruence.
 - destruct(Z6582 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6589 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 28%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6595:forall t,(Nat.add start 30<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6595(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 29%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1958(history t)=Some(Gval(Fuint 1)[::g 1958]))in Guard.
 destruct(g 1958)eqn:G.
 - destruct(Z6589 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6595 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 29%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6582 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6595 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 29%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6614:forall t,(Nat.add start 31<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1886=true) ->exists width,VM.find 6614(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 30%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2565(history t)=Some(Gval(Fuint 1)[::g 2565]))in Guard.
 destruct(g 2565)eqn:G.
 - destruct(Z6595 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6614 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 30%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6623:forall t,(Nat.add start 32<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6623(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 31%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1886(history t)=Some(Gval(Fuint 1)[::g 1886]))in Guard.
 destruct(g 1886)eqn:G.
 - destruct(Z6614 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6623 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 31%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6595 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6623 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 31%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6630:forall t,(Nat.add start 33<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1951=true) ->exists width,VM.find 6630(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 32%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2736(history t)=Some(Gval(Fuint 1)[::g 2736]))in Guard.
 destruct(g 2736)eqn:G.
 - exfalso;intuition congruence.
 - destruct(Z6623 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6630 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 32%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6640:forall t,(Nat.add start 34<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6640(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 33%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1951(history t)=Some(Gval(Fuint 1)[::g 1951]))in Guard.
 destruct(g 1951)eqn:G.
 - destruct(Z6630 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6640 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 33%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6623 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6640 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 33%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6663:forall t,(Nat.add start 35<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1946=true) ->exists width,VM.find 6663(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 34%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2723(history t)=Some(Gval(Fuint 1)[::g 2723]))in Guard.
 destruct(g 2723)eqn:G.
 - destruct(Z6640 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6663 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 34%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6672:forall t,(Nat.add start 36<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6672(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 35%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1946(history t)=Some(Gval(Fuint 1)[::g 1946]))in Guard.
 destruct(g 1946)eqn:G.
 - destruct(Z6663 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6672 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 35%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6640 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6672 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 35%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6687:forall t,(Nat.add start 37<=t)%coq_nat ->(t<=limit)%coq_nat ->(g 1941=true) ->exists width,VM.find 6687(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 36%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 2708(history t)=Some(Gval(Fuint 1)[::g 2708]))in Guard.
 destruct(g 2708)eqn:G.
 - destruct(Z6672 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6687 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 36%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - exfalso;intuition congruence.
 }
 assert(Z6696:forall t,(Nat.add start 38<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6696(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 37%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1941(history t)=Some(Gval(Fuint 1)[::g 1941]))in Guard.
 destruct(g 1941)eqn:G.
 - destruct(Z6687 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6696 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 37%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6672 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6696 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 37%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6701:forall t,(Nat.add start 39<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6701(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 38%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1937(history t)=Some(Gval(Fuint 1)[::g 1937]))in Guard.
 destruct(g 1937)eqn:G.
 - exfalso;intuition congruence.
 - destruct(Z6696 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6701 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 38%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6704:forall t,(Nat.add start 40<=t)%coq_nat ->(t<=limit)%coq_nat ->(False) ->exists width,VM.find 6704(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 }
 assert(Z6705:forall t,(Nat.add start 41<=t)%coq_nat ->(t<=limit)%coq_nat ->(False) ->exists width,VM.find 6705(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 }
 assert(Z6706:forall t,(Nat.add start 42<=t)%coq_nat ->(t<=limit)%coq_nat ->(False) ->exists width,VM.find 6706(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 }
 assert(Z6709:forall t,(Nat.add start 43<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6709(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 42%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1933(history t)=Some(Gval(Fuint 1)[::g 1933]))in Guard.
 destruct(g 1933)eqn:G.
 - destruct(Z6706 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6709 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 42%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - destruct(Z6701 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6709 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 42%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6778:forall t,(Nat.add start 44<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6778(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 43%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 3042(history t)=Some(Gval(Fuint 1)[::g 3042]))in Guard.
 destruct(g 3042)eqn:G.
 - exfalso;intuition congruence.
 - destruct(Z6709 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6778 _ _ _ invalid(history t)(history(S t))false width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 43%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6779:forall t,(Nat.add start 45<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6779(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 pose proof(Guards 44%nat t ltac:(lia)ltac:(lia)ltac:(lia) Active)as Guard.
 change(VM.find 1707(history t)=Some(Gval(Fuint 1)[::g 1707]))in Guard.
 destruct(g 1707)eqn:G.
 - destruct(Z6778 t ltac:(lia)ltac:(lia)ltac:(intuition congruence))as[width Zero].
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6779 _ _ _ invalid(history t)(history(S t))true width);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 44%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 - assert(Zero:Some(Gval(Fuint 1)[::false])=Some(Gval(Fuint 1)(zeros 1)))by reflexivity.
   eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6779 _ _ _ invalid(history t)(history(S t))false 1);
   [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 44%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;exact Zero|apply Steps;lia].
 }
 assert(Z6780:forall t,(Nat.add start 46<=t)%coq_nat ->(t<=limit)%coq_nat ->(True) ->exists width,VM.find 6780(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper Active;try lia.
 destruct(Z6779 t ltac:(lia)ltac:(lia) I)as[width Zero]. exists width.
 eapply(reference_redirect_ground_step reference_event_offsets reference_event_nodes 6780 (@Eref VarOrder.T (@Eid VarOrder.T 6779)));[exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 45%nat);vm_compute;reflexivity|intros site;exact Zero|apply Steps;lia]. }
 intros t Lower Upper.
 destruct(Z6780 t Lower Upper I)as[width Zero].
 destruct(reference_event_spine_types_history invalid history limit start Steps 45%nat ltac:(lia)t Lower Upper)as[value[Value Typed]].
 change(VM.find 6780(history t)=Some value)in Value.
 rewrite Zero in Value;inversion Value;subst value.
 change(Gtyp(Fuint width)=Gtyp(Fuint 1))in Typed.
 inversion Typed;subst width;exact Zero.
Qed.
