Require Import CoreSocModel ComparisonNodes RFReferenceNopRelation FormalDeclaredWireCheck X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalTypedNodeEquation FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames RegisterInvariants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_exit_node (base index : nat) := N.of_nat (Nat.add base (Nat.mul 80 (Nat.pred index))).
Definition rf_exit_port index := N.of_nat (Nat.add 1787 index).
Definition rf_exit_outer index := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707))
 (@Eref VarOrder.T (@Eid VarOrder.T (rf_exit_node 3614 index)))
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (Nat.sub 2177 index)))).
Definition rf_exit_alias index := @Eref VarOrder.T (@Eid VarOrder.T (rf_exit_node 3615 index)).
Definition rf_exit_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(rf_exit_node 3615 1%nat,rf_exit_outer 1%nat);(rf_exit_node 3616 1%nat,rf_exit_alias 1%nat);(rf_exit_node 3615 2%nat,rf_exit_outer 2%nat);(rf_exit_node 3616 2%nat,rf_exit_alias 2%nat);(rf_exit_node 3615 3%nat,rf_exit_outer 3%nat);(rf_exit_node 3616 3%nat,rf_exit_alias 3%nat);(rf_exit_node 3615 4%nat,rf_exit_outer 4%nat);(rf_exit_node 3616 4%nat,rf_exit_alias 4%nat);(rf_exit_node 3615 5%nat,rf_exit_outer 5%nat);(rf_exit_node 3616 5%nat,rf_exit_alias 5%nat);(rf_exit_node 3615 6%nat,rf_exit_outer 6%nat);(rf_exit_node 3616 6%nat,rf_exit_alias 6%nat);(rf_exit_node 3615 7%nat,rf_exit_outer 7%nat);(rf_exit_node 3616 7%nat,rf_exit_alias 7%nat);(rf_exit_node 3615 8%nat,rf_exit_outer 8%nat);(rf_exit_node 3616 8%nat,rf_exit_alias 8%nat);(rf_exit_node 3615 9%nat,rf_exit_outer 9%nat);(rf_exit_node 3616 9%nat,rf_exit_alias 9%nat);(rf_exit_node 3615 10%nat,rf_exit_outer 10%nat);(rf_exit_node 3616 10%nat,rf_exit_alias 10%nat);(rf_exit_node 3615 11%nat,rf_exit_outer 11%nat);(rf_exit_node 3616 11%nat,rf_exit_alias 11%nat);(rf_exit_node 3615 12%nat,rf_exit_outer 12%nat);(rf_exit_node 3616 12%nat,rf_exit_alias 12%nat);(rf_exit_node 3615 13%nat,rf_exit_outer 13%nat);(rf_exit_node 3616 13%nat,rf_exit_alias 13%nat);(rf_exit_node 3615 14%nat,rf_exit_outer 14%nat);(rf_exit_node 3616 14%nat,rf_exit_alias 14%nat);(rf_exit_node 3615 15%nat,rf_exit_outer 15%nat);(rf_exit_node 3616 15%nat,rf_exit_alias 15%nat);(rf_exit_node 3615 16%nat,rf_exit_outer 16%nat);(rf_exit_node 3616 16%nat,rf_exit_alias 16%nat);(rf_exit_node 3615 17%nat,rf_exit_outer 17%nat);(rf_exit_node 3616 17%nat,rf_exit_alias 17%nat);(rf_exit_node 3615 18%nat,rf_exit_outer 18%nat);(rf_exit_node 3616 18%nat,rf_exit_alias 18%nat);(rf_exit_node 3615 19%nat,rf_exit_outer 19%nat);(rf_exit_node 3616 19%nat,rf_exit_alias 19%nat);(rf_exit_node 3615 20%nat,rf_exit_outer 20%nat);(rf_exit_node 3616 20%nat,rf_exit_alias 20%nat);(rf_exit_node 3615 21%nat,rf_exit_outer 21%nat);(rf_exit_node 3616 21%nat,rf_exit_alias 21%nat);(rf_exit_node 3615 22%nat,rf_exit_outer 22%nat);(rf_exit_node 3616 22%nat,rf_exit_alias 22%nat);(rf_exit_node 3615 23%nat,rf_exit_outer 23%nat);(rf_exit_node 3616 23%nat,rf_exit_alias 23%nat);(rf_exit_node 3615 24%nat,rf_exit_outer 24%nat);(rf_exit_node 3616 24%nat,rf_exit_alias 24%nat);(rf_exit_node 3615 25%nat,rf_exit_outer 25%nat);(rf_exit_node 3616 25%nat,rf_exit_alias 25%nat);(rf_exit_node 3615 26%nat,rf_exit_outer 26%nat);(rf_exit_node 3616 26%nat,rf_exit_alias 26%nat);(rf_exit_node 3615 27%nat,rf_exit_outer 27%nat);(rf_exit_node 3616 27%nat,rf_exit_alias 27%nat);(rf_exit_node 3615 28%nat,rf_exit_outer 28%nat);(rf_exit_node 3616 28%nat,rf_exit_alias 28%nat);(rf_exit_node 3615 29%nat,rf_exit_outer 29%nat);(rf_exit_node 3616 29%nat,rf_exit_alias 29%nat);(rf_exit_node 3615 30%nat,rf_exit_outer 30%nat);(rf_exit_node 3616 30%nat,rf_exit_alias 30%nat);(rf_exit_node 3615 31%nat,rf_exit_outer 31%nat);(rf_exit_node 3616 31%nat,rf_exit_alias 31%nat)].
Definition rf_exit_offsets : seq nat := [::3694%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat;78%nat;0%nat].
Lemma rf_exit_positions : select_node_offsets rf_exit_offsets flat_statements = Some rf_exit_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_exit_safety : selected_node_safety flat_memories flat_statements rf_exit_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_exit_members index : (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 List.In (rf_exit_node 3615 index, rf_exit_outer index) rf_exit_nodes /\
 List.In (rf_exit_node 3616 index, rf_exit_alias index) rf_exit_nodes.
Proof. intros Lower Upper.
 split.
 - apply (List.nth_error_In rf_exit_nodes (Nat.mul 2 (Nat.pred index))).
   destruct index as [|index]. { lia. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   lia.
 - apply (List.nth_error_In rf_exit_nodes (S (Nat.mul 2 (Nat.pred index)))).
   destruct index as [|index]. { lia. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   destruct index as [|index]. { vm_compute; reflexivity. }
   lia.
Qed.
Definition rf_exit_decl_position (index : nat) : nat := match index with
| 1%nat => 1867%nat
| 2%nat => 1868%nat
| 3%nat => 1869%nat
| 4%nat => 1870%nat
| 5%nat => 1871%nat
| 6%nat => 1872%nat
| 7%nat => 1873%nat
| 8%nat => 1874%nat
| 9%nat => 1875%nat
| 10%nat => 1876%nat
| 11%nat => 1877%nat
| 12%nat => 1878%nat
| 13%nat => 1879%nat
| 14%nat => 1880%nat
| 15%nat => 1881%nat
| 16%nat => 1882%nat
| 17%nat => 1883%nat
| 18%nat => 1884%nat
| 19%nat => 1885%nat
| 20%nat => 1886%nat
| 21%nat => 1887%nat
| 22%nat => 1888%nat
| 23%nat => 1889%nat
| 24%nat => 1890%nat
| 25%nat => 1891%nat
| 26%nat => 1892%nat
| 27%nat => 1893%nat
| 28%nat => 1894%nat
| 29%nat => 1895%nat
| 30%nat => 1896%nat
| 31%nat => 1897%nat
| _ => 0%nat end.
Definition rf_exit_connect_position (index : nat) : nat := match index with
| 1%nat => 7358%nat
| 2%nat => 7359%nat
| 3%nat => 7360%nat
| 4%nat => 7361%nat
| 5%nat => 7362%nat
| 6%nat => 7363%nat
| 7%nat => 7364%nat
| 8%nat => 7365%nat
| 9%nat => 7366%nat
| 10%nat => 7367%nat
| 11%nat => 7368%nat
| 12%nat => 7369%nat
| 13%nat => 7370%nat
| 14%nat => 7371%nat
| 15%nat => 7372%nat
| 16%nat => 7373%nat
| 17%nat => 7374%nat
| 18%nat => 7375%nat
| 19%nat => 7376%nat
| 20%nat => 7377%nat
| 21%nat => 7378%nat
| 22%nat => 7379%nat
| 23%nat => 7380%nat
| 24%nat => 7381%nat
| 25%nat => 7382%nat
| 26%nat => 7383%nat
| 27%nat => 7384%nat
| 28%nat => 7385%nat
| 29%nat => 7386%nat
| 30%nat => 7387%nat
| 31%nat => 7388%nat
| _ => 0%nat end.
Lemma rf_exit_wire_certificates index : (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 declared_wire_check flat_memories flat_statements (rf_exit_decl_position index)
 (Nat.sub (rf_exit_connect_position index) (S (rf_exit_decl_position index)))
 (rf_exit_port index) (rf_exit_node 3616 index) 32 = true.
Proof. intros Lower Upper.
destruct index as [|index]. { lia. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
destruct index as [|index]. { vm_compute; reflexivity. }
lia. Qed.
Lemma rf_exit_alias_step index invalid old current result value :
 (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 VM.find (rf_exit_node 3615 index) old = Some value ->
 (exists width word, value = Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_exit_node 3616 index) result = Some value.
Proof.
 intros Lower Upper Input [width [word Value]] Step. subst value.
 destruct (rf_exit_members index Lower Upper) as [_ Member].
 destruct (selected_node_safe_position flat_memories flat_statements rf_exit_offsets flat_statements rf_exit_nodes _ _ rf_exit_positions rf_exit_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rf_exit_alias eval_hfexpr_validif_policy eval_href_validif_policy]. exact Input.
Qed.
Lemma rf_exit_wire_step index invalid old current result word value :
 (1 <= index)%coq_nat -> (index < 32)%coq_nat -> size word = 32%nat ->
 rf_reference_word_extension word value ->
 VM.find (rf_exit_node 3616 index) old = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_exit_port index) result = Some (Gval (Fuint 32) word).
Proof.
 intros Lower Upper Size [width [Width Value]] Input Step. subst value.
 eapply (declared_wire_checked_value flat_memories flat_statements (rf_exit_decl_position index)
 (Nat.sub (rf_exit_connect_position index) (S (rf_exit_decl_position index))) (rf_exit_port index) (rf_exit_node 3616 index) 32);
 [apply rf_exit_wire_certificates;assumption|exact Input| |exact Step].
 cbn [adapt_hvalue_as_type].
 rewrite (rf_reference_word_resize word width 32 Size Width (leqnn 32)).
 unfold zext_to, zext. rewrite Size subnn cats0. reflexivity.
Qed.
Theorem rf_reference_nop_exit index invalid state0 state1 state2 state3 word value :
 (1 <= index)%coq_nat -> (index < 32)%coq_nat -> size word = 32%nat ->
 rf_reference_word_extension word value ->
 VM.find (rf_exit_node 3614 index) state0 = Some value ->
 VM.find 1707 state0 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories state0 false state0 flat_statements = Some state1 ->
 formal_value_iter invalid flat_memories state1 false state1 flat_statements = Some state2 ->
 formal_value_iter invalid flat_memories state2 false state2 flat_statements = Some state3 ->
 VM.find (rf_exit_port index) state3 = Some (Gval (Fuint 32) word).
Proof.
 intros Lower Upper Size Extension Input Enable Step0 Step1 Step2.
 destruct (rf_exit_members index Lower Upper) as [Member _].
 destruct (rf_reference_word_true_node rf_exit_offsets rf_exit_nodes (rf_exit_node 3615 index) 1707 (rf_exit_node 3614 index) (N.of_nat (Nat.sub 2177 index)) invalid state0 state0 state1 word value rf_exit_positions rf_exit_safety Member Size Extension Enable Input Step0) as [outer [Outer Extended]].
 assert (Alias : VM.find (rf_exit_node 3616 index) state2 = Some outer).
 { eapply rf_exit_alias_step; [exact Lower|exact Upper|exact Outer| |exact Step1].
   destruct Extended as [width [_ Value]]. exists width, (zext_to width word). exact Value. }
 exact (rf_exit_wire_step index invalid state2 state2 state3 word outer Lower Upper Size Extended Alias Step2).
Qed.
