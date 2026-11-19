Require Import CoreSocModel ComparisonNodes FormalDeclaredWireCheck X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalTypedNodeEquation.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_dut_output_node base index := N.of_nat (Nat.add base index).
Definition rf_dut_alias_target stage index := rf_dut_output_node (match stage with 0%nat => 1117%nat | 1%nat => 8041%nat | _ => 8166%nat end) index.
Definition rf_dut_alias_source stage index := rf_dut_output_node (match stage with 0%nat => 1053%nat | 1%nat => 819%nat | _ => 8041%nat end) index.
Definition rf_dut_alias_expression stage index := @Eref VarOrder.T (@Eid VarOrder.T (rf_dut_alias_source stage index)).
Definition rf_dut_output_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(rf_dut_alias_target 0%nat 0%nat,rf_dut_alias_expression 0%nat 0%nat);(rf_dut_alias_target 0%nat 1%nat,rf_dut_alias_expression 0%nat 1%nat);(rf_dut_alias_target 0%nat 2%nat,rf_dut_alias_expression 0%nat 2%nat);(rf_dut_alias_target 0%nat 3%nat,rf_dut_alias_expression 0%nat 3%nat);(rf_dut_alias_target 0%nat 4%nat,rf_dut_alias_expression 0%nat 4%nat);(rf_dut_alias_target 0%nat 5%nat,rf_dut_alias_expression 0%nat 5%nat);(rf_dut_alias_target 0%nat 6%nat,rf_dut_alias_expression 0%nat 6%nat);(rf_dut_alias_target 0%nat 7%nat,rf_dut_alias_expression 0%nat 7%nat);(rf_dut_alias_target 0%nat 8%nat,rf_dut_alias_expression 0%nat 8%nat);(rf_dut_alias_target 0%nat 9%nat,rf_dut_alias_expression 0%nat 9%nat);(rf_dut_alias_target 0%nat 10%nat,rf_dut_alias_expression 0%nat 10%nat);(rf_dut_alias_target 0%nat 11%nat,rf_dut_alias_expression 0%nat 11%nat);(rf_dut_alias_target 0%nat 12%nat,rf_dut_alias_expression 0%nat 12%nat);(rf_dut_alias_target 0%nat 13%nat,rf_dut_alias_expression 0%nat 13%nat);(rf_dut_alias_target 0%nat 14%nat,rf_dut_alias_expression 0%nat 14%nat);(rf_dut_alias_target 0%nat 15%nat,rf_dut_alias_expression 0%nat 15%nat);(rf_dut_alias_target 0%nat 16%nat,rf_dut_alias_expression 0%nat 16%nat);(rf_dut_alias_target 0%nat 17%nat,rf_dut_alias_expression 0%nat 17%nat);(rf_dut_alias_target 0%nat 18%nat,rf_dut_alias_expression 0%nat 18%nat);(rf_dut_alias_target 0%nat 19%nat,rf_dut_alias_expression 0%nat 19%nat);(rf_dut_alias_target 0%nat 20%nat,rf_dut_alias_expression 0%nat 20%nat);(rf_dut_alias_target 0%nat 21%nat,rf_dut_alias_expression 0%nat 21%nat);(rf_dut_alias_target 0%nat 22%nat,rf_dut_alias_expression 0%nat 22%nat);(rf_dut_alias_target 0%nat 23%nat,rf_dut_alias_expression 0%nat 23%nat);(rf_dut_alias_target 0%nat 24%nat,rf_dut_alias_expression 0%nat 24%nat);(rf_dut_alias_target 0%nat 25%nat,rf_dut_alias_expression 0%nat 25%nat);(rf_dut_alias_target 0%nat 26%nat,rf_dut_alias_expression 0%nat 26%nat);(rf_dut_alias_target 0%nat 27%nat,rf_dut_alias_expression 0%nat 27%nat);(rf_dut_alias_target 0%nat 28%nat,rf_dut_alias_expression 0%nat 28%nat);(rf_dut_alias_target 0%nat 29%nat,rf_dut_alias_expression 0%nat 29%nat);(rf_dut_alias_target 0%nat 30%nat,rf_dut_alias_expression 0%nat 30%nat);(rf_dut_alias_target 0%nat 31%nat,rf_dut_alias_expression 0%nat 31%nat);(rf_dut_alias_target 1%nat 0%nat,rf_dut_alias_expression 1%nat 0%nat);(rf_dut_alias_target 1%nat 1%nat,rf_dut_alias_expression 1%nat 1%nat);(rf_dut_alias_target 1%nat 2%nat,rf_dut_alias_expression 1%nat 2%nat);(rf_dut_alias_target 1%nat 3%nat,rf_dut_alias_expression 1%nat 3%nat);(rf_dut_alias_target 1%nat 4%nat,rf_dut_alias_expression 1%nat 4%nat);(rf_dut_alias_target 1%nat 5%nat,rf_dut_alias_expression 1%nat 5%nat);(rf_dut_alias_target 1%nat 6%nat,rf_dut_alias_expression 1%nat 6%nat);(rf_dut_alias_target 1%nat 7%nat,rf_dut_alias_expression 1%nat 7%nat);(rf_dut_alias_target 1%nat 8%nat,rf_dut_alias_expression 1%nat 8%nat);(rf_dut_alias_target 1%nat 9%nat,rf_dut_alias_expression 1%nat 9%nat);(rf_dut_alias_target 1%nat 10%nat,rf_dut_alias_expression 1%nat 10%nat);(rf_dut_alias_target 1%nat 11%nat,rf_dut_alias_expression 1%nat 11%nat);(rf_dut_alias_target 1%nat 12%nat,rf_dut_alias_expression 1%nat 12%nat);(rf_dut_alias_target 1%nat 13%nat,rf_dut_alias_expression 1%nat 13%nat);(rf_dut_alias_target 1%nat 14%nat,rf_dut_alias_expression 1%nat 14%nat);(rf_dut_alias_target 1%nat 15%nat,rf_dut_alias_expression 1%nat 15%nat);(rf_dut_alias_target 1%nat 16%nat,rf_dut_alias_expression 1%nat 16%nat);(rf_dut_alias_target 1%nat 17%nat,rf_dut_alias_expression 1%nat 17%nat);(rf_dut_alias_target 1%nat 18%nat,rf_dut_alias_expression 1%nat 18%nat);(rf_dut_alias_target 1%nat 19%nat,rf_dut_alias_expression 1%nat 19%nat);(rf_dut_alias_target 1%nat 20%nat,rf_dut_alias_expression 1%nat 20%nat);(rf_dut_alias_target 1%nat 21%nat,rf_dut_alias_expression 1%nat 21%nat);(rf_dut_alias_target 1%nat 22%nat,rf_dut_alias_expression 1%nat 22%nat);(rf_dut_alias_target 1%nat 23%nat,rf_dut_alias_expression 1%nat 23%nat);(rf_dut_alias_target 1%nat 24%nat,rf_dut_alias_expression 1%nat 24%nat);(rf_dut_alias_target 1%nat 25%nat,rf_dut_alias_expression 1%nat 25%nat);(rf_dut_alias_target 1%nat 26%nat,rf_dut_alias_expression 1%nat 26%nat);(rf_dut_alias_target 1%nat 27%nat,rf_dut_alias_expression 1%nat 27%nat);(rf_dut_alias_target 1%nat 28%nat,rf_dut_alias_expression 1%nat 28%nat);(rf_dut_alias_target 1%nat 29%nat,rf_dut_alias_expression 1%nat 29%nat);(rf_dut_alias_target 1%nat 30%nat,rf_dut_alias_expression 1%nat 30%nat);(rf_dut_alias_target 1%nat 31%nat,rf_dut_alias_expression 1%nat 31%nat);(rf_dut_alias_target 2%nat 0%nat,rf_dut_alias_expression 2%nat 0%nat);(rf_dut_alias_target 2%nat 1%nat,rf_dut_alias_expression 2%nat 1%nat);(rf_dut_alias_target 2%nat 2%nat,rf_dut_alias_expression 2%nat 2%nat);(rf_dut_alias_target 2%nat 3%nat,rf_dut_alias_expression 2%nat 3%nat);(rf_dut_alias_target 2%nat 4%nat,rf_dut_alias_expression 2%nat 4%nat);(rf_dut_alias_target 2%nat 5%nat,rf_dut_alias_expression 2%nat 5%nat);(rf_dut_alias_target 2%nat 6%nat,rf_dut_alias_expression 2%nat 6%nat);(rf_dut_alias_target 2%nat 7%nat,rf_dut_alias_expression 2%nat 7%nat);(rf_dut_alias_target 2%nat 8%nat,rf_dut_alias_expression 2%nat 8%nat);(rf_dut_alias_target 2%nat 9%nat,rf_dut_alias_expression 2%nat 9%nat);(rf_dut_alias_target 2%nat 10%nat,rf_dut_alias_expression 2%nat 10%nat);(rf_dut_alias_target 2%nat 11%nat,rf_dut_alias_expression 2%nat 11%nat);(rf_dut_alias_target 2%nat 12%nat,rf_dut_alias_expression 2%nat 12%nat);(rf_dut_alias_target 2%nat 13%nat,rf_dut_alias_expression 2%nat 13%nat);(rf_dut_alias_target 2%nat 14%nat,rf_dut_alias_expression 2%nat 14%nat);(rf_dut_alias_target 2%nat 15%nat,rf_dut_alias_expression 2%nat 15%nat);(rf_dut_alias_target 2%nat 16%nat,rf_dut_alias_expression 2%nat 16%nat);(rf_dut_alias_target 2%nat 17%nat,rf_dut_alias_expression 2%nat 17%nat);(rf_dut_alias_target 2%nat 18%nat,rf_dut_alias_expression 2%nat 18%nat);(rf_dut_alias_target 2%nat 19%nat,rf_dut_alias_expression 2%nat 19%nat);(rf_dut_alias_target 2%nat 20%nat,rf_dut_alias_expression 2%nat 20%nat);(rf_dut_alias_target 2%nat 21%nat,rf_dut_alias_expression 2%nat 21%nat);(rf_dut_alias_target 2%nat 22%nat,rf_dut_alias_expression 2%nat 22%nat);(rf_dut_alias_target 2%nat 23%nat,rf_dut_alias_expression 2%nat 23%nat);(rf_dut_alias_target 2%nat 24%nat,rf_dut_alias_expression 2%nat 24%nat);(rf_dut_alias_target 2%nat 25%nat,rf_dut_alias_expression 2%nat 25%nat);(rf_dut_alias_target 2%nat 26%nat,rf_dut_alias_expression 2%nat 26%nat);(rf_dut_alias_target 2%nat 27%nat,rf_dut_alias_expression 2%nat 27%nat);(rf_dut_alias_target 2%nat 28%nat,rf_dut_alias_expression 2%nat 28%nat);(rf_dut_alias_target 2%nat 29%nat,rf_dut_alias_expression 2%nat 29%nat);(rf_dut_alias_target 2%nat 30%nat,rf_dut_alias_expression 2%nat 30%nat);(rf_dut_alias_target 2%nat 31%nat,rf_dut_alias_expression 2%nat 31%nat)].
Definition rf_dut_output_offsets : seq nat := [::1126%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;7389%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;93%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_dut_output_positions : select_node_offsets rf_dut_output_offsets flat_statements = Some rf_dut_output_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_dut_output_safety : selected_node_safety flat_memories flat_statements rf_dut_output_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_dut_alias_member (stage index : nat) : (stage < 3)%coq_nat -> (index < 32)%coq_nat ->
 List.In (rf_dut_alias_target stage index, rf_dut_alias_expression stage index) rf_dut_output_nodes.
Proof. intros Stage Index.
 apply (List.nth_error_In rf_dut_output_nodes (Nat.add (Nat.mul 32 stage) index)).
 destruct stage as [|[|[|stage]]]; try lia.
 - destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
   lia.
 - destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
   lia.
 - destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
   lia.
Qed.
Definition rf_dut_wire_target outer index := rf_dut_output_node (if outer then 1399%nat else 819%nat) index.
Definition rf_dut_wire_source outer index := rf_dut_output_node (if outer then 8166%nat else 1117%nat) index.
Definition rf_dut_wire_position (outer : bool) (index : nat) : nat :=
 match outer,index with
| false,0%nat => 828%nat
| false,1%nat => 829%nat
| false,2%nat => 830%nat
| false,3%nat => 831%nat
| false,4%nat => 832%nat
| false,5%nat => 833%nat
| false,6%nat => 834%nat
| false,7%nat => 835%nat
| false,8%nat => 836%nat
| false,9%nat => 837%nat
| false,10%nat => 838%nat
| false,11%nat => 839%nat
| false,12%nat => 840%nat
| false,13%nat => 841%nat
| false,14%nat => 842%nat
| false,15%nat => 843%nat
| false,16%nat => 844%nat
| false,17%nat => 845%nat
| false,18%nat => 846%nat
| false,19%nat => 847%nat
| false,20%nat => 848%nat
| false,21%nat => 849%nat
| false,22%nat => 850%nat
| false,23%nat => 851%nat
| false,24%nat => 852%nat
| false,25%nat => 853%nat
| false,26%nat => 854%nat
| false,27%nat => 855%nat
| false,28%nat => 856%nat
| false,29%nat => 857%nat
| false,30%nat => 858%nat
| false,31%nat => 859%nat
| true,0%nat => 1478%nat
| true,1%nat => 1479%nat
| true,2%nat => 1480%nat
| true,3%nat => 1481%nat
| true,4%nat => 1482%nat
| true,5%nat => 1483%nat
| true,6%nat => 1484%nat
| true,7%nat => 1485%nat
| true,8%nat => 1486%nat
| true,9%nat => 1487%nat
| true,10%nat => 1488%nat
| true,11%nat => 1489%nat
| true,12%nat => 1490%nat
| true,13%nat => 1491%nat
| true,14%nat => 1492%nat
| true,15%nat => 1493%nat
| true,16%nat => 1494%nat
| true,17%nat => 1495%nat
| true,18%nat => 1496%nat
| true,19%nat => 1497%nat
| true,20%nat => 1498%nat
| true,21%nat => 1499%nat
| true,22%nat => 1500%nat
| true,23%nat => 1501%nat
| true,24%nat => 1502%nat
| true,25%nat => 1503%nat
| true,26%nat => 1504%nat
| true,27%nat => 1505%nat
| true,28%nat => 1506%nat
| true,29%nat => 1507%nat
| true,30%nat => 1508%nat
| true,31%nat => 1509%nat
| _,_ => 0%nat end.
Definition rf_dut_wire_distance (outer : bool) (index : nat) : nat :=
 match outer,index with
| false,0%nat => 331%nat
| false,1%nat => 331%nat
| false,2%nat => 331%nat
| false,3%nat => 331%nat
| false,4%nat => 331%nat
| false,5%nat => 331%nat
| false,6%nat => 331%nat
| false,7%nat => 331%nat
| false,8%nat => 331%nat
| false,9%nat => 331%nat
| false,10%nat => 331%nat
| false,11%nat => 331%nat
| false,12%nat => 331%nat
| false,13%nat => 331%nat
| false,14%nat => 331%nat
| false,15%nat => 331%nat
| false,16%nat => 331%nat
| false,17%nat => 331%nat
| false,18%nat => 331%nat
| false,19%nat => 331%nat
| false,20%nat => 331%nat
| false,21%nat => 331%nat
| false,22%nat => 331%nat
| false,23%nat => 331%nat
| false,24%nat => 331%nat
| false,25%nat => 331%nat
| false,26%nat => 331%nat
| false,27%nat => 331%nat
| false,28%nat => 331%nat
| false,29%nat => 331%nat
| false,30%nat => 331%nat
| false,31%nat => 331%nat
| true,0%nat => 7408%nat
| true,1%nat => 7408%nat
| true,2%nat => 7408%nat
| true,3%nat => 7408%nat
| true,4%nat => 7408%nat
| true,5%nat => 7408%nat
| true,6%nat => 7408%nat
| true,7%nat => 7408%nat
| true,8%nat => 7408%nat
| true,9%nat => 7408%nat
| true,10%nat => 7408%nat
| true,11%nat => 7408%nat
| true,12%nat => 7408%nat
| true,13%nat => 7408%nat
| true,14%nat => 7408%nat
| true,15%nat => 7408%nat
| true,16%nat => 7408%nat
| true,17%nat => 7408%nat
| true,18%nat => 7408%nat
| true,19%nat => 7408%nat
| true,20%nat => 7408%nat
| true,21%nat => 7408%nat
| true,22%nat => 7408%nat
| true,23%nat => 7408%nat
| true,24%nat => 7408%nat
| true,25%nat => 7408%nat
| true,26%nat => 7408%nat
| true,27%nat => 7408%nat
| true,28%nat => 7408%nat
| true,29%nat => 7408%nat
| true,30%nat => 7408%nat
| true,31%nat => 7408%nat
| _,_ => 0%nat end.
Lemma rf_dut_wire_certificate outer index : (index < 32)%coq_nat ->
 declared_wire_check flat_memories flat_statements (rf_dut_wire_position outer index) (rf_dut_wire_distance outer index)
 (rf_dut_wire_target outer index) (rf_dut_wire_source outer index) 32 = true.
Proof. intro Index. destruct outer.
 - destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
   lia.
 - destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
destruct index as [|index]. { vm_compute;reflexivity. }
   lia.
Qed.
Lemma rf_dut_output_alias_step stage index invalid old current result word :
 (stage < 3)%coq_nat -> (index < 32)%coq_nat ->
 VM.find (rf_dut_alias_source stage index) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_dut_alias_target stage index) result = Some (Gval (Fuint 32) word).
Proof.
 intros Stage Index Input Step.
 pose proof (rf_dut_alias_member stage index Stage Index) as Member.
 destruct (selected_node_safe_position flat_memories flat_statements rf_dut_output_offsets flat_statements rf_dut_output_nodes _ _ rf_dut_output_positions rf_dut_output_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rf_dut_alias_expression eval_hfexpr_validif_policy eval_href_validif_policy]. exact Input.
Qed.
Lemma rf_dut_output_wire_step outer index invalid old current result word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (rf_dut_wire_source outer index) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_dut_wire_target outer index) result = Some (Gval (Fuint 32) word).
Proof.
 intros Index Size Input Step.
 eapply (declared_wire_checked_value flat_memories flat_statements (rf_dut_wire_position outer index) (rf_dut_wire_distance outer index) (rf_dut_wire_target outer index) (rf_dut_wire_source outer index) 32);
 [apply rf_dut_wire_certificate;exact Index|exact Input| |exact Step].
 cbn [adapt_hvalue_as_type].
 assert (Take : take 32 word = word). { apply take_oversize. rewrite Size. reflexivity. }
 rewrite Take. unfold zext_to, zext. rewrite Size subnn cats0. reflexivity.
Qed.
Theorem rf_dut_output_wires index invalid state0 state1 state2 state3 state4 state5 word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (rf_dut_output_node 1053 index) state0 = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories state0 false state0 flat_statements = Some state1 ->
 formal_value_iter invalid flat_memories state1 false state1 flat_statements = Some state2 ->
 formal_value_iter invalid flat_memories state2 false state2 flat_statements = Some state3 ->
 formal_value_iter invalid flat_memories state3 false state3 flat_statements = Some state4 ->
 formal_value_iter invalid flat_memories state4 false state4 flat_statements = Some state5 ->
 VM.find (rf_dut_output_node 1399 index) state5 = Some (Gval (Fuint 32) word).
Proof.
 intros Index Size Input Step0 Step1 Step2 Step3 Step4.
 pose proof (rf_dut_output_alias_step 0 index invalid state0 state0 state1 word ltac:(lia) Index Input Step0) as Alias0.
 pose proof (rf_dut_output_wire_step false index invalid state1 state1 state2 word Index Size Alias0 Step1) as Wire0.
 pose proof (rf_dut_output_alias_step 1 index invalid state2 state2 state3 word ltac:(lia) Index Wire0 Step2) as Alias1.
 pose proof (rf_dut_output_alias_step 2 index invalid state3 state3 state4 word ltac:(lia) Index Alias1 Step3) as Alias2.
 exact (rf_dut_output_wire_step true index invalid state4 state4 state5 word Index Size Alias2 Step4).
Qed.
