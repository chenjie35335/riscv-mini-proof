Require Import DataAddressDependencyRanks CheckedDependencyHistory.
From Coq Require Import List Arith Lia.
Import ListNotations.
Definition data_address_targets : list nat := [9186;9194;9202;9210;9221].
Lemma data_address_target_rank node :
 In node data_address_targets -> In (node, (80, [9182])) data_address_dependency_ranks.
Proof.
 unfold data_address_targets. intros Member.
 repeat destruct Member as [Equal|Member]; try contradiction; subst node.
 - apply (@nth_error_In _ data_address_dependency_ranks 514 (9186, (80, [9182]))). vm_compute. reflexivity.
 - apply (@nth_error_In _ data_address_dependency_ranks 515 (9194, (80, [9182]))). vm_compute. reflexivity.
 - apply (@nth_error_In _ data_address_dependency_ranks 516 (9202, (80, [9182]))). vm_compute. reflexivity.
 - apply (@nth_error_In _ data_address_dependency_ranks 517 (9210, (80, [9182]))). vm_compute. reflexivity.
 - apply (@nth_error_In _ data_address_dependency_ranks 518 (9221, (80, [9182]))). vm_compute. reflexivity.
Qed.
Theorem data_address_checked_history_targets (holds : nat -> nat -> Prop) limit :
 (forall time node dependencies, time <= limit ->
   In (node, (0, dependencies)) data_address_dependency_ranks -> holds time node) ->
 (forall time node rank dependencies,
   time < limit -> In (node, (rank, dependencies)) data_address_dependency_ranks -> 0 < rank ->
   (forall source, In source dependencies -> holds time source) -> holds (S time) node) ->
 forall time node, time <= limit -> 80 <= time -> In node data_address_targets -> holds time node.
Proof.
 intros Boundary Step time node Within Depth Target.
 exact (checked_dependency_history data_address_dependency_ranks holds limit
 data_address_dependency_ranks_checked Boundary Step time node 80 [9182]
 Within (data_address_target_rank node Target) Depth).
Qed.
Print Assumptions data_address_checked_history_targets.
