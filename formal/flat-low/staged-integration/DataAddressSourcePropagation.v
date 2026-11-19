Require Import CoreSocModel ComparisonNodes DataAddressDependencyRanks DataAddressGraphPropagation CheckedDependencyHistory.
From Coq Require Import ZArith List Arith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma data_address_source_rank :
 List.In (9182%nat, (79%nat, [::37%nat])) data_address_dependency_ranks.
Proof.
 apply (@List.nth_error_In _ data_address_dependency_ranks 513 (9182%nat, (79%nat, [::37%nat]))).
 vm_compute. reflexivity.
Qed.
Theorem data_address_source_history inputs path history limit :
 (forall time node dependencies, (time <= limit)%coq_nat ->
   List.In (node, (0%nat, dependencies)) data_address_dependency_ranks -> data_address_ground_at (history time) node) ->
 (forall time, (time < limit)%coq_nat ->
   exists width bits, VM.find (N.of_nat 851) (history time) = Some (Gval (Fuint width) bits)) ->
 (forall time, (time < limit)%coq_nat ->
   formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat -> (79 <= time)%coq_nat ->
 data_address_ground_at (history time) 9182.
Proof.
 intros Boundary Typed851 Steps time Within Depth.
 eapply (checked_dependency_history data_address_dependency_ranks
   (fun time node => data_address_ground_at (history time) node) limit
   data_address_dependency_ranks_checked Boundary).
 - intros t node rank dependencies Bound Member Positive Sources.
   pose proof (data_address_dependency_transfers inputs path (history t) (history t) (history (S t))
     (Typed851 t Bound) (Steps t Bound)) as Transfers.
   rewrite List.Forall_forall in Transfers.
   exact (Transfers (node, (rank, dependencies)) Member Positive Sources).
 - exact Within.
 - exact data_address_source_rank.
 - exact Depth.
Qed.
Print Assumptions data_address_source_history.
