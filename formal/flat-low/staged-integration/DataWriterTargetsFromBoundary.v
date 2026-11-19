Require Import CoreSocModel ComparisonNodes DataWriterDependencyRanks DataWriterGraphPropagation DataWriterFromBoundaryHistory DataWriterBoundaryRegisters ConcreteRegisterInitialization FormalDataReadersInvariant ConcreteMemoryRead.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Definition data_writer_targets : list nat := [::9230;9232;9233;9234].
Lemma data_writer_target_entry node : List.In node data_writer_targets ->
 exists rank deps, (rank <= 91)%coq_nat /\ List.In (node,(rank,deps)) data_writer_dependency_ranks.
Proof.
 unfold data_writer_targets. intro Member.
 repeat destruct Member as [Equal|Member]; try contradiction; subst node.
 - exists 82%nat, [::36;9225]. split; [lia|].
   apply (@List.nth_error_In _ data_writer_dependency_ranks 662 (9230,(82,[::36;9225]))). vm_compute. reflexivity.
 - exists 82%nat, [::36;9227]. split; [lia|].
   apply (@List.nth_error_In _ data_writer_dependency_ranks 663 (9232,(82,[::36;9227]))). vm_compute. reflexivity.
 - exists 82%nat, [::36;9228]. split; [lia|].
   apply (@List.nth_error_In _ data_writer_dependency_ranks 664 (9233,(82,[::36;9228]))). vm_compute. reflexivity.
 - exists 91%nat, [::36;9229]. split; [lia|].
   apply (@List.nth_error_In _ data_writer_dependency_ranks 682 (9234,(91,[::36;9229]))). vm_compute. reflexivity.
Qed.
Lemma data_writer_target_uint node : List.In node data_writer_targets -> writer_uint_required node = true.
Proof.
 unfold data_writer_targets. intro Member.
 repeat destruct Member as [Equal|Member]; try contradiction; subst node; reflexivity.
Qed.
Theorem data_writer_targets_from_boundary inputs path history limit values :
 (forall node width, List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 data_readers_typed (history 0%nat) ->
 VM.find (N.of_nat 9179) (history 0%nat) = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 (forall time, (time <= limit)%coq_nat -> exists bit,
 VM.find (N.of_nat 1) (history time) = Some (Gval (Fuint 1) [::bit])) ->
 (forall time, (time < limit)%coq_nat ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time node, (time <= limit)%coq_nat -> (172 <= time)%coq_nat ->
 List.In node data_writer_targets ->
 exists width bits, VM.find (N.of_nat node) (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Initial Ports Storage Concrete Reset Steps time node Within Depth Target.
 destruct (data_writer_target_entry node Target) as [rank [deps [Bound Member]]].
 pose proof (data_writer_from_boundary_history inputs path history limit values Initial Ports Storage Concrete Reset Steps
 time node rank deps Within Member ltac:(lia)) as Value.
 unfold writer_concrete_at in Value. rewrite (data_writer_target_uint node Target) in Value. exact Value.
Qed.
Print Assumptions data_writer_targets_from_boundary.
