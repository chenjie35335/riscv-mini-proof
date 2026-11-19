Require Import CoreSocModel ComparisonNodes DataWriterDependencyRanks DataWriterBoundaryCertificate DataWriterBoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma data_writer_boundaries_are_registers_or_reset :
 data_writer_boundary_ids = 1%nat :: List.map fst data_writer_boundary_registers.
Proof. reflexivity. Qed.
Theorem data_writer_register_history_concrete invalid history limit node width :
 List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat) ->
 (forall time, (time < limit)%coq_nat ->
 formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat -> map_uint_concrete (N.of_nat node) width (history time).
Proof.
 intros Member Initial Steps time. induction time as [|time IH]; intro Within; [exact Initial|].
 destruct (IH ltac:(lia)) as [bits [Size Lookup]].
 exists bits. split; [exact Size|].
 rewrite (data_writer_boundary_registers_comb_hold invalid (history time) (history time) (history (S time)) node width Member (Steps time ltac:(lia))).
 exact Lookup.
Qed.
Theorem data_writer_rank_zero_history_concrete invalid history limit :
 (forall node width, List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time <= limit)%coq_nat -> exists bit,
 VM.find (N.of_nat 1) (history time) = Some (Gval (Fuint 1) [::bit])) ->
 (forall time, (time < limit)%coq_nat ->
 formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time node dependencies, (time <= limit)%coq_nat ->
 List.In (node,(0%nat,dependencies)) data_writer_dependency_ranks ->
 exists width bits, VM.find (N.of_nat node) (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Initial Reset Steps time node dependencies Within Member.
 pose proof (data_writer_zero_rank_is_boundary node dependencies Member) as Boundary.
 rewrite data_writer_boundaries_are_registers_or_reset in Boundary.
 destruct Boundary as [Equal|Register].
 - subst node. destruct (Reset time Within) as [bit Lookup]. exists 1%nat, [::bit]. exact Lookup.
 - apply List.in_map_iff in Register.
   destruct Register as [[id width] [Equal Register]]. cbn [fst] in Equal. subst id.
   destruct (data_writer_register_history_concrete invalid history limit node width Register
   (Initial node width Register) Steps time Within) as [bits [_ Lookup]].
   exists width, bits. exact Lookup.
Qed.
Print Assumptions data_writer_rank_zero_history_concrete.
Theorem data_writer_register_history_same invalid history limit node width :
 List.In (node,width) data_writer_boundary_registers ->
 (forall time, (time < limit)%coq_nat ->
 formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat ->
 VM.find (N.of_nat node) (history time) = VM.find (N.of_nat node) (history 0%nat).
Proof.
 intros Member Steps time. induction time as [|time IH]; intro Within; [reflexivity|].
 rewrite (data_writer_boundary_registers_comb_hold invalid (history time) (history time) (history (S time)) node width Member (Steps time ltac:(lia))).
 apply IH. lia.
Qed.
Print Assumptions data_writer_register_history_same.
