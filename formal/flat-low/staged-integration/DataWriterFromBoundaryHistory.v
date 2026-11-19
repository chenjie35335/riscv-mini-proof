Require Import CoreSocModel ComparisonNodes DataWriterDependencyRanks DataWriterGraphPropagation DataWriterMemoryWarmup DataWriterBoundaryRegisters DataWriterBoundaryHistory DataWriterBoundaryIncludesAddress ConcreteRegisterInitialization FormalDataReadersInvariant ConcreteMemoryRead.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem data_writer_from_boundary_history inputs path history limit values :
 (forall node width, List.In (node,width) data_writer_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 data_readers_typed (history 0%nat) ->
 VM.find (N.of_nat 9179) (history 0%nat) = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 (forall time, (time <= limit)%coq_nat -> exists bit,
 VM.find (N.of_nat 1) (history time) = Some (Gval (Fuint 1) [::bit])) ->
 (forall time, (time < limit)%coq_nat ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time node rank dependencies, (time <= limit)%coq_nat ->
 List.In (node,(rank,dependencies)) data_writer_dependency_ranks ->
 (Nat.add 81 rank <= time)%coq_nat -> writer_concrete_at (history time) node.
Proof.
 intros Initial Ports Storage Concrete Reset Steps time node rank dependencies Within Member Depth.
 assert (Shifted : writer_concrete_at (history (Nat.add 81 (Nat.sub time 81))) node).
 { eapply (data_writer_concrete_history inputs path (fun i => history (Nat.add 81 i)) (Nat.sub limit 81)).
   - intros i id deps Bound Entry.
     destruct (data_writer_rank_zero_history_concrete _ history limit Initial Reset Steps
       (Nat.add 81 i) id deps ltac:(lia) Entry) as [width [bits Lookup]].
     unfold writer_concrete_at. destruct (writer_uint_required id).
     + exists width, bits. exact Lookup.
     + exists (Fuint width), bits. exact Lookup.
   - intros i Bound.
     eapply (writer_memory_history_after_warmup inputs path history limit values).
     + intros id width AddressMember. apply Initial. apply data_writer_includes_address. exact AddressMember.
     + exact Ports.
     + exact Storage.
     + exact Concrete.
     + exact Reset.
     + exact Steps.
     + lia.
     + lia.
   - intros i Bound. cbn beta.
     replace (Nat.add 81 (S i)) with (S (Nat.add 81 i)) by lia.
     apply Steps. lia.
   - lia.
   - exact Member.
   - lia. }
 replace (Nat.add 81 (Nat.sub time 81)) with time in Shifted by lia.
 exact Shifted.
Qed.
Print Assumptions data_writer_from_boundary_history.
