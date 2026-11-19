Require Import X0DependencyRanks.
From Coq Require Import List Arith Bool.
Import ListNotations.
Lemma dependency_rank_lookup_member node table rank :
 dependency_rank_lookup node table = Some rank ->
 exists dependencies, In (node, (rank, dependencies)) table.
Proof.
 induction table as [|[id [level dependencies]] rest IH]; cbn; [discriminate|].
 destruct (Nat.eqb node id) eqn:Equal.
 - apply Nat.eqb_eq in Equal. subst id. intro Found. inversion Found; subst.
   exists dependencies. left. reflexivity.
 - intro Found. destruct (IH Found) as [sources Member].
   exists sources. right. exact Member.
Qed.
Theorem dependency_ranks_valid_sound table node rank dependencies source :
 dependency_ranks_valid table = true ->
 In (node, (rank, dependencies)) table ->
 In source dependencies ->
 exists source_rank source_dependencies,
 dependency_rank_lookup source table = Some source_rank /\
 In (source, (source_rank, source_dependencies)) table /\ source_rank < rank.
Proof.
 intros Valid Member Edge.
 unfold dependency_ranks_valid in Valid. rewrite forallb_forall in Valid.
 specialize (Valid (node, (rank, dependencies)) Member). cbn in Valid.
 rewrite forallb_forall in Valid. specialize (Valid source Edge).
 destruct (dependency_rank_lookup source table) as [source_rank|] eqn:Lookup; [|discriminate Valid].
 apply Nat.ltb_lt in Valid.
 destruct (dependency_rank_lookup_member source table source_rank Lookup) as [sources SourceMember].
 exists source_rank, sources. repeat split; assumption.
Qed.
Theorem x0_dependency_edges_decrease node rank dependencies source :
 In (node, (rank, dependencies)) x0_dependency_ranks -> In source dependencies ->
 exists source_rank source_dependencies,
 dependency_rank_lookup source x0_dependency_ranks = Some source_rank /\
 In (source, (source_rank, source_dependencies)) x0_dependency_ranks /\ source_rank < rank.
Proof.
 exact (dependency_ranks_valid_sound x0_dependency_ranks node rank dependencies source x0_dependency_ranks_checked).
Qed.
Print Assumptions x0_dependency_edges_decrease.
