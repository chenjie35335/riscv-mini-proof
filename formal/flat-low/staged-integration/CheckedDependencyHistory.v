Require Import X0DependencyRanks DependencyRankSoundness.
From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Theorem checked_dependency_history table (holds : nat -> nat -> Prop) limit :
 dependency_ranks_valid table = true ->
 (forall time node dependencies, time <= limit -> In (node, (0, dependencies)) table -> holds time node) ->
 (forall time node rank dependencies,
   time < limit -> In (node, (rank, dependencies)) table -> 0 < rank ->
   (forall source, In source dependencies -> holds time source) -> holds (S time) node) ->
 forall time node rank dependencies,
 time <= limit -> In (node, (rank, dependencies)) table -> rank <= time -> holds time node.
Proof.
 intros Valid Boundary Step time. induction time as [|time IH]; intros node rank dependencies Within Member Depth.
 - assert (rank = 0) by lia. subst rank. exact (Boundary 0 node dependencies Within Member).
 - destruct rank as [|rank].
   + exact (Boundary (S time) node dependencies Within Member).
   + apply (Step time node (S rank) dependencies); try assumption; try lia.
     intros source Edge.
     destruct (dependency_ranks_valid_sound table node (S rank) dependencies source Valid Member Edge)
       as [source_rank [sources [Lookup [SourceMember Less]]]].
     exact (IH source source_rank sources ltac:(lia) SourceMember ltac:(lia)).
Qed.
Lemma x0_enable_rank_entry : In (784, (44, [7941])) x0_dependency_ranks.
Proof. unfold x0_dependency_ranks. repeat first [left; reflexivity | right]. Qed.
Lemma x0_address_rank_entry : In (785, (2, [7805])) x0_dependency_ranks.
Proof. unfold x0_dependency_ranks. repeat first [left; reflexivity | right]. Qed.
Corollary x0_checked_history_targets (holds : nat -> nat -> Prop) limit :
 (forall time node dependencies, time <= limit -> In (node, (0, dependencies)) x0_dependency_ranks -> holds time node) ->
 (forall time node rank dependencies,
   time < limit -> In (node, (rank, dependencies)) x0_dependency_ranks -> 0 < rank ->
   (forall source, In source dependencies -> holds time source) -> holds (S time) node) ->
 forall time, time <= limit -> 44 <= time -> holds time 784 /\ holds time 785.
Proof.
 intros Boundary Step time Within Depth. split.
 - exact (checked_dependency_history x0_dependency_ranks holds limit x0_dependency_ranks_checked Boundary Step
   time 784 44 [7941] Within x0_enable_rank_entry Depth).
 - exact (checked_dependency_history x0_dependency_ranks holds limit x0_dependency_ranks_checked Boundary Step
   time 785 2 [7805] Within x0_address_rank_entry ltac:(lia)).
Qed.
Print Assumptions x0_checked_history_targets.
