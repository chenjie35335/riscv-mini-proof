Require Import PipelinePCAdjacentTransfer FetchPCArithmetic FetchPCSequentialExact.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem fetch_pc_successor_low_adjacent fetch :
 size fetch = 33%nat ->
 pc_adjacent (take 32 fetch) (take 32 (fetch_pc_plus_four fetch)).
Proof.
 intro Size. split; [rewrite size_take Size; reflexivity|].
 split; [rewrite size_take fetch_pc_plus_four_size; reflexivity|].
 assert (Low : take 32 fetch = from_N 32 (to_N fetch)).
 { rewrite <- (from_N_to_N fetch) at 1. rewrite Size.
   apply fetch_pc_take_from_N. reflexivity. }
 rewrite Low fetch_pc_low32_plus_four !to_N_from_N.
 symmetry. apply N.add_mod_idemp_l. discriminate.
Qed.
Print Assumptions fetch_pc_successor_low_adjacent.
