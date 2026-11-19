Require Import FormalPCDecodeNodeCertificates PCDecodeExpressionValues FormalPCDecodeInputConnections FormalPCDecodeConnections CoreSocModel ComparisonNodes FormalLocalHistory.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem fetch_pc_decode_history_same invalid history (n : nat) :
 (forall i, (i < n)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 (forall t u, (t <= n)%coq_nat -> (u <= n)%coq_nat -> exists word,
 VM.find 7748 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 7748 (history u) = Some (Gval (Fuint 32) word)) ->
 forall t u, (55 <= t)%coq_nat -> (55 <= u)%coq_nat -> (t <= n)%coq_nat -> (u <= n)%coq_nat ->
 exists word, VM.find 84 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 84 (history u) = Some (Gval (Fuint 2) word).
Proof.
 intros Steps V7748.
 assert (V83 : forall t u, (Nat.le 1 t /\ Nat.le t n) -> (Nat.le 1 u /\ Nat.le u n) -> exists word, VM.find 83 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 83 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V7748 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   eexists. split; eapply decode_input_connection_83; [exact Source0|reflexivity|apply Steps;lia|exact Other0|reflexivity|apply Steps;lia].
 }
 assert (V8249 : forall t u, (Nat.le 2 t /\ Nat.le t n) -> (Nat.le 2 u /\ Nat.le u n) -> exists word, VM.find 8249 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8249 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V83 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   eexists. split; eapply decode_input_connection_8249; [exact Source0|reflexivity|apply Steps;lia|exact Other0|reflexivity|apply Steps;lia].
 }
 assert (V8263 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8263 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8263 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8263 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8263 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8263 (history t) (history t)).
   { cbn [decode_expr_8263 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8263 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8263 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8265 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8265 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8265 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8265 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8265 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8265 (history t) (history t)).
   { cbn [decode_expr_8265 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8265 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8265 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8267 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8267 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8267 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8267 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8267 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8267 (history t) (history t)).
   { cbn [decode_expr_8267 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8267 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8267 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8269 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8269 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8269 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8269 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8269 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8269 (history t) (history t)).
   { cbn [decode_expr_8269 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8269 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8269 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8271 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8271 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8271 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8271 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8271 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8271 (history t) (history t)).
   { cbn [decode_expr_8271 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8271 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8271 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8273 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8273 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8273 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8273 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8273 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8273 (history t) (history t)).
   { cbn [decode_expr_8273 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8273 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8273 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8275 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8275 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8275 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8275 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8275 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8275 (history t) (history t)).
   { cbn [decode_expr_8275 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8275 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8275 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8277 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8277 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8277 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8277 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8277 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8277 (history t) (history t)).
   { cbn [decode_expr_8277 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8277 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8277 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8279 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8279 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8279 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8279 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8279 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8279 (history t) (history t)).
   { cbn [decode_expr_8279 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8279 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8279 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8281 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8281 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8281 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8281 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8281 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8281 (history t) (history t)).
   { cbn [decode_expr_8281 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8281 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8281 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8283 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8283 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8283 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8283 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8283 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8283 (history t) (history t)).
   { cbn [decode_expr_8283 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8283 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8283 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8285 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8285 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8285 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8285 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8285 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8285 (history t) (history t)).
   { cbn [decode_expr_8285 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8285 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8285 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8287 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8287 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8287 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8287 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8287 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8287 (history t) (history t)).
   { cbn [decode_expr_8287 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8287 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8287 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8289 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8289 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8289 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8289 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8289 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8289 (history t) (history t)).
   { cbn [decode_expr_8289 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8289 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8289 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8291 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8291 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8291 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8291 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8291 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8291 (history t) (history t)).
   { cbn [decode_expr_8291 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8291 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8291 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8293 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8293 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8293 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8293 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8293 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8293 (history t) (history t)).
   { cbn [decode_expr_8293 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8293 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8293 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8297 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8297 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8297 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8297 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8297 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8297 (history t) (history t)).
   { cbn [decode_expr_8297 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8297 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8297 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8299 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8299 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8299 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8299 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8299 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8299 (history t) (history t)).
   { cbn [decode_expr_8299 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8299 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8299 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8295 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8295 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8295 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8295 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8295 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8295 (history t) (history t)).
   { cbn [decode_expr_8295 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8295 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8295 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8301 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8301 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8301 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8301 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8301 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8301 (history t) (history t)).
   { cbn [decode_expr_8301 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8301 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8301 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8305 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8305 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8305 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8305 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8305 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8305 (history t) (history t)).
   { cbn [decode_expr_8305 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8305 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8305 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8303 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8303 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8303 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8303 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8303 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8303 (history t) (history t)).
   { cbn [decode_expr_8303 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8303 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8303 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8309 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8309 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8309 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8309 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8309 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8309 (history t) (history t)).
   { cbn [decode_expr_8309 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8309 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8309 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8307 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8307 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8307 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8307 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8307 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8307 (history t) (history t)).
   { cbn [decode_expr_8307 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8307 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8307 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8311 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8311 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8311 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8311 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8311 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8311 (history t) (history t)).
   { cbn [decode_expr_8311 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8311 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8311 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8313 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8313 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8313 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8313 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8313 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8313 (history t) (history t)).
   { cbn [decode_expr_8313 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8313 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8313 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8315 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8315 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8315 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8315 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8315 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8315 (history t) (history t)).
   { cbn [decode_expr_8315 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8315 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8315 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8317 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8317 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8317 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8317 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8317 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8317 (history t) (history t)).
   { cbn [decode_expr_8317 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8317 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8317 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8319 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8319 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8319 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8319 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8319 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8319 (history t) (history t)).
   { cbn [decode_expr_8319 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8319 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8319 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8321 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8321 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8321 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8321 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8321 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8321 (history t) (history t)).
   { cbn [decode_expr_8321 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8321 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8321 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8323 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8323 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8323 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8323 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8323 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8323 (history t) (history t)).
   { cbn [decode_expr_8323 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8323 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8323 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8325 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8325 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8325 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8325 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8325 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8325 (history t) (history t)).
   { cbn [decode_expr_8325 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8325 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8325 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8327 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8327 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8327 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8327 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8327 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8327 (history t) (history t)).
   { cbn [decode_expr_8327 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8327 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8327 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8329 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8329 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8329 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8329 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8329 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8329 (history t) (history t)).
   { cbn [decode_expr_8329 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8329 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8329 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8331 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8331 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8331 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8331 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8331 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8331 (history t) (history t)).
   { cbn [decode_expr_8331 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8331 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8331 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8333 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8333 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8333 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8333 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8333 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8333 (history t) (history t)).
   { cbn [decode_expr_8333 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8333 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8333 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8335 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8335 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8335 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8335 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8335 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8335 (history t) (history t)).
   { cbn [decode_expr_8335 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8335 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8335 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8337 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8337 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8337 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8337 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8337 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8337 (history t) (history t)).
   { cbn [decode_expr_8337 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8337 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8337 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8339 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8339 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8339 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8339 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8339 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8339 (history t) (history t)).
   { cbn [decode_expr_8339 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8339 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8339 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8341 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8341 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8341 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8341 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8341 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8341 (history t) (history t)).
   { cbn [decode_expr_8341 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8341 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8341 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8343 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8343 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8343 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8343 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8343 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8343 (history t) (history t)).
   { cbn [decode_expr_8343 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8343 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8343 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8345 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8345 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8345 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8345 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8345 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8345 (history t) (history t)).
   { cbn [decode_expr_8345 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8345 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8345 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8347 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8347 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8347 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8347 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8347 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8347 (history t) (history t)).
   { cbn [decode_expr_8347 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8347 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8347 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8349 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8349 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8349 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8349 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8349 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8349 (history t) (history t)).
   { cbn [decode_expr_8349 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8349 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8349 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8351 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8351 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8351 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8351 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8351 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8351 (history t) (history t)).
   { cbn [decode_expr_8351 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8351 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8351 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8353 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8353 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8353 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8353 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8353 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8353 (history t) (history t)).
   { cbn [decode_expr_8353 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8353 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8353 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8355 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8355 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8355 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8355 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8355 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8355 (history t) (history t)).
   { cbn [decode_expr_8355 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8355 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8355 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8357 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8357 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8357 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8357 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8357 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8357 (history t) (history t)).
   { cbn [decode_expr_8357 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8357 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8357 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8359 : forall t u, (Nat.le 3 t /\ Nat.le t n) -> (Nat.le 3 u /\ Nat.le u n) -> exists word, VM.find 8359 (history t) = Some (Gval (Fuint 32) word) /\ VM.find 8359 (history u) = Some (Gval (Fuint 32) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8249 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8359 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8359 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8359 (history t) (history t)).
   { cbn [decode_expr_8359 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8359 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8359 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8264 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8264 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8264 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8263 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8264 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8264 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8264 (history t) (history t)).
   { cbn [decode_expr_8264 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8264 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8264 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8266 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8266 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8266 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8265 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8266 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8266 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8266 (history t) (history t)).
   { cbn [decode_expr_8266 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8266 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8266 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8268 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8268 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8268 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8267 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8268 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8268 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8268 (history t) (history t)).
   { cbn [decode_expr_8268 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8268 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8268 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8270 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8270 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8270 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8269 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8270 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8270 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8270 (history t) (history t)).
   { cbn [decode_expr_8270 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8270 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8270 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8272 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8272 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8272 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8271 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8272 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8272 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8272 (history t) (history t)).
   { cbn [decode_expr_8272 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8272 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8272 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8274 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8274 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8274 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8273 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8274 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8274 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8274 (history t) (history t)).
   { cbn [decode_expr_8274 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8274 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8274 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8276 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8276 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8276 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8275 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8276 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8276 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8276 (history t) (history t)).
   { cbn [decode_expr_8276 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8276 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8276 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8278 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8278 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8278 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8277 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8278 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8278 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8278 (history t) (history t)).
   { cbn [decode_expr_8278 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8278 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8278 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8280 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8280 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8280 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8279 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8280 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8280 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8280 (history t) (history t)).
   { cbn [decode_expr_8280 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8280 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8280 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8282 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8282 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8282 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8281 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8282 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8282 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8282 (history t) (history t)).
   { cbn [decode_expr_8282 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8282 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8282 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8284 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8284 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8284 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8283 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8284 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8284 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8284 (history t) (history t)).
   { cbn [decode_expr_8284 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8284 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8284 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8286 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8286 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8286 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8285 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8286 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8286 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8286 (history t) (history t)).
   { cbn [decode_expr_8286 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8286 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8286 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8288 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8288 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8288 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8287 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8288 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8288 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8288 (history t) (history t)).
   { cbn [decode_expr_8288 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8288 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8288 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8290 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8290 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8290 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8289 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8290 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8290 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8290 (history t) (history t)).
   { cbn [decode_expr_8290 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8290 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8290 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8292 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8292 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8292 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8291 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8292 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8292 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8292 (history t) (history t)).
   { cbn [decode_expr_8292 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8292 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8292 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8294 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8294 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8294 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8293 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8294 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8294 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8294 (history t) (history t)).
   { cbn [decode_expr_8294 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8294 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8294 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8296 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8296 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8296 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8295 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8296 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8296 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8296 (history t) (history t)).
   { cbn [decode_expr_8296 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8296 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8296 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8298 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8298 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8298 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8297 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8298 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8298 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8298 (history t) (history t)).
   { cbn [decode_expr_8298 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8298 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8298 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8300 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8300 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8300 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8299 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8300 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8300 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8300 (history t) (history t)).
   { cbn [decode_expr_8300 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8300 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8300 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8302 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8302 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8302 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8301 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8302 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8302 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8302 (history t) (history t)).
   { cbn [decode_expr_8302 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8302 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8302 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8304 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8304 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8304 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8303 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8304 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8304 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8304 (history t) (history t)).
   { cbn [decode_expr_8304 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8304 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8304 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8306 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8306 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8306 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8305 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8306 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8306 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8306 (history t) (history t)).
   { cbn [decode_expr_8306 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8306 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8306 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8308 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8308 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8308 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8307 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8308 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8308 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8308 (history t) (history t)).
   { cbn [decode_expr_8308 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8308 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8308 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8310 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8310 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8310 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8309 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8310 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8310 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8310 (history t) (history t)).
   { cbn [decode_expr_8310 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8310 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8310 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8312 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8312 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8312 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8311 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8312 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8312 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8312 (history t) (history t)).
   { cbn [decode_expr_8312 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8312 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8312 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8314 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8314 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8314 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8313 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8314 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8314 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8314 (history t) (history t)).
   { cbn [decode_expr_8314 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8314 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8314 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8316 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8316 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8316 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8315 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8316 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8316 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8316 (history t) (history t)).
   { cbn [decode_expr_8316 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8316 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8316 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8318 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8318 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8318 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8317 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8318 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8318 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8318 (history t) (history t)).
   { cbn [decode_expr_8318 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8318 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8318 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8320 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8320 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8320 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8319 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8320 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8320 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8320 (history t) (history t)).
   { cbn [decode_expr_8320 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8320 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8320 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8322 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8322 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8322 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8321 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8322 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8322 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8322 (history t) (history t)).
   { cbn [decode_expr_8322 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8322 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8322 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8324 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8324 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8324 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8323 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8324 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8324 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8324 (history t) (history t)).
   { cbn [decode_expr_8324 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8324 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8324 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8326 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8326 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8326 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8325 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8326 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8326 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8326 (history t) (history t)).
   { cbn [decode_expr_8326 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8326 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8326 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8328 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8328 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8328 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8327 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8328 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8328 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8328 (history t) (history t)).
   { cbn [decode_expr_8328 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8328 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8328 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8330 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8330 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8330 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8329 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8330 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8330 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8330 (history t) (history t)).
   { cbn [decode_expr_8330 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8330 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8330 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8332 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8332 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8332 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8331 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8332 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8332 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8332 (history t) (history t)).
   { cbn [decode_expr_8332 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8332 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8332 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8334 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8334 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8334 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8333 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8334 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8334 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8334 (history t) (history t)).
   { cbn [decode_expr_8334 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8334 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8334 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8336 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8336 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8336 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8335 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8336 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8336 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8336 (history t) (history t)).
   { cbn [decode_expr_8336 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8336 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8336 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8338 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8338 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8338 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8337 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8338 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8338 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8338 (history t) (history t)).
   { cbn [decode_expr_8338 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8338 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8338 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8340 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8340 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8340 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8339 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8340 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8340 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8340 (history t) (history t)).
   { cbn [decode_expr_8340 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8340 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8340 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8342 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8342 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8342 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8341 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8342 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8342 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8342 (history t) (history t)).
   { cbn [decode_expr_8342 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8342 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8342 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8344 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8344 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8344 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8343 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8344 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8344 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8344 (history t) (history t)).
   { cbn [decode_expr_8344 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8344 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8344 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8346 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8346 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8346 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8345 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8346 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8346 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8346 (history t) (history t)).
   { cbn [decode_expr_8346 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8346 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8346 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8348 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8348 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8348 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8347 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8348 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8348 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8348 (history t) (history t)).
   { cbn [decode_expr_8348 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8348 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8348 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8350 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8350 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8350 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8349 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8350 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8350 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8350 (history t) (history t)).
   { cbn [decode_expr_8350 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8350 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8350 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8352 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8352 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8352 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8351 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8352 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8352 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8352 (history t) (history t)).
   { cbn [decode_expr_8352 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8352 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8352 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8354 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8354 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8354 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8353 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8354 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8354 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8354 (history t) (history t)).
   { cbn [decode_expr_8354 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8354 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8354 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8356 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8356 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8356 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8355 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8356 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8356 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8356 (history t) (history t)).
   { cbn [decode_expr_8356 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8356 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8356 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8358 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8358 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8358 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8357 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8358 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8358 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8358 (history t) (history t)).
   { cbn [decode_expr_8358 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8358 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8358 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8360 : forall t u, (Nat.le 4 t /\ Nat.le t n) -> (Nat.le 4 u /\ Nat.le u n) -> exists bit, VM.find 8360 (history t) = Some (Gval (Fuint 1) [::bit]) /\ VM.find 8360 (history u) = Some (Gval (Fuint 1) [::bit])).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8359 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8360 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8360 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8360 (history t) (history t)).
   { cbn [decode_expr_8360 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8360 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8360 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8361 : forall t u, (Nat.le 5 t /\ Nat.le t n) -> (Nat.le 5 u /\ Nat.le u n) -> exists word, VM.find 8361 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8361 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8360 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (decode_eval_8361 flat_memories (history t) source0 Source0) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8361 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8361 (history t) (history t)).
   { cbn [decode_expr_8361 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8361 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8361 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8362 : forall t u, (Nat.le 6 t /\ Nat.le t n) -> (Nat.le 6 u /\ Nat.le u n) -> exists word, VM.find 8362 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8362 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8358 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8361 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8362 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8362 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8362 (history t) (history t)).
   { cbn [decode_expr_8362 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8362 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8362 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8363 : forall t u, (Nat.le 7 t /\ Nat.le t n) -> (Nat.le 7 u /\ Nat.le u n) -> exists word, VM.find 8363 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8363 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8356 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8362 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8363 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8363 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8363 (history t) (history t)).
   { cbn [decode_expr_8363 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8363 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8363 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8364 : forall t u, (Nat.le 8 t /\ Nat.le t n) -> (Nat.le 8 u /\ Nat.le u n) -> exists word, VM.find 8364 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8364 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8354 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8363 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8364 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8364 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8364 (history t) (history t)).
   { cbn [decode_expr_8364 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8364 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8364 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8365 : forall t u, (Nat.le 9 t /\ Nat.le t n) -> (Nat.le 9 u /\ Nat.le u n) -> exists word, VM.find 8365 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8365 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8352 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8364 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8365 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8365 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8365 (history t) (history t)).
   { cbn [decode_expr_8365 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8365 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8365 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8366 : forall t u, (Nat.le 10 t /\ Nat.le t n) -> (Nat.le 10 u /\ Nat.le u n) -> exists word, VM.find 8366 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8366 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8350 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8365 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8366 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8366 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8366 (history t) (history t)).
   { cbn [decode_expr_8366 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8366 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8366 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8367 : forall t u, (Nat.le 11 t /\ Nat.le t n) -> (Nat.le 11 u /\ Nat.le u n) -> exists word, VM.find 8367 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8367 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8348 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8366 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8367 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8367 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8367 (history t) (history t)).
   { cbn [decode_expr_8367 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8367 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8367 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8368 : forall t u, (Nat.le 12 t /\ Nat.le t n) -> (Nat.le 12 u /\ Nat.le u n) -> exists word, VM.find 8368 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8368 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8346 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8367 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8368 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8368 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8368 (history t) (history t)).
   { cbn [decode_expr_8368 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8368 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8368 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8369 : forall t u, (Nat.le 13 t /\ Nat.le t n) -> (Nat.le 13 u /\ Nat.le u n) -> exists word, VM.find 8369 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8369 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8344 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8368 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8369 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8369 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8369 (history t) (history t)).
   { cbn [decode_expr_8369 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8369 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8369 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8370 : forall t u, (Nat.le 14 t /\ Nat.le t n) -> (Nat.le 14 u /\ Nat.le u n) -> exists word, VM.find 8370 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8370 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8342 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8369 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8370 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8370 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8370 (history t) (history t)).
   { cbn [decode_expr_8370 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8370 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8370 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8371 : forall t u, (Nat.le 15 t /\ Nat.le t n) -> (Nat.le 15 u /\ Nat.le u n) -> exists word, VM.find 8371 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8371 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8340 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8370 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8371 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8371 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8371 (history t) (history t)).
   { cbn [decode_expr_8371 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8371 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8371 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8372 : forall t u, (Nat.le 16 t /\ Nat.le t n) -> (Nat.le 16 u /\ Nat.le u n) -> exists word, VM.find 8372 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8372 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8338 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8371 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8372 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8372 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8372 (history t) (history t)).
   { cbn [decode_expr_8372 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8372 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8372 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8373 : forall t u, (Nat.le 17 t /\ Nat.le t n) -> (Nat.le 17 u /\ Nat.le u n) -> exists word, VM.find 8373 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8373 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8336 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8372 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8373 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8373 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8373 (history t) (history t)).
   { cbn [decode_expr_8373 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8373 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8373 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8374 : forall t u, (Nat.le 18 t /\ Nat.le t n) -> (Nat.le 18 u /\ Nat.le u n) -> exists word, VM.find 8374 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8374 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8334 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8373 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8374 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8374 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8374 (history t) (history t)).
   { cbn [decode_expr_8374 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8374 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8374 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8375 : forall t u, (Nat.le 19 t /\ Nat.le t n) -> (Nat.le 19 u /\ Nat.le u n) -> exists word, VM.find 8375 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8375 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8332 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8374 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8375 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8375 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8375 (history t) (history t)).
   { cbn [decode_expr_8375 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8375 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8375 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8376 : forall t u, (Nat.le 20 t /\ Nat.le t n) -> (Nat.le 20 u /\ Nat.le u n) -> exists word, VM.find 8376 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8376 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8330 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8375 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8376 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8376 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8376 (history t) (history t)).
   { cbn [decode_expr_8376 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8376 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8376 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8377 : forall t u, (Nat.le 21 t /\ Nat.le t n) -> (Nat.le 21 u /\ Nat.le u n) -> exists word, VM.find 8377 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8377 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8328 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8376 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8377 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8377 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8377 (history t) (history t)).
   { cbn [decode_expr_8377 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8377 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8377 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8378 : forall t u, (Nat.le 22 t /\ Nat.le t n) -> (Nat.le 22 u /\ Nat.le u n) -> exists word, VM.find 8378 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8378 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8326 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8377 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8378 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8378 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8378 (history t) (history t)).
   { cbn [decode_expr_8378 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8378 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8378 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8379 : forall t u, (Nat.le 23 t /\ Nat.le t n) -> (Nat.le 23 u /\ Nat.le u n) -> exists word, VM.find 8379 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8379 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8324 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8378 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8379 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8379 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8379 (history t) (history t)).
   { cbn [decode_expr_8379 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8379 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8379 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8380 : forall t u, (Nat.le 24 t /\ Nat.le t n) -> (Nat.le 24 u /\ Nat.le u n) -> exists word, VM.find 8380 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8380 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8322 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8379 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8380 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8380 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8380 (history t) (history t)).
   { cbn [decode_expr_8380 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8380 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8380 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8381 : forall t u, (Nat.le 25 t /\ Nat.le t n) -> (Nat.le 25 u /\ Nat.le u n) -> exists word, VM.find 8381 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8381 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8320 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8380 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8381 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8381 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8381 (history t) (history t)).
   { cbn [decode_expr_8381 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8381 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8381 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8382 : forall t u, (Nat.le 26 t /\ Nat.le t n) -> (Nat.le 26 u /\ Nat.le u n) -> exists word, VM.find 8382 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8382 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8318 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8381 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8382 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8382 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8382 (history t) (history t)).
   { cbn [decode_expr_8382 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8382 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8382 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8383 : forall t u, (Nat.le 27 t /\ Nat.le t n) -> (Nat.le 27 u /\ Nat.le u n) -> exists word, VM.find 8383 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8383 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8316 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8382 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8383 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8383 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8383 (history t) (history t)).
   { cbn [decode_expr_8383 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8383 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8383 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8384 : forall t u, (Nat.le 28 t /\ Nat.le t n) -> (Nat.le 28 u /\ Nat.le u n) -> exists word, VM.find 8384 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8384 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8314 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8383 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8384 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8384 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8384 (history t) (history t)).
   { cbn [decode_expr_8384 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8384 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8384 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8385 : forall t u, (Nat.le 29 t /\ Nat.le t n) -> (Nat.le 29 u /\ Nat.le u n) -> exists word, VM.find 8385 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8385 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8312 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8384 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8385 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8385 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8385 (history t) (history t)).
   { cbn [decode_expr_8385 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8385 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8385 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8386 : forall t u, (Nat.le 30 t /\ Nat.le t n) -> (Nat.le 30 u /\ Nat.le u n) -> exists word, VM.find 8386 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8386 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8310 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8385 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8386 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8386 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8386 (history t) (history t)).
   { cbn [decode_expr_8386 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8386 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8386 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8387 : forall t u, (Nat.le 31 t /\ Nat.le t n) -> (Nat.le 31 u /\ Nat.le u n) -> exists word, VM.find 8387 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8387 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8308 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8386 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8387 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8387 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8387 (history t) (history t)).
   { cbn [decode_expr_8387 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8387 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8387 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8388 : forall t u, (Nat.le 32 t /\ Nat.le t n) -> (Nat.le 32 u /\ Nat.le u n) -> exists word, VM.find 8388 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8388 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8306 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8387 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8388 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8388 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8388 (history t) (history t)).
   { cbn [decode_expr_8388 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8388 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8388 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8389 : forall t u, (Nat.le 33 t /\ Nat.le t n) -> (Nat.le 33 u /\ Nat.le u n) -> exists word, VM.find 8389 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8389 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8304 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8388 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8389 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8389 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8389 (history t) (history t)).
   { cbn [decode_expr_8389 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8389 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8389 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8390 : forall t u, (Nat.le 34 t /\ Nat.le t n) -> (Nat.le 34 u /\ Nat.le u n) -> exists word, VM.find 8390 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8390 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8302 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8389 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8390 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8390 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8390 (history t) (history t)).
   { cbn [decode_expr_8390 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8390 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8390 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8391 : forall t u, (Nat.le 35 t /\ Nat.le t n) -> (Nat.le 35 u /\ Nat.le u n) -> exists word, VM.find 8391 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8391 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8300 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8390 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8391 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8391 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8391 (history t) (history t)).
   { cbn [decode_expr_8391 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8391 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8391 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8392 : forall t u, (Nat.le 36 t /\ Nat.le t n) -> (Nat.le 36 u /\ Nat.le u n) -> exists word, VM.find 8392 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8392 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8298 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8391 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8392 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8392 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8392 (history t) (history t)).
   { cbn [decode_expr_8392 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8392 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8392 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8393 : forall t u, (Nat.le 37 t /\ Nat.le t n) -> (Nat.le 37 u /\ Nat.le u n) -> exists word, VM.find 8393 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8393 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8296 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8392 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8393 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8393 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8393 (history t) (history t)).
   { cbn [decode_expr_8393 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8393 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8393 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8394 : forall t u, (Nat.le 38 t /\ Nat.le t n) -> (Nat.le 38 u /\ Nat.le u n) -> exists word, VM.find 8394 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8394 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8294 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8393 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8394 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8394 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8394 (history t) (history t)).
   { cbn [decode_expr_8394 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8394 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8394 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8395 : forall t u, (Nat.le 39 t /\ Nat.le t n) -> (Nat.le 39 u /\ Nat.le u n) -> exists word, VM.find 8395 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8395 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8292 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8394 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8395 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8395 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8395 (history t) (history t)).
   { cbn [decode_expr_8395 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8395 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8395 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8396 : forall t u, (Nat.le 40 t /\ Nat.le t n) -> (Nat.le 40 u /\ Nat.le u n) -> exists word, VM.find 8396 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8396 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8290 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8395 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8396 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8396 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8396 (history t) (history t)).
   { cbn [decode_expr_8396 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8396 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8396 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8397 : forall t u, (Nat.le 41 t /\ Nat.le t n) -> (Nat.le 41 u /\ Nat.le u n) -> exists word, VM.find 8397 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8397 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8288 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8396 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8397 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8397 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8397 (history t) (history t)).
   { cbn [decode_expr_8397 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8397 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8397 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8398 : forall t u, (Nat.le 42 t /\ Nat.le t n) -> (Nat.le 42 u /\ Nat.le u n) -> exists word, VM.find 8398 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8398 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8286 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8397 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8398 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8398 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8398 (history t) (history t)).
   { cbn [decode_expr_8398 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8398 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8398 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8399 : forall t u, (Nat.le 43 t /\ Nat.le t n) -> (Nat.le 43 u /\ Nat.le u n) -> exists word, VM.find 8399 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8399 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8284 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8398 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8399 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8399 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8399 (history t) (history t)).
   { cbn [decode_expr_8399 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8399 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8399 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8400 : forall t u, (Nat.le 44 t /\ Nat.le t n) -> (Nat.le 44 u /\ Nat.le u n) -> exists word, VM.find 8400 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8400 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8282 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8399 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8400 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8400 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8400 (history t) (history t)).
   { cbn [decode_expr_8400 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8400 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8400 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8401 : forall t u, (Nat.le 45 t /\ Nat.le t n) -> (Nat.le 45 u /\ Nat.le u n) -> exists word, VM.find 8401 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8401 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8280 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8400 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8401 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8401 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8401 (history t) (history t)).
   { cbn [decode_expr_8401 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8401 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8401 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8402 : forall t u, (Nat.le 46 t /\ Nat.le t n) -> (Nat.le 46 u /\ Nat.le u n) -> exists word, VM.find 8402 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8402 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8278 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8401 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8402 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8402 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8402 (history t) (history t)).
   { cbn [decode_expr_8402 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8402 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8402 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8403 : forall t u, (Nat.le 47 t /\ Nat.le t n) -> (Nat.le 47 u /\ Nat.le u n) -> exists word, VM.find 8403 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8403 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8276 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8402 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8403 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8403 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8403 (history t) (history t)).
   { cbn [decode_expr_8403 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8403 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8403 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8404 : forall t u, (Nat.le 48 t /\ Nat.le t n) -> (Nat.le 48 u /\ Nat.le u n) -> exists word, VM.find 8404 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8404 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8274 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8403 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8404 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8404 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8404 (history t) (history t)).
   { cbn [decode_expr_8404 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8404 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8404 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8405 : forall t u, (Nat.le 49 t /\ Nat.le t n) -> (Nat.le 49 u /\ Nat.le u n) -> exists word, VM.find 8405 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8405 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8272 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8404 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8405 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8405 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8405 (history t) (history t)).
   { cbn [decode_expr_8405 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8405 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8405 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8406 : forall t u, (Nat.le 50 t /\ Nat.le t n) -> (Nat.le 50 u /\ Nat.le u n) -> exists word, VM.find 8406 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8406 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8270 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8405 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8406 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8406 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8406 (history t) (history t)).
   { cbn [decode_expr_8406 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8406 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8406 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8407 : forall t u, (Nat.le 51 t /\ Nat.le t n) -> (Nat.le 51 u /\ Nat.le u n) -> exists word, VM.find 8407 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8407 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8268 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8406 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8407 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8407 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8407 (history t) (history t)).
   { cbn [decode_expr_8407 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8407 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8407 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8408 : forall t u, (Nat.le 52 t /\ Nat.le t n) -> (Nat.le 52 u /\ Nat.le u n) -> exists word, VM.find 8408 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8408 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8266 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8407 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8408 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8408 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8408 (history t) (history t)).
   { cbn [decode_expr_8408 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8408 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8408 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8409 : forall t u, (Nat.le 53 t /\ Nat.le t n) -> (Nat.le 53 u /\ Nat.le u n) -> exists word, VM.find 8409 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8409 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8264 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   destruct (V8408 t u ltac:(lia) ltac:(lia)) as [source1 [Source1 Other1]].
   destruct (decode_eval_8409 flat_memories (history t) source0 source1 Source0 Source1) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_8409 (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_8409 (history t) (history t)).
   { cbn [decode_expr_8409 eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
     rewrite Source0 Other0.
     rewrite Source1 Other1.
     reflexivity. }
   exists value. split.
   - exact (decode_node_8409 invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_8409 invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
 }
 assert (V8250 : forall t u, (Nat.le 54 t /\ Nat.le t n) -> (Nat.le 54 u /\ Nat.le u n) -> exists word, VM.find 8250 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 8250 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8409 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   eexists. split; eapply pc_decode_connection_8250; [exact Source0|reflexivity|apply Steps;lia|exact Other0|reflexivity|apply Steps;lia].
 }
 assert (V84 : forall t u, (Nat.le 55 t /\ Nat.le t n) -> (Nat.le 55 u /\ Nat.le u n) -> exists word, VM.find 84 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 84 (history u) = Some (Gval (Fuint 2) word)).
 { intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
   destruct (V8250 t u ltac:(lia) ltac:(lia)) as [source0 [Source0 Other0]].
   eexists. split; eapply pc_decode_connection_84; [exact Source0|reflexivity|apply Steps;lia|exact Other0|reflexivity|apply Steps;lia].
 }
 intros t u LT LU UT UU. apply V84; lia.
Qed.
