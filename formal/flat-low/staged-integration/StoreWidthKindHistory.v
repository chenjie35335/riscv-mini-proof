Require Import MemoryRequestWidth.
Require Import StoreWidthSelectNode CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_width_select_kind invalid old current result previous kind :
 VM.find 7765 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7754 old=Some previous ->type_of_val previous=Gtyp(Fuint 2) ->
 VM.find 91 old=Some(Gval(Fuint 2)(from_N 2 (N.of_nat kind))) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7996 result=Some(Gval(Fuint 2)(from_N 2 (N.of_nat kind))).
Proof.
 intros Stall Previous Typed Decode Step.
 eapply(store_width_select_node_step 7996 store_width_select_expr_7996 invalid old current result).
 - unfold store_width_select_nodes. left;reflexivity.
 - intro site. cbn[store_width_select_expr_7996 eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite Stall. cbn. rewrite Decode.
   unfold eval_type_of_expr. cbn[type_of_expr' eval_type_of_ref]. rewrite Previous. cbn[option_map]. rewrite Typed. reflexivity.
 - exact Step.
Qed.
Theorem store_width_kind_history invalid history limit start kind :
 (kind<4)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7765(history t)=Some(Gval(Fuint 1)[::false])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists previous,VM.find 7754(history t)=Some previous /\type_of_val previous=Gtyp(Fuint 2)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 91(history t)=Some(Gval(Fuint 2)(from_N 2 (N.of_nat kind)))) ->
 forall t,(Nat.add start 13<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8002(history t)=Some(Gval(Fuint 6)(from_N 6 (memory_request_width true kind))).
Proof.
 intros Kind Steps Stall Previous Decode t Lower Upper.
 assert(Selected:forall u,(S start<=u)%coq_nat ->(u<=limit)%coq_nat ->VM.find 7996(history u)=Some(Gval(Fuint 2)(from_N 2 (N.of_nat kind)))).
 { intros [|u] Low High;[lia|].
   destruct(Previous u ltac:(lia)ltac:(lia))as[previous[Value Typed]].
   exact(store_width_select_kind invalid (history u)(history u)(history(S u))previous kind
    (Stall u ltac:(lia)ltac:(lia))Value Typed(Decode u ltac:(lia)ltac:(lia))(Steps u ltac:(lia))). }
 pose proof(memory_width_decoder_history true kind invalid
   (fun i=>history(Nat.add(S start)i)) (Nat.sub limit(S start)) Kind)as Width.
 assert(ShiftSteps:forall i,(i<Nat.sub limit(S start))%coq_nat ->formal_value_iter invalid flat_memories(history(Nat.add(S start)i))false(history(Nat.add(S start)i))flat_statements=Some(history(Nat.add(S start)(S i)))).
 { intros i Bound. replace(Nat.add(S start)(S i))with(S(Nat.add(S start)i))by lia. apply Steps;lia. }
 specialize(Width ShiftSteps ltac:(intros i Bound;apply Selected;lia)
 (Nat.sub t(S start)) ltac:(lia) ltac:(lia)).
 cbv beta in Width.
 replace(Nat.add(S start)(Nat.sub t(S start)))with t in Width by lia.
 exact Width.
Qed.
