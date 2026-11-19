Require Import StoreAddressSelectNodes CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_address_select_step invalid old current result select pending address :
 size pending=32%nat ->size address=32%nat ->
 VM.find 7765 old=Some(Gval(Fuint 1)[::select]) ->
 VM.find 7752 old=Some(Gval(Fuint 32)pending) ->
 VM.find 1155 old=Some(Gval(Fuint 32)address) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8003 result=Some(Gval(Fuint 32)(if select then pending else address)).
Proof.
 intros PS AS Select Pending Address Step.
 assert(P:zext_to 32(take 32 pending)=pending).
 { rewrite -PS take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity. }
 assert(A:zext_to 32(take 32 address)=address).
 { rewrite -AS take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity. }
 eapply(store_address_select_node_step 8003 store_address_select_expr_8003 invalid old current result).
 - unfold store_address_select_nodes. left;reflexivity.
 - intro site. cbn[store_address_select_expr_8003 eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite Select Pending Address. unfold eval_type_of_expr. cbn[type_of_expr' eval_type_of_ref].
   rewrite Pending Address. destruct select.
   + change (Some(Gval(Fuint 32)(zext_to 32(take 32 pending)))=Some(Gval(Fuint 32)pending)). rewrite P. reflexivity.
   + change (Some(Gval(Fuint 32)(zext_to 32(take 32 address)))=Some(Gval(Fuint 32)address)). rewrite A. reflexivity.
 - exact Step.
Qed.
