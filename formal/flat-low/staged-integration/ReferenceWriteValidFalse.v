Require Import ReferenceWriteValidShapes ReferenceRequestSpine ReferenceRedirectSpine CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma reference_write_false_6641 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 6641 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Step.
 eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 6641 (@Econst VarOrder.T (Fuint 1) [::false]));
 [exact reference_request_positions|exact reference_request_safety|apply(List.nth_error_In reference_request_nodes 20%nat);vm_compute;reflexivity| |exact Step].
 intro site.
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity.
Qed.
Lemma reference_write_false_6642 invalid old current result :
 VM.find 1951 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 6641 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 6642 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Guard No Step.
 eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 6642 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1951)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6641))));
 [exact reference_request_positions|exact reference_request_safety|apply(List.nth_error_In reference_request_nodes 21%nat);vm_compute;reflexivity| |exact Step].
 intro site.
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Guard. cbn. rewrite No. reflexivity.
Qed.
Lemma reference_write_false_6668 invalid old current result other :
 VM.find 1946 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 6659 old=Some other ->type_of_val other=Gtyp(Fuint 1) ->
 VM.find 6642 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 6668 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Guard Yes Typed No Step.
 eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 6668 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1946)) (@Eref VarOrder.T (@Eid VarOrder.T 6659)) (@Eref VarOrder.T (@Eid VarOrder.T 6642))));
 [exact reference_request_positions|exact reference_request_safety|apply(List.nth_error_In reference_request_nodes 26%nat);vm_compute;reflexivity| |exact Step].
 intro site.
 exact(reference_write_false_mux_typed invalid site old 1946 6659 6642 other Guard Yes Typed No).
Qed.
Lemma reference_write_false_6692 invalid old current result other :
 VM.find 1941 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 6683 old=Some other ->type_of_val other=Gtyp(Fuint 1) ->
 VM.find 6668 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 6692 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Guard Yes Typed No Step.
 eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 6692 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1941)) (@Eref VarOrder.T (@Eid VarOrder.T 6683)) (@Eref VarOrder.T (@Eid VarOrder.T 6668))));
 [exact reference_request_positions|exact reference_request_safety|apply(List.nth_error_In reference_request_nodes 30%nat);vm_compute;reflexivity| |exact Step].
 intro site.
 exact(reference_write_false_mux_typed invalid site old 1941 6683 6668 other Guard Yes Typed No).
Qed.
Lemma reference_write_false_7113 invalid old current result bit :
 VM.find 1707 old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find 6692 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 6641 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7113 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Guard Yes No Step.
 eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 7113 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6692)) (@Eref VarOrder.T (@Eid VarOrder.T 6641))));
 [exact reference_request_positions|exact reference_request_safety|apply(List.nth_error_In reference_request_nodes 34%nat);vm_compute;reflexivity| |exact Step].
 intro site.
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Guard. destruct bit;cbn;rewrite ?Yes ?No;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?Yes ?No;reflexivity.
Qed.
