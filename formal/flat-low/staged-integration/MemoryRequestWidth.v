Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine LoadTypeCorrespondence DUTRedirectDecode FormalDeclaredWireCheck JointUpdateBoundaryHistory FormalObservedHistory FormalLocalHistory JointBoundaryRegisters.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition memory_width_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(7984,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))));(7985,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7984)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 1) [::false])));(7986,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))));(7987,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7986)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7985))));(7988,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))));(7989,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7988)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7987))));(7990,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))));(7991,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7990)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7989))));(7992,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))));(7993,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7992)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7991))));(7994,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))));(7995,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7994)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7993))));(7997,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7996))));(7998,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7997)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; true; false; false]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false])));(7999,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7996))));(8000,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7999)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7998))));(8001,(@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7996))));(8002,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8001)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8000))));(8077,(@Eref VarOrder.T (@Eid VarOrder.T 7995)));(8078,(@Eref VarOrder.T (@Eid VarOrder.T 8077)));(8085,(@Eref VarOrder.T (@Eid VarOrder.T 8040)));(8086,(@Eref VarOrder.T (@Eid VarOrder.T 8085)));(8200,(@Eref VarOrder.T (@Eid VarOrder.T 8078)));(8204,(@Eref VarOrder.T (@Eid VarOrder.T 8086)))].
Definition memory_width_offsets := [::8490%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;1%nat;0%nat;0%nat;0%nat;0%nat;0%nat;74%nat;0%nat;6%nat;0%nat;113%nat;3%nat].
Lemma memory_width_wire writing : declared_wire_check flat_memories flat_statements
 (if writing then 1559 else 1555) (if writing then 7408 else 7408)
 (if writing then 1480 else 1476) (if writing then 8204 else 8200) 6 = true.
Proof. destruct writing;vm_compute;reflexivity. Qed.
Lemma memory_width_positions : select_node_offsets memory_width_offsets flat_statements = Some memory_width_nodes.
Proof. vm_compute; reflexivity. Qed.
Lemma memory_width_safety : selected_node_safety flat_memories flat_statements memory_width_offsets flat_statements = true.
Proof. vm_compute; reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition memory_request_width (writing:bool) (kind:nat) : N :=
 if writing then nth 0 [::0;32;16;8] kind else nth 0 [::0;32;16;8;16;8;0;0] kind.
Definition memory_request_active writing kind := negb (N.eqb (memory_request_width writing kind) 0).
Theorem memory_width_decoder_history writing kind invalid history limit :
 (kind < (if writing then 4 else 8))%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= limit)%coq_nat -> VM.find (if writing then 7996 else 7755) (history i) = Some (Gval (Fuint (if writing then 2 else 3)) (from_N (if writing then 2 else 3) (N.of_nat kind)))) ->
 forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (if writing then 8002 else 7995) (history time) = Some (Gval (Fuint 6) (from_N 6 (memory_request_width writing kind))).
Proof.
 intros Kind Steps Source. destruct writing;cbn in Kind.
 - 
 assert (V7997 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7997 (history time) = Some (Gval (Fuint 1) (nth [::] [::[::false];[::false];[::false];[::true]] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7997 ((@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7996)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 12%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (Source time ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(Source time ltac:(lia)).
   do 4 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7998 : forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7998 (history time) = Some (Gval (Fuint 6) (nth [::] [::from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 8] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7998 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7997)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; true; false; false]) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false]))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 13%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (V7997 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(V7997 time ltac:(lia) ltac:(lia)).
   do 4 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7999 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7999 (history time) = Some (Gval (Fuint 1) (nth [::] [::[::false];[::false];[::true];[::false]] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7999 ((@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7996)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 14%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (Source time ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(Source time ltac:(lia)).
   do 4 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V8000 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8000 (history time) = Some (Gval (Fuint 6) (nth [::] [::from_N 6 0;from_N 6 0;from_N 6 16;from_N 6 8] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 8000 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7999)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7998)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 15%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (V7999 time ltac:(lia) ltac:(lia)) (V7998 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(V7999 time ltac:(lia) ltac:(lia)) ?(V7998 time ltac:(lia) ltac:(lia)).
   do 4 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V8001 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8001 (history time) = Some (Gval (Fuint 1) (nth [::] [::[::false];[::true];[::false];[::false]] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 8001 ((@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7996)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 16%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (Source time ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(Source time ltac:(lia)).
   do 4 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V8002 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8002 (history time) = Some (Gval (Fuint 6) (nth [::] [::from_N 6 0;from_N 6 32;from_N 6 16;from_N 6 8] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 8002 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8001)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8000)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 17%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (V8001 time ltac:(lia) ltac:(lia)) (V8000 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(V8001 time ltac:(lia) ltac:(lia)) ?(V8000 time ltac:(lia) ltac:(lia)).
   do 4 (destruct kind as [|kind];[reflexivity|]);lia. }
 intros time Lower Upper. specialize (V8002 time ltac:(lia) Upper).
 do 4 (destruct kind as [|kind];[exact V8002|]);lia.
 - 
 assert (V7984 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7984 (history time) = Some (Gval (Fuint 1) (nth [::] [::[::true];[::false];[::false];[::false];[::false];[::false];[::false];[::false]] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7984 ((@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 0%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (Source time ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(Source time ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7985 : forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7985 (history time) = Some (Gval (Fuint 6) (nth [::] [::from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 0] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7985 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7984)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 1) [::false]))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 1%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (V7984 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(V7984 time ltac:(lia) ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7986 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7986 (history time) = Some (Gval (Fuint 1) (nth [::] [::[::false];[::false];[::false];[::true];[::false];[::false];[::false];[::false]] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7986 ((@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 2%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (Source time ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(Source time ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7987 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7987 (history time) = Some (Gval (Fuint 6) (nth [::] [::from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 8;from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 0] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7987 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7986)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7985)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 3%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (V7986 time ltac:(lia) ltac:(lia)) (V7985 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(V7986 time ltac:(lia) ltac:(lia)) ?(V7985 time ltac:(lia) ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7988 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7988 (history time) = Some (Gval (Fuint 1) (nth [::] [::[::false];[::false];[::true];[::false];[::false];[::false];[::false];[::false]] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7988 ((@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 4%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (Source time ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(Source time ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7989 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7989 (history time) = Some (Gval (Fuint 6) (nth [::] [::from_N 6 0;from_N 6 0;from_N 6 16;from_N 6 8;from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 0] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7989 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7988)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7987)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 5%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (V7988 time ltac:(lia) ltac:(lia)) (V7987 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(V7988 time ltac:(lia) ltac:(lia)) ?(V7987 time ltac:(lia) ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7990 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7990 (history time) = Some (Gval (Fuint 1) (nth [::] [::[::false];[::true];[::false];[::false];[::false];[::false];[::false];[::false]] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7990 ((@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 6%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (Source time ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(Source time ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7991 : forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7991 (history time) = Some (Gval (Fuint 6) (nth [::] [::from_N 6 0;from_N 6 32;from_N 6 16;from_N 6 8;from_N 6 0;from_N 6 0;from_N 6 0;from_N 6 0] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7991 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7990)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7989)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 7%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (V7990 time ltac:(lia) ltac:(lia)) (V7989 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(V7990 time ltac:(lia) ltac:(lia)) ?(V7989 time ltac:(lia) ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7992 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7992 (history time) = Some (Gval (Fuint 1) (nth [::] [::[::false];[::false];[::false];[::false];[::false];[::true];[::false];[::false]] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7992 ((@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7755)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 8%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (Source time ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(Source time ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7993 : forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7993 (history time) = Some (Gval (Fuint 6) (nth [::] [::from_N 6 0;from_N 6 32;from_N 6 16;from_N 6 8;from_N 6 0;from_N 6 8;from_N 6 0;from_N 6 0] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7993 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7992)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7991)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 9%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (V7992 time ltac:(lia) ltac:(lia)) (V7991 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(V7992 time ltac:(lia) ltac:(lia)) ?(V7991 time ltac:(lia) ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7994 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7994 (history time) = Some (Gval (Fuint 1) (nth [::] [::[::false];[::false];[::false];[::false];[::true];[::false];[::false];[::false]] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7994 ((@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7755)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 10%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (Source time ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(Source time ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 assert (V7995 : forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7995 (history time) = Some (Gval (Fuint 6) (nth [::] [::from_N 6 0;from_N 6 32;from_N 6 16;from_N 6 8;from_N 6 16;from_N 6 8;from_N 6 0;from_N 6 0] kind))).
 { intros [|time] Lower Upper;try lia.
   eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes 7995 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7994)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7993)))));
   [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 11%nat);vm_compute;reflexivity| |apply Steps;lia].
   intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite (V7994 time ltac:(lia) ltac:(lia)) (V7993 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?(V7994 time ltac:(lia) ltac:(lia)) ?(V7993 time ltac:(lia) ltac:(lia)).
   do 8 (destruct kind as [|kind];[reflexivity|]);lia. }
 intros time Lower Upper. specialize (V7995 time ltac:(lia) Upper).
 do 8 (destruct kind as [|kind];[exact V7995|]);lia.
Qed.
(* Shared request semantics. *)
Theorem memory_width_alias_history writing word invalid history limit :
 size word = 6%nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (12 <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find (if writing then 8040 else 7995) (history i) = Some (Gval (Fuint 6) word)) ->
 forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (if writing then 1480 else 1476) (history time) = Some (Gval (Fuint 6) word).
Proof.
 intros Size Steps Source [|[|[|[|time]]]] Lower Upper;try lia.
 eapply declared_wire_checked_value;[exact (memory_width_wire writing)| |apply dut_decode_adapt;exact Size|apply Steps;lia].
 assert (Alias : forall stage t, (stage < 3)%coq_nat -> (Nat.add 13 stage <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find (nth 0 (if writing then [::8085;8086;8204] else [::8077;8078;8200]) stage) (history t) = Some (Gval (Fuint 6) word)).
 { intros stage. induction stage as [|stage IH];intros [|t] Bound Lo Hi;try lia.
   - destruct writing; eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes _ (@Eref VarOrder.T (@Eid VarOrder.T _)));
     [exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 20%nat);vm_compute;reflexivity| |apply Steps;lia
     |exact memory_width_positions|exact memory_width_safety|apply (List.nth_error_In memory_width_nodes 18%nat);vm_compute;reflexivity| |apply Steps;lia];
     intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];apply Source;lia.
   - pose proof (IH t ltac:(lia) ltac:(lia) ltac:(lia)) as Prior.
     destruct writing;destruct stage as [|[|stage]];try lia;
     eapply (reference_redirect_ground_step memory_width_offsets memory_width_nodes _ (@Eref VarOrder.T (@Eid VarOrder.T _)));
     try exact memory_width_positions;try exact memory_width_safety;try (apply Steps;lia).
     + apply (List.nth_error_In memory_width_nodes 21%nat);vm_compute;reflexivity.
     + intros site;exact Prior.
     + apply (List.nth_error_In memory_width_nodes 23%nat);vm_compute;reflexivity.
     + intros site;exact Prior.
     + apply (List.nth_error_In memory_width_nodes 19%nat);vm_compute;reflexivity.
     + intros site;exact Prior.
     + apply (List.nth_error_In memory_width_nodes 22%nat);vm_compute;reflexivity.
     + intros site;exact Prior. }
 pose proof (Alias 2%nat (S (S (S time))) ltac:(lia) ltac:(lia) ltac:(lia)) as Final.
 destruct writing;exact Final.
Qed.
Definition memory_load_lane_width lane : N := nth 0 [::16;8;32;16;8] lane.
Theorem memory_load_width_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (lane < 5)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 VM.find 1476 (top_environment observed) = Some (Gval (Fuint 6) (from_N 6 (memory_load_lane_width lane))).
Proof.
 intros Observe Legal Lane Instruction Load.
 pose proof (load_type_instruction_observed memory inputs k observed instruction lane Observe Legal Lane Instruction Load) as Mode.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Source : forall i, (i <= 9259)%coq_nat -> VM.find 7755 (history i) = Some (Gval (Fuint 3) (from_N 3 (load_type_lane_kind lane)))).
 { intros i Bound.
   pose proof (joint_update_register_history_same (formal_invalid_policy (generated_observation_input inputs k) nil) history 9259 7755 3
    ltac:(apply (List.nth_error_In joint_boundary_registers 60%nat);vm_compute;reflexivity) Steps) as Hold.
   rewrite (Hold i Bound). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Mode. }
 assert (Bound : (N.to_nat (load_type_lane_kind lane) < 8)%coq_nat).
 { do 5 (destruct lane as [|lane];[vm_compute;lia|]);lia. }
 assert (Widths : memory_request_width false (N.to_nat (load_type_lane_kind lane)) = memory_load_lane_width lane).
 { do 5 (destruct lane as [|lane];[reflexivity|]);lia. }
 rewrite <- Last. eapply (memory_width_alias_history false);[apply size_from_N|exact Steps| |vm_compute;lia|vm_compute;lia].
 intros i Lower Upper. rewrite <- Widths.
 eapply (memory_width_decoder_history false);[exact Bound|exact Steps| |exact Lower|exact Upper].
 intros j J. cbn. rewrite N2Nat.id. apply Source;exact J.
Qed.
