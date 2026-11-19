Require Import CoreSocModel ComparisonNodes ReferenceInstructionDecode ReferenceIllegalFold ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence3.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_illegal_expression row := @Emux VarOrder.T
 (@Eref VarOrder.T (@Eid VarOrder.T (reference_instruction_guard row)))
 (@Econst VarOrder.T (Fuint 1) [::false])
 (match row with O => @Econst VarOrder.T (Fuint 1) [::true]
 | S n => @Eref VarOrder.T (@Eid VarOrder.T (2993 + N.of_nat n)) end).
Lemma reference_illegal_member row : (row < 48)%coq_nat ->
 List.In (2993+N.of_nat row, reference_illegal_expression row) reference_control_3_nodes.
Proof. intro Bound.
 destruct row as [|row];[exact reference_control_member_2993|].
 destruct row as [|row];[exact reference_control_member_2994|].
 destruct row as [|row];[exact reference_control_member_2995|].
 destruct row as [|row];[exact reference_control_member_2996|].
 destruct row as [|row];[exact reference_control_member_2997|].
 destruct row as [|row];[exact reference_control_member_2998|].
 destruct row as [|row];[exact reference_control_member_2999|].
 destruct row as [|row];[exact reference_control_member_3000|].
 destruct row as [|row];[exact reference_control_member_3001|].
 destruct row as [|row];[exact reference_control_member_3002|].
 destruct row as [|row];[exact reference_control_member_3003|].
 destruct row as [|row];[exact reference_control_member_3004|].
 destruct row as [|row];[exact reference_control_member_3005|].
 destruct row as [|row];[exact reference_control_member_3006|].
 destruct row as [|row];[exact reference_control_member_3007|].
 destruct row as [|row];[exact reference_control_member_3008|].
 destruct row as [|row];[exact reference_control_member_3009|].
 destruct row as [|row];[exact reference_control_member_3010|].
 destruct row as [|row];[exact reference_control_member_3011|].
 destruct row as [|row];[exact reference_control_member_3012|].
 destruct row as [|row];[exact reference_control_member_3013|].
 destruct row as [|row];[exact reference_control_member_3014|].
 destruct row as [|row];[exact reference_control_member_3015|].
 destruct row as [|row];[exact reference_control_member_3016|].
 destruct row as [|row];[exact reference_control_member_3017|].
 destruct row as [|row];[exact reference_control_member_3018|].
 destruct row as [|row];[exact reference_control_member_3019|].
 destruct row as [|row];[exact reference_control_member_3020|].
 destruct row as [|row];[exact reference_control_member_3021|].
 destruct row as [|row];[exact reference_control_member_3022|].
 destruct row as [|row];[exact reference_control_member_3023|].
 destruct row as [|row];[exact reference_control_member_3024|].
 destruct row as [|row];[exact reference_control_member_3025|].
 destruct row as [|row];[exact reference_control_member_3026|].
 destruct row as [|row];[exact reference_control_member_3027|].
 destruct row as [|row];[exact reference_control_member_3028|].
 destruct row as [|row];[exact reference_control_member_3029|].
 destruct row as [|row];[exact reference_control_member_3030|].
 destruct row as [|row];[exact reference_control_member_3031|].
 destruct row as [|row];[exact reference_control_member_3032|].
 destruct row as [|row];[exact reference_control_member_3033|].
 destruct row as [|row];[exact reference_control_member_3034|].
 destruct row as [|row];[exact reference_control_member_3035|].
 destruct row as [|row];[exact reference_control_member_3036|].
 destruct row as [|row];[exact reference_control_member_3037|].
 destruct row as [|row];[exact reference_control_member_3038|].
 destruct row as [|row];[exact reference_control_member_3039|].
 destruct row as [|row];[exact reference_control_member_3040|].
 lia.
Qed.
Lemma reference_illegal_step row guards invalid old result :
 (row < 48)%coq_nat ->
 VM.find (reference_instruction_guard row) old = Some (Gval (Fuint 1) [::guards row]) ->
 (row <> 0%nat -> VM.find (2992+N.of_nat row) old = Some (Gval (Fuint 1) [::reference_illegal_fold guards row])) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (2993+N.of_nat row) result = Some (Gval (Fuint 1) [::reference_illegal_fold guards (S row)]).
Proof.
 intros Bound Guard Previous Step.
 eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes _ (reference_illegal_expression row));
 [exact reference_control_3_positions|exact reference_control_3_safety|apply reference_illegal_member;exact Bound| |exact Step].
 intros site. unfold reference_illegal_expression. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Guard.
 destruct row as [|row].
 - cbn [reference_illegal_fold]. destruct (guards 0%nat);reflexivity.
 - assert (Prev : VM.find (2993+N.of_nat row) old = Some (Gval (Fuint 1) [::reference_illegal_fold guards (S row)])).
   { replace (2993+N.of_nat row) with (2992+N.of_nat (S row)) by lia. apply Previous;discriminate. }
   destruct (guards (S row)) eqn:Choice;cbn;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite Prev;
   cbn [reference_illegal_fold];rewrite Choice;destruct (guards row);reflexivity.
Qed.
Theorem reference_illegal_prefix_history invalid history limit start guards :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall row i, (row < 48)%coq_nat -> (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find (reference_instruction_guard row) (history i) = Some (Gval (Fuint 1) [::guards row])) ->
 forall count, (0 < count)%coq_nat -> (count <= 48)%coq_nat ->
 forall time, (Nat.add start count <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (2992+N.of_nat count) (history time) = Some (Gval (Fuint 1) [::reference_illegal_fold guards count]).
Proof.
 intros Steps Guards count. induction count as [|count IH];intros Positive Bound [|time] Lower Upper;try lia.
 replace (2992+N.of_nat (S count)) with (2993+N.of_nat count) by lia.
 eapply (reference_illegal_step count guards invalid (history time) (history (S time)));[lia|apply Guards;lia| |apply Steps;lia].
 intro Nonzero. apply IH;lia.
Qed.
(* Final illegal output. *)
Theorem reference_illegal_output_history invalid history limit start guards enabled :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall row i, (row < 48)%coq_nat -> (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find (reference_instruction_guard row) (history i) = Some (Gval (Fuint 1) [::guards row])) ->
 (forall i, (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find 1707 (history i) = Some (Gval (Fuint 1) [::enabled])) ->
 forall time, (Nat.add start 50 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 3042 (history time) = Some (Gval (Fuint 1) [::if enabled then reference_illegal_fold guards 48 else false]).
Proof.
 intros Steps Guards Enabled [|[|time]] Lower Upper;try lia.
 pose proof (reference_illegal_prefix_history invalid history limit start guards Steps Guards 48%nat ltac:(lia) ltac:(lia) time ltac:(lia) ltac:(lia)) as Prefix.
 change (VM.find 3040 (history time) = Some (Gval (Fuint 1) [::reference_illegal_fold guards 48])) in Prefix.
 assert (Gate : VM.find 3041 (history (S time)) = Some (Gval (Fuint 1) [::if enabled then reference_illegal_fold guards 48 else false])).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 3041 reference_control_expr_3041);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_3041| |apply Steps;lia].
 intros site. cbn [reference_control_expr_3041 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (Enabled time ltac:(lia) ltac:(lia)). remember (reference_illegal_fold guards 48) as bit in Prefix |- *. destruct enabled,bit;cbn;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite Prefix;reflexivity. }
 eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 3042 reference_control_expr_3042);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_3042| |apply Steps;lia].
 intros site;exact Gate.
Qed.
