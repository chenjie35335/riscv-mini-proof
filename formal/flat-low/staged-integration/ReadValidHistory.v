Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine RequestEnableNormalized FormalDeclaredWireCheck MemoryRequestWidth.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition read_valid_expr_8005 := (@Eprim_binop VarOrder.T (Bcomp Bgt) (@Eref VarOrder.T (@Eid VarOrder.T 7995)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition read_valid_expr_8006 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition read_valid_expr_8007 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 8005)) (@Eref VarOrder.T (@Eid VarOrder.T 8006))).
Definition read_valid_expr_8073 := (@Eref VarOrder.T (@Eid VarOrder.T 8007)).
Definition read_valid_expr_8074 := (@Eref VarOrder.T (@Eid VarOrder.T 8073)).
Definition read_valid_expr_8198 := (@Eref VarOrder.T (@Eid VarOrder.T 8074)).
Definition read_valid_nodes := [::(8005,read_valid_expr_8005);(8006,read_valid_expr_8006);(8007,read_valid_expr_8007);(8073,read_valid_expr_8073);(8074,read_valid_expr_8074);(8198,read_valid_expr_8198)].
Definition read_valid_offsets := [::8511%nat;0%nat;0%nat;65%nat;0%nat;123%nat].
Lemma read_valid_positions :select_node_offsets read_valid_offsets flat_statements=Some read_valid_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma read_valid_safety :selected_node_safety flat_memories flat_statements read_valid_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem read_valid_history kind invalid history limit start :
 (kind<8)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7995(history t)=Some(Gval(Fuint 6)(from_N 6(memory_request_width false kind)))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 128(history t)=Some(Gval(Fuint 1)[::false])) ->
 forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 1474(history t)=Some(Gval(Fuint 1)[::memory_request_active false kind]).
Proof.
 intros Kind Steps Width Quiet.
 assert(V8005:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8005(history t)=Some(Gval(Fuint 1)[::memory_request_active false kind])).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step read_valid_offsets read_valid_nodes 8005 read_valid_expr_8005);
 [exact read_valid_positions|exact read_valid_safety|apply(List.nth_error_In read_valid_nodes 0%nat);reflexivity| |apply Steps;lia].
 intros site. cbn[read_valid_expr_8005 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Width t ltac:(lia)ltac:(lia)). do 8(destruct kind as[|kind];[reflexivity|]);lia. }
 assert(V8006:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8006(history t)=Some(Gval(Fuint 1)[::true])).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step read_valid_offsets read_valid_nodes 8006 read_valid_expr_8006);
 [exact read_valid_positions|exact read_valid_safety|apply(List.nth_error_In read_valid_nodes 1%nat);reflexivity| |apply Steps;lia].
 intros site. cbn[read_valid_expr_8006 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Quiet t ltac:(lia)ltac:(lia));reflexivity. }
 assert(V8007:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8007(history t)=Some(Gval(Fuint 1)[::memory_request_active false kind])).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step read_valid_offsets read_valid_nodes 8007 read_valid_expr_8007);
 [exact read_valid_positions|exact read_valid_safety|apply(List.nth_error_In read_valid_nodes 2%nat);reflexivity| |apply Steps;lia].
 intros site. cbn[read_valid_expr_8007 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V8005 t ltac:(lia)ltac:(lia))(V8006 t ltac:(lia)ltac:(lia)). destruct(memory_request_active false kind);reflexivity. }
 assert(V8073:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8073(history t)=Some(Gval(Fuint 1)[::memory_request_active false kind])).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step read_valid_offsets read_valid_nodes 8073 read_valid_expr_8073);
 [exact read_valid_positions|exact read_valid_safety|apply(List.nth_error_In read_valid_nodes 3%nat);reflexivity| |apply Steps;lia].
 intros site. cbn[read_valid_expr_8073 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact(V8007 t ltac:(lia)ltac:(lia)). }
 assert(V8074:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8074(history t)=Some(Gval(Fuint 1)[::memory_request_active false kind])).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step read_valid_offsets read_valid_nodes 8074 read_valid_expr_8074);
 [exact read_valid_positions|exact read_valid_safety|apply(List.nth_error_In read_valid_nodes 4%nat);reflexivity| |apply Steps;lia].
 intros site. cbn[read_valid_expr_8074 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact(V8073 t ltac:(lia)ltac:(lia)). }
 assert(V8198:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8198(history t)=Some(Gval(Fuint 1)[::memory_request_active false kind])).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step read_valid_offsets read_valid_nodes 8198 read_valid_expr_8198);
 [exact read_valid_positions|exact read_valid_safety|apply(List.nth_error_In read_valid_nodes 5%nat);reflexivity| |apply Steps;lia].
 intros site. cbn[read_valid_expr_8198 eval_hfexpr_validif_policy eval_href_validif_policy].
 exact(V8074 t ltac:(lia)ltac:(lia)). }
 intros[|t] Lower Upper;try lia. eapply declared_wire_checked_value;
 [exact read_valid_certificate_1474|exact(V8198 t ltac:(lia)ltac:(lia))|reflexivity|exact(Steps t ltac:(lia))].
Qed.
