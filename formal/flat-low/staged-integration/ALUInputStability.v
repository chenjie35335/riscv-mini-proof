Require Import CoreSocModel ComparisonNodes DataAddressPositionCertificate DataAddressSafetyCertificate
 DataAddressOutputCertificates DataAddressExpressionCertificates DataAddressConnectionCertificates
 ReferenceControlNodeGeneric ReferenceControlGroundExpressions ReferenceControlGroundOperations
 SelectedNodeSafety FormalDeclaredConnectionCongruence X0DependencyRanks DependencyRankSoundness.
From Coq Require Import NArith ZArith List Lia Arith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition alu_stability_ground env node := exists ground bits, VM.find (N.of_nat node) env = Some (Gval ground bits).
Definition alu_stability_roots : seq nat := [::86%nat;87%nat;88%nat;89%nat;7748%nat;7749%nat;7816%nat;7819%nat].
Definition alu_stability_table : list (nat * (nat * list nat)) := [::
(86%nat,(0%nat,[::]));
(87%nat,(0%nat,[::]));
(88%nat,(0%nat,[::]));
(89%nat,(0%nat,[::]));
(7748%nat,(0%nat,[::]));
(7749%nat,(0%nat,[::]));
(7816%nat,(0%nat,[::]));
(7819%nat,(0%nat,[::]));
(1306%nat,(1%nat,[::7748%nat]));
(1309%nat,(2%nat,[::1306%nat]));
(1311%nat,(2%nat,[::1306%nat]));
(1312%nat,(2%nat,[::1306%nat]));
(1315%nat,(2%nat,[::1306%nat]));
(1316%nat,(2%nat,[::1306%nat]));
(1317%nat,(2%nat,[::1306%nat]));
(1318%nat,(2%nat,[::1306%nat]));
(1324%nat,(2%nat,[::1306%nat]));
(1327%nat,(2%nat,[::1306%nat]));
(1328%nat,(2%nat,[::1306%nat]));
(1329%nat,(2%nat,[::1306%nat]));
(1330%nat,(2%nat,[::1306%nat]));
(1331%nat,(2%nat,[::1306%nat]));
(1338%nat,(2%nat,[::1306%nat]));
(1310%nat,(3%nat,[::1309%nat]));
(1313%nat,(3%nat,[::1311%nat;1312%nat]));
(1319%nat,(3%nat,[::1318%nat]));
(1320%nat,(3%nat,[::1315%nat;1316%nat]));
(1325%nat,(3%nat,[::1324%nat]));
(1332%nat,(3%nat,[::1330%nat;1331%nat]));
(1334%nat,(3%nat,[::1327%nat;1328%nat]));
(1339%nat,(3%nat,[::1338%nat]));
(1314%nat,(4%nat,[::1313%nat]));
(1321%nat,(4%nat,[::1317%nat;1320%nat]));
(1326%nat,(4%nat,[::1325%nat]));
(1333%nat,(4%nat,[::1332%nat]));
(1335%nat,(4%nat,[::1329%nat;1334%nat]));
(1340%nat,(4%nat,[::1310%nat]));
(1322%nat,(5%nat,[::1319%nat;1321%nat]));
(1336%nat,(5%nat,[::1333%nat;1335%nat]));
(1341%nat,(5%nat,[::1340%nat]));
(1323%nat,(6%nat,[::1322%nat]));
(1337%nat,(6%nat,[::1336%nat]));
(1153%nat,(56%nat,[::89%nat]));
(1307%nat,(56%nat,[::88%nat]));
(7820%nat,(56%nat,[::86%nat]));
(7822%nat,(56%nat,[::87%nat]));
(1156%nat,(57%nat,[::1153%nat]));
(1342%nat,(57%nat,[::1307%nat]));
(1344%nat,(57%nat,[::1307%nat]));
(1346%nat,(57%nat,[::1307%nat]));
(1348%nat,(57%nat,[::1307%nat]));
(1350%nat,(57%nat,[::1307%nat]));
(1352%nat,(57%nat,[::1307%nat]));
(7821%nat,(57%nat,[::7749%nat;7816%nat;7820%nat]));
(1151%nat,(58%nat,[::7821%nat]));
(1343%nat,(58%nat,[::1310%nat;1341%nat;1342%nat]));
(1345%nat,(59%nat,[::1314%nat;1343%nat;1344%nat]));
(1347%nat,(60%nat,[::1323%nat;1345%nat;1346%nat]));
(1349%nat,(61%nat,[::1326%nat;1347%nat;1348%nat]));
(1351%nat,(62%nat,[::1337%nat;1349%nat;1350%nat]));
(1353%nat,(63%nat,[::1339%nat;1351%nat;1352%nat]));
(1354%nat,(64%nat,[::1353%nat]));
(1308%nat,(65%nat,[::1354%nat]));
(7823%nat,(66%nat,[::1308%nat;7819%nat;7822%nat]));
(1152%nat,(67%nat,[::7823%nat]));
(1157%nat,(68%nat,[::1152%nat]));
(1158%nat,(69%nat,[::1157%nat]));
(1159%nat,(70%nat,[::1152%nat;1156%nat;1158%nat]));
(1160%nat,(71%nat,[::1151%nat;1159%nat]));
(1161%nat,(72%nat,[::1160%nat]));
(1155%nat,(73%nat,[::1161%nat]))].
Lemma alu_stability_ranks : dependency_ranks_valid alu_stability_table = true.
Proof. vm_compute;reflexivity. Qed.
Theorem alu_stability_transfer_batch inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 List.Forall (fun entry => let '(node,(rank,deps)) := entry in (0 < rank)%coq_nat ->
 (forall source, List.In source deps -> alu_stability_ground left source /\ VM.find (N.of_nat source) left = VM.find (N.of_nat source) right) ->
 alu_stability_ground next_left node /\ VM.find (N.of_nat node) next_left = VM.find (N.of_nat node) next_right) alu_stability_table.
Proof.
 intros Left Right. unfold alu_stability_table.
 constructor. { cbn;intros Positive Sources;lia. }
 constructor. { cbn;intros Positive Sources;lia. }
 constructor. { cbn;intros Positive Sources;lia. }
 constructor. { cbn;intros Positive Sources;lia. }
 constructor. { cbn;intros Positive Sources;lia. }
 constructor. { cbn;intros Positive Sources;lia. }
 constructor. { cbn;intros Positive Sources;lia. }
 constructor. { cbn;intros Positive Sources;lia. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 7748%nat ltac:(cbn;tauto)) as [G7748 E7748].
 split.
 - destruct (data_address_connection_1306_output (formal_invalid_policy inputs path) left left next_left G7748 Left) as [bits Value]. exists (Fuint 32),bits;exact Value.
 - exact (declared_connection_congruence 1383 flat_statements data_address_connection_1306_decl data_address_connection_1306_mid data_address_connection_1306_tail 1306 7748 32 (formal_invalid_policy inputs path) flat_memories left right next_left next_right
 data_address_connection_1306_position data_address_connection_1306_split data_address_connection_1306_straight data_address_connection_1306_mid_safe data_address_connection_1306_tail_safe data_address_connection_1306_nonregister (Logic.eq_refl _) E7748 Left Right). }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1309 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1309 address_expr_1309
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 76%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1309 address_expr_1309 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1309. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1309 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1311 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1311 address_expr_1311
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 78%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1311 address_expr_1311 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1311. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1311 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1312 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1312 address_expr_1312
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 79%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1312 address_expr_1312 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1312. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1312 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1315 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1315 address_expr_1315
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 82%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1315 address_expr_1315 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1315. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1315 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1316 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1316 address_expr_1316
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 83%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1316 address_expr_1316 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1316. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1316 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1317 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1317 address_expr_1317
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 84%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1317 address_expr_1317 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1317. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1317 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1318 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1318 address_expr_1318
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 85%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1318 address_expr_1318 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1318. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1318 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1324 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1324 address_expr_1324
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 91%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1324 address_expr_1324 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1324. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1324 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1327 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1327 address_expr_1327
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 94%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1327 address_expr_1327 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1327. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1327 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1328 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1328 address_expr_1328
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 95%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1328 address_expr_1328 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1328. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1328 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1329 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1329 address_expr_1329
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 96%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1329 address_expr_1329 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1329. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1329 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1330 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1330 address_expr_1330
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 97%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1330 address_expr_1330 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1330. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1330 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1331 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1331 address_expr_1331
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 98%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1331 address_expr_1331 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1331. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1331 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1306%nat ltac:(cbn;tauto)) as [G1306 E1306].
 split.
 - exact (data_address_node_output_1338 inputs path left left next_left G1306 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1338 address_expr_1338
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 105%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1338 address_expr_1338 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1306 as [g1306 [b1306 G1306]].
   unfold address_expr_1338. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1338 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1306. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1309%nat ltac:(cbn;tauto)) as [G1309 E1309].
 split.
 - exact (data_address_node_output_1310 inputs path left left next_left G1309 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1310 address_expr_1310
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 77%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1310 address_expr_1310 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1309 as [g1309 [b1309 G1309]].
   unfold address_expr_1310. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1310 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1309. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1311%nat ltac:(cbn;tauto)) as [G1311 E1311].
 destruct (Sources 1312%nat ltac:(cbn;tauto)) as [G1312 E1312].
 split.
 - exact (data_address_node_output_1313 inputs path left left next_left G1311 G1312 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1313 address_expr_1313
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 80%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1313 address_expr_1313 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1311 as [g1311 [b1311 G1311]].
   destruct G1312 as [g1312 [b1312 G1312]].
   unfold address_expr_1313. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1313 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1311 E1312. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1318%nat ltac:(cbn;tauto)) as [G1318 E1318].
 split.
 - exact (data_address_node_output_1319 inputs path left left next_left G1318 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1319 address_expr_1319
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 86%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1319 address_expr_1319 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1318 as [g1318 [b1318 G1318]].
   unfold address_expr_1319. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1319 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1318. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1315%nat ltac:(cbn;tauto)) as [G1315 E1315].
 destruct (Sources 1316%nat ltac:(cbn;tauto)) as [G1316 E1316].
 split.
 - exact (data_address_node_output_1320 inputs path left left next_left G1315 G1316 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1320 address_expr_1320
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 87%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1320 address_expr_1320 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1315 as [g1315 [b1315 G1315]].
   destruct G1316 as [g1316 [b1316 G1316]].
   unfold address_expr_1320. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1320 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1315 E1316. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1324%nat ltac:(cbn;tauto)) as [G1324 E1324].
 split.
 - exact (data_address_node_output_1325 inputs path left left next_left G1324 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1325 address_expr_1325
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 92%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1325 address_expr_1325 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1324 as [g1324 [b1324 G1324]].
   unfold address_expr_1325. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1325 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1324. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1330%nat ltac:(cbn;tauto)) as [G1330 E1330].
 destruct (Sources 1331%nat ltac:(cbn;tauto)) as [G1331 E1331].
 split.
 - exact (data_address_node_output_1332 inputs path left left next_left G1330 G1331 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1332 address_expr_1332
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 99%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1332 address_expr_1332 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1330 as [g1330 [b1330 G1330]].
   destruct G1331 as [g1331 [b1331 G1331]].
   unfold address_expr_1332. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1332 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1330 E1331. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1327%nat ltac:(cbn;tauto)) as [G1327 E1327].
 destruct (Sources 1328%nat ltac:(cbn;tauto)) as [G1328 E1328].
 split.
 - exact (data_address_node_output_1334 inputs path left left next_left G1327 G1328 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1334 address_expr_1334
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 101%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1334 address_expr_1334 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1327 as [g1327 [b1327 G1327]].
   destruct G1328 as [g1328 [b1328 G1328]].
   unfold address_expr_1334. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1334 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1327 E1328. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1338%nat ltac:(cbn;tauto)) as [G1338 E1338].
 split.
 - exact (data_address_node_output_1339 inputs path left left next_left G1338 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1339 address_expr_1339
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 106%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1339 address_expr_1339 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1338 as [g1338 [b1338 G1338]].
   unfold address_expr_1339. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1339 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1338. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1313%nat ltac:(cbn;tauto)) as [G1313 E1313].
 split.
 - exact (data_address_node_output_1314 inputs path left left next_left G1313 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1314 address_expr_1314
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 81%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1314 address_expr_1314 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1313 as [g1313 [b1313 G1313]].
   unfold address_expr_1314. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1314 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1313. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1317%nat ltac:(cbn;tauto)) as [G1317 E1317].
 destruct (Sources 1320%nat ltac:(cbn;tauto)) as [G1320 E1320].
 split.
 - exact (data_address_node_output_1321 inputs path left left next_left G1317 G1320 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1321 address_expr_1321
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 88%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1321 address_expr_1321 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1317 as [g1317 [b1317 G1317]].
   destruct G1320 as [g1320 [b1320 G1320]].
   unfold address_expr_1321. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1321 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1317 E1320. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1325%nat ltac:(cbn;tauto)) as [G1325 E1325].
 split.
 - exact (data_address_node_output_1326 inputs path left left next_left G1325 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1326 address_expr_1326
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 93%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1326 address_expr_1326 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1325 as [g1325 [b1325 G1325]].
   unfold address_expr_1326. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1326 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1325. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1332%nat ltac:(cbn;tauto)) as [G1332 E1332].
 split.
 - exact (data_address_node_output_1333 inputs path left left next_left G1332 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1333 address_expr_1333
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 100%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1333 address_expr_1333 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1332 as [g1332 [b1332 G1332]].
   unfold address_expr_1333. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1333 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1332. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1329%nat ltac:(cbn;tauto)) as [G1329 E1329].
 destruct (Sources 1334%nat ltac:(cbn;tauto)) as [G1334 E1334].
 split.
 - exact (data_address_node_output_1335 inputs path left left next_left G1329 G1334 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1335 address_expr_1335
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 102%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1335 address_expr_1335 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1329 as [g1329 [b1329 G1329]].
   destruct G1334 as [g1334 [b1334 G1334]].
   unfold address_expr_1335. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1335 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1329 E1334. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1310%nat ltac:(cbn;tauto)) as [G1310 E1310].
 split.
 - exact (data_address_node_output_1340 inputs path left left next_left G1310 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1340 address_expr_1340
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 107%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1340 address_expr_1340 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1310 as [g1310 [b1310 G1310]].
   unfold address_expr_1340. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1340 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1310. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1319%nat ltac:(cbn;tauto)) as [G1319 E1319].
 destruct (Sources 1321%nat ltac:(cbn;tauto)) as [G1321 E1321].
 split.
 - exact (data_address_node_output_1322 inputs path left left next_left G1319 G1321 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1322 address_expr_1322
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 89%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1322 address_expr_1322 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1319 as [g1319 [b1319 G1319]].
   destruct G1321 as [g1321 [b1321 G1321]].
   unfold address_expr_1322. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1322 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1319 E1321. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1333%nat ltac:(cbn;tauto)) as [G1333 E1333].
 destruct (Sources 1335%nat ltac:(cbn;tauto)) as [G1335 E1335].
 split.
 - exact (data_address_node_output_1336 inputs path left left next_left G1333 G1335 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1336 address_expr_1336
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 103%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1336 address_expr_1336 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1333 as [g1333 [b1333 G1333]].
   destruct G1335 as [g1335 [b1335 G1335]].
   unfold address_expr_1336. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1336 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1333 E1335. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1340%nat ltac:(cbn;tauto)) as [G1340 E1340].
 split.
 - exact (data_address_node_output_1341 inputs path left left next_left G1340 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1341 address_expr_1341
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 108%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1341 address_expr_1341 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1340 as [g1340 [b1340 G1340]].
   unfold address_expr_1341. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1341 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1340. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1322%nat ltac:(cbn;tauto)) as [G1322 E1322].
 split.
 - exact (data_address_node_output_1323 inputs path left left next_left G1322 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1323 address_expr_1323
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 90%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1323 address_expr_1323 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1322 as [g1322 [b1322 G1322]].
   unfold address_expr_1323. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1323 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1322. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1336%nat ltac:(cbn;tauto)) as [G1336 E1336].
 split.
 - exact (data_address_node_output_1337 inputs path left left next_left G1336 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1337 address_expr_1337
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 104%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1337 address_expr_1337 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1336 as [g1336 [b1336 G1336]].
   unfold address_expr_1337. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1337 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1336. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 89%nat ltac:(cbn;tauto)) as [G89 E89].
 split.
 - destruct (data_address_connection_1153_output (formal_invalid_policy inputs path) left left next_left G89 Left) as [bits Value]. exists (Fuint 4),bits;exact Value.
 - exact (declared_connection_congruence 1228 flat_statements data_address_connection_1153_decl data_address_connection_1153_mid data_address_connection_1153_tail 1153 89 4 (formal_invalid_policy inputs path) flat_memories left right next_left next_right
 data_address_connection_1153_position data_address_connection_1153_split data_address_connection_1153_straight data_address_connection_1153_mid_safe data_address_connection_1153_tail_safe data_address_connection_1153_nonregister (Logic.eq_refl _) E89 Left Right). }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 88%nat ltac:(cbn;tauto)) as [G88 E88].
 split.
 - destruct (data_address_connection_1307_output (formal_invalid_policy inputs path) left left next_left G88 Left) as [bits Value]. exists (Fuint 3),bits;exact Value.
 - exact (declared_connection_congruence 1384 flat_statements data_address_connection_1307_decl data_address_connection_1307_mid data_address_connection_1307_tail 1307 88 3 (formal_invalid_policy inputs path) flat_memories left right next_left next_right
 data_address_connection_1307_position data_address_connection_1307_split data_address_connection_1307_straight data_address_connection_1307_mid_safe data_address_connection_1307_tail_safe data_address_connection_1307_nonregister (Logic.eq_refl _) E88 Left Right). }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 86%nat ltac:(cbn;tauto)) as [G86 E86].
 split.
 - exact (data_address_node_output_7820 inputs path left left next_left G86 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 7820 address_expr_7820
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 142%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 7820 address_expr_7820 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G86 as [g86 [b86 G86]].
   unfold address_expr_7820. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_7820 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E86. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 87%nat ltac:(cbn;tauto)) as [G87 E87].
 split.
 - exact (data_address_node_output_7822 inputs path left left next_left G87 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 7822 address_expr_7822
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 144%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 7822 address_expr_7822 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G87 as [g87 [b87 G87]].
   unfold address_expr_7822. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_7822 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E87. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1153%nat ltac:(cbn;tauto)) as [G1153 E1153].
 split.
 - exact (data_address_node_output_1156 inputs path left left next_left G1153 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1156 address_expr_1156
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 70%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1156 address_expr_1156 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1153 as [g1153 [b1153 G1153]].
   unfold address_expr_1156. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1156 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1153. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1307%nat ltac:(cbn;tauto)) as [G1307 E1307].
 split.
 - exact (data_address_node_output_1342 inputs path left left next_left G1307 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1342 address_expr_1342
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 109%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1342 address_expr_1342 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1307 as [g1307 [b1307 G1307]].
   unfold address_expr_1342. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1342 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1307. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1307%nat ltac:(cbn;tauto)) as [G1307 E1307].
 split.
 - exact (data_address_node_output_1344 inputs path left left next_left G1307 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1344 address_expr_1344
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 111%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1344 address_expr_1344 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1307 as [g1307 [b1307 G1307]].
   unfold address_expr_1344. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1344 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1307. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1307%nat ltac:(cbn;tauto)) as [G1307 E1307].
 split.
 - exact (data_address_node_output_1346 inputs path left left next_left G1307 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1346 address_expr_1346
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 113%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1346 address_expr_1346 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1307 as [g1307 [b1307 G1307]].
   unfold address_expr_1346. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1346 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1307. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1307%nat ltac:(cbn;tauto)) as [G1307 E1307].
 split.
 - exact (data_address_node_output_1348 inputs path left left next_left G1307 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1348 address_expr_1348
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 115%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1348 address_expr_1348 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1307 as [g1307 [b1307 G1307]].
   unfold address_expr_1348. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1348 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1307. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1307%nat ltac:(cbn;tauto)) as [G1307 E1307].
 split.
 - exact (data_address_node_output_1350 inputs path left left next_left G1307 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1350 address_expr_1350
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 117%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1350 address_expr_1350 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1307 as [g1307 [b1307 G1307]].
   unfold address_expr_1350. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1350 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1307. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1307%nat ltac:(cbn;tauto)) as [G1307 E1307].
 split.
 - exact (data_address_node_output_1352 inputs path left left next_left G1307 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1352 address_expr_1352
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 119%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1352 address_expr_1352 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1307 as [g1307 [b1307 G1307]].
   unfold address_expr_1352. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1352 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1307. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 7749%nat ltac:(cbn;tauto)) as [G7749 E7749].
 destruct (Sources 7816%nat ltac:(cbn;tauto)) as [G7816 E7816].
 destruct (Sources 7820%nat ltac:(cbn;tauto)) as [G7820 E7820].
 split.
 - exact (data_address_node_output_7821 inputs path left left next_left G7749 G7816 G7820 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 7821 address_expr_7821
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 143%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 7821 address_expr_7821 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G7749 as [g7749 [b7749 G7749]].
   destruct G7816 as [g7816 [b7816 G7816]].
   destruct G7820 as [g7820 [b7820 G7820]].
   unfold address_expr_7821. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_7821 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E7749 E7816 E7820. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 7821%nat ltac:(cbn;tauto)) as [G7821 E7821].
 split.
 - destruct (data_address_connection_1151_output (formal_invalid_policy inputs path) left left next_left G7821 Left) as [bits Value]. exists (Fuint 32),bits;exact Value.
 - exact (declared_connection_congruence 1226 flat_statements data_address_connection_1151_decl data_address_connection_1151_mid data_address_connection_1151_tail 1151 7821 32 (formal_invalid_policy inputs path) flat_memories left right next_left next_right
 data_address_connection_1151_position data_address_connection_1151_split data_address_connection_1151_straight data_address_connection_1151_mid_safe data_address_connection_1151_tail_safe data_address_connection_1151_nonregister (Logic.eq_refl _) E7821 Left Right). }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1310%nat ltac:(cbn;tauto)) as [G1310 E1310].
 destruct (Sources 1341%nat ltac:(cbn;tauto)) as [G1341 E1341].
 destruct (Sources 1342%nat ltac:(cbn;tauto)) as [G1342 E1342].
 split.
 - exact (data_address_node_output_1343 inputs path left left next_left G1310 G1341 G1342 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1343 address_expr_1343
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 110%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1343 address_expr_1343 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1310 as [g1310 [b1310 G1310]].
   destruct G1341 as [g1341 [b1341 G1341]].
   destruct G1342 as [g1342 [b1342 G1342]].
   unfold address_expr_1343. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1343 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1310 E1341 E1342. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1314%nat ltac:(cbn;tauto)) as [G1314 E1314].
 destruct (Sources 1343%nat ltac:(cbn;tauto)) as [G1343 E1343].
 destruct (Sources 1344%nat ltac:(cbn;tauto)) as [G1344 E1344].
 split.
 - exact (data_address_node_output_1345 inputs path left left next_left G1314 G1343 G1344 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1345 address_expr_1345
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 112%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1345 address_expr_1345 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1314 as [g1314 [b1314 G1314]].
   destruct G1343 as [g1343 [b1343 G1343]].
   destruct G1344 as [g1344 [b1344 G1344]].
   unfold address_expr_1345. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1345 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1314 E1343 E1344. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1323%nat ltac:(cbn;tauto)) as [G1323 E1323].
 destruct (Sources 1345%nat ltac:(cbn;tauto)) as [G1345 E1345].
 destruct (Sources 1346%nat ltac:(cbn;tauto)) as [G1346 E1346].
 split.
 - exact (data_address_node_output_1347 inputs path left left next_left G1323 G1345 G1346 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1347 address_expr_1347
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 114%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1347 address_expr_1347 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1323 as [g1323 [b1323 G1323]].
   destruct G1345 as [g1345 [b1345 G1345]].
   destruct G1346 as [g1346 [b1346 G1346]].
   unfold address_expr_1347. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1347 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1323 E1345 E1346. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1326%nat ltac:(cbn;tauto)) as [G1326 E1326].
 destruct (Sources 1347%nat ltac:(cbn;tauto)) as [G1347 E1347].
 destruct (Sources 1348%nat ltac:(cbn;tauto)) as [G1348 E1348].
 split.
 - exact (data_address_node_output_1349 inputs path left left next_left G1326 G1347 G1348 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1349 address_expr_1349
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 116%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1349 address_expr_1349 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1326 as [g1326 [b1326 G1326]].
   destruct G1347 as [g1347 [b1347 G1347]].
   destruct G1348 as [g1348 [b1348 G1348]].
   unfold address_expr_1349. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1349 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1326 E1347 E1348. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1337%nat ltac:(cbn;tauto)) as [G1337 E1337].
 destruct (Sources 1349%nat ltac:(cbn;tauto)) as [G1349 E1349].
 destruct (Sources 1350%nat ltac:(cbn;tauto)) as [G1350 E1350].
 split.
 - exact (data_address_node_output_1351 inputs path left left next_left G1337 G1349 G1350 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1351 address_expr_1351
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 118%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1351 address_expr_1351 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1337 as [g1337 [b1337 G1337]].
   destruct G1349 as [g1349 [b1349 G1349]].
   destruct G1350 as [g1350 [b1350 G1350]].
   unfold address_expr_1351. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1351 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1337 E1349 E1350. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1339%nat ltac:(cbn;tauto)) as [G1339 E1339].
 destruct (Sources 1351%nat ltac:(cbn;tauto)) as [G1351 E1351].
 destruct (Sources 1352%nat ltac:(cbn;tauto)) as [G1352 E1352].
 split.
 - exact (data_address_node_output_1353 inputs path left left next_left G1339 G1351 G1352 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1353 address_expr_1353
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 120%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1353 address_expr_1353 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1339 as [g1339 [b1339 G1339]].
   destruct G1351 as [g1351 [b1351 G1351]].
   destruct G1352 as [g1352 [b1352 G1352]].
   unfold address_expr_1353. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1353 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1339 E1351 E1352. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1353%nat ltac:(cbn;tauto)) as [G1353 E1353].
 split.
 - exact (data_address_node_output_1354 inputs path left left next_left G1353 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1354 address_expr_1354
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 121%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1354 address_expr_1354 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1353 as [g1353 [b1353 G1353]].
   unfold address_expr_1354. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1354 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1353. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1354%nat ltac:(cbn;tauto)) as [G1354 E1354].
 split.
 - destruct (data_address_connection_1308_output (formal_invalid_policy inputs path) left left next_left G1354 Left) as [bits Value]. exists (Fuint 32),bits;exact Value.
 - exact (declared_connection_congruence 1385 flat_statements data_address_connection_1308_decl data_address_connection_1308_mid data_address_connection_1308_tail 1308 1354 32 (formal_invalid_policy inputs path) flat_memories left right next_left next_right
 data_address_connection_1308_position data_address_connection_1308_split data_address_connection_1308_straight data_address_connection_1308_mid_safe data_address_connection_1308_tail_safe data_address_connection_1308_nonregister (Logic.eq_refl _) E1354 Left Right). }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1308%nat ltac:(cbn;tauto)) as [G1308 E1308].
 destruct (Sources 7819%nat ltac:(cbn;tauto)) as [G7819 E7819].
 destruct (Sources 7822%nat ltac:(cbn;tauto)) as [G7822 E7822].
 split.
 - exact (data_address_node_output_7823 inputs path left left next_left G1308 G7819 G7822 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 7823 address_expr_7823
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 145%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 7823 address_expr_7823 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1308 as [g1308 [b1308 G1308]].
   destruct G7819 as [g7819 [b7819 G7819]].
   destruct G7822 as [g7822 [b7822 G7822]].
   unfold address_expr_7823. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_7823 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1308 E7819 E7822. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 7823%nat ltac:(cbn;tauto)) as [G7823 E7823].
 split.
 - destruct (data_address_connection_1152_output (formal_invalid_policy inputs path) left left next_left G7823 Left) as [bits Value]. exists (Fuint 32),bits;exact Value.
 - exact (declared_connection_congruence 1227 flat_statements data_address_connection_1152_decl data_address_connection_1152_mid data_address_connection_1152_tail 1152 7823 32 (formal_invalid_policy inputs path) flat_memories left right next_left next_right
 data_address_connection_1152_position data_address_connection_1152_split data_address_connection_1152_straight data_address_connection_1152_mid_safe data_address_connection_1152_tail_safe data_address_connection_1152_nonregister (Logic.eq_refl _) E7823 Left Right). }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1152%nat ltac:(cbn;tauto)) as [G1152 E1152].
 split.
 - exact (data_address_node_output_1157 inputs path left left next_left G1152 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1157 address_expr_1157
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 71%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1157 address_expr_1157 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1152 as [g1152 [b1152 G1152]].
   unfold address_expr_1157. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1157 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1152. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1157%nat ltac:(cbn;tauto)) as [G1157 E1157].
 split.
 - exact (data_address_node_output_1158 inputs path left left next_left G1157 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1158 address_expr_1158
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 72%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1158 address_expr_1158 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1157 as [g1157 [b1157 G1157]].
   unfold address_expr_1158. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1158 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1157. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1152%nat ltac:(cbn;tauto)) as [G1152 E1152].
 destruct (Sources 1156%nat ltac:(cbn;tauto)) as [G1156 E1156].
 destruct (Sources 1158%nat ltac:(cbn;tauto)) as [G1158 E1158].
 split.
 - exact (data_address_node_output_1159 inputs path left left next_left G1152 G1156 G1158 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1159 address_expr_1159
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 73%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1159 address_expr_1159 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1152 as [g1152 [b1152 G1152]].
   destruct G1156 as [g1156 [b1156 G1156]].
   destruct G1158 as [g1158 [b1158 G1158]].
   unfold address_expr_1159. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1159 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1152 E1156 E1158. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1151%nat ltac:(cbn;tauto)) as [G1151 E1151].
 destruct (Sources 1159%nat ltac:(cbn;tauto)) as [G1159 E1159].
 split.
 - exact (data_address_node_output_1160 inputs path left left next_left G1151 G1159 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1160 address_expr_1160
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 74%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1160 address_expr_1160 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1151 as [g1151 [b1151 G1151]].
   destruct G1159 as [g1159 [b1159 G1159]].
   unfold address_expr_1160. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1160 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1151 E1159. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1160%nat ltac:(cbn;tauto)) as [G1160 E1160].
 split.
 - exact (data_address_node_output_1161 inputs path left left next_left G1160 Left).
 - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 1161 address_expr_1161
 data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes 75%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].
 eapply (reference_control_node_congruent count tail 1161 address_expr_1161 inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].
 + destruct G1160 as [g1160 [b1160 G1160]].
   unfold address_expr_1161. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].
 + intros site. cbn [address_expr_1161 eval_hfexpr_validif_policy eval_href_validif_policy].
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref].
   rewrite E1160. reflexivity. }
 constructor. { cbn [fst snd]. intros Positive Sources.
 destruct (Sources 1161%nat ltac:(cbn;tauto)) as [G1161 E1161].
 split.
 - destruct (data_address_connection_1155_output (formal_invalid_policy inputs path) left left next_left G1161 Left) as [bits Value]. exists (Fuint 32),bits;exact Value.
 - exact (declared_connection_congruence 1230 flat_statements data_address_connection_1155_decl data_address_connection_1155_mid data_address_connection_1155_tail 1155 1161 32 (formal_invalid_policy inputs path) flat_memories left right next_left next_right
 data_address_connection_1155_position data_address_connection_1155_split data_address_connection_1155_straight data_address_connection_1155_mid_safe data_address_connection_1155_tail_safe data_address_connection_1155_nonregister (Logic.eq_refl _) E1161 Left Right). }
 constructor.
Qed.
(* Stable public history interface. *)
Lemma alu_stability_rank_zero node deps :
 List.In (node,(0%nat,deps)) alu_stability_table -> List.In node alu_stability_roots.
Proof.
 assert (Check : List.forallb (fun entry => negb (Nat.eqb (fst (snd entry)) 0) || List.existsb (Nat.eqb (fst entry)) alu_stability_roots) alu_stability_table = true).
 { vm_compute;reflexivity. }
 rewrite List.forallb_forall in Check. intro Member.
 specialize (Check _ Member). cbn [fst snd Nat.eqb negb orb] in Check.
 apply List.existsb_exists in Check. destruct Check as [source [Source Equal]].
 apply Nat.eqb_eq in Equal. subst source;exact Source.
Qed.
Theorem alu_stability_from_roots inputs path history limit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall node, List.In node alu_stability_roots -> forall t u,
   (55 <= t)%coq_nat -> (55 <= u)%coq_nat -> (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
   alu_stability_ground (history t) node /\ VM.find (N.of_nat node) (history t) = VM.find (N.of_nat node) (history u)) ->
 forall rank node deps, List.In (node,(rank,deps)) alu_stability_table -> forall t u,
 (Nat.add 55 rank <= t)%coq_nat -> (Nat.add 55 rank <= u)%coq_nat -> (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 alu_stability_ground (history t) node /\ VM.find (N.of_nat node) (history t) = VM.find (N.of_nat node) (history u).
Proof.
 intros Steps Roots rank. induction rank as [rank IH] using lt_wf_ind.
 intros node deps Member t u LT LU UT UU. destruct rank as [|rank].
 - apply Roots;[exact (alu_stability_rank_zero node deps Member)|lia|lia|exact UT|exact UU].
 - destruct t as [|t];[lia|]. destruct u as [|u];[lia|].
   pose proof (alu_stability_transfer_batch inputs path (history t) (history u) (history (S t)) (history (S u)) (Steps t ltac:(lia)) (Steps u ltac:(lia))) as Transfers.
   rewrite List.Forall_forall in Transfers. apply (Transfers _ Member);[lia|].
   intros source Edge.
   destruct (dependency_ranks_valid_sound alu_stability_table node (S rank) deps source alu_stability_ranks Member Edge)
   as [sr [sources [Lookup [SM Less]]]].
   exact (IH sr Less source sources SM t u ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
From nbits Require Import NBits.
Require Import LoadExecuteControl EarlyControlStabilityHistory JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization.
Lemma alu_stability_roots_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall node, List.In node alu_stability_roots -> forall t u,
 (55 <= t)%coq_nat -> (55 <= u)%coq_nat -> (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 alu_stability_ground (history t) node /\ VM.find (N.of_nat node) (history t) = VM.find (N.of_nat node) (history u).
Proof.
 intros Boundary Steps node Member t u LT LU UT UU.
 assert (InstructionMember : List.In (7748%nat,32%nat) joint_boundary_registers).
 { apply (List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity. }
 destruct (joint_update_register_history_concrete _ history limit 7748 32 InstructionMember (Boundary _ _ InstructionMember) Steps limit (le_n _)) as [instruction [Size Front]].
 assert (Control : forall which, (which < 4)%coq_nat ->
   (exists ground bits, VM.find (load_execute_wire_target which true) (history t) = Some (Gval ground bits)) /\
   VM.find (load_execute_wire_target which true) (history t) = VM.find (load_execute_wire_target which true) (history u)).
 { intros which Which.
   pose proof (load_execute_decode_history inputs path history limit instruction which Which Steps Front Size) as Value.
   split.
   - exists (Fuint (load_execute_width which)), (load_execute_decode which (to_N instruction) 49). exact (Value t LT UT).
   - rewrite (Value t LT UT) (Value u LU UU);reflexivity. }
 assert (Register : forall reg width, List.In (reg,width) joint_boundary_registers ->
   alu_stability_ground (history t) reg /\ VM.find (N.of_nat reg) (history t) = VM.find (N.of_nat reg) (history u)).
 { intros reg width RM. split.
   - destruct (joint_update_register_history_concrete _ history limit reg width RM (Boundary _ _ RM) Steps t UT) as [bits [BS BV]]. exists (Fuint width),bits;exact BV.
   - rewrite (joint_update_register_history_same _ history limit reg width RM Steps t UT) (joint_update_register_history_same _ history limit reg width RM Steps u UU);reflexivity. }
 unfold alu_stability_roots in Member.
 destruct Member as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|Bad]]]]]]]];try contradiction.
 - exact (Control 0%nat ltac:(lia)).
 - exact (Control 1%nat ltac:(lia)).
 - exact (Control 2%nat ltac:(lia)).
 - exact (Control 3%nat ltac:(lia)).
 - exact (Register 7748%nat 32%nat InstructionMember).
 - apply (Register 7749%nat 32%nat). apply (List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity.
 - split.
   + destruct (early_control_concrete_7816_history inputs path history limit Boundary Steps t ltac:(lia) UT) as [width [bits Value]]. exists (Fuint width),bits;exact Value.
   + apply (early_control_stable_7816_history inputs path history limit Boundary Steps t u);lia.
 - split.
   + destruct (early_control_concrete_7819_history inputs path history limit Boundary Steps t ltac:(lia) UT) as [width [bits Value]]. exists (Fuint width),bits;exact Value.
   + apply (early_control_stable_7819_history inputs path history limit Boundary Steps t u);lia.
Qed.
Definition alu_stability_targets : seq nat := [::1151%nat;1152%nat;1153%nat;1155%nat;1161%nat;1308%nat].
Lemma alu_stability_target_rank node : List.In node alu_stability_targets ->
 exists rank deps, List.In (node,(rank,deps)) alu_stability_table /\ (rank <= 73)%coq_nat.
Proof.
 unfold alu_stability_targets. intros [<-|[<-|[<-|[<-|[<-|[<-|Bad]]]]]];try contradiction.
 - exists 58%nat,[::7821%nat]. split;[apply (List.nth_error_In alu_stability_table 54%nat);vm_compute;reflexivity|lia].
 - exists 67%nat,[::7823%nat]. split;[apply (List.nth_error_In alu_stability_table 64%nat);vm_compute;reflexivity|lia].
 - exists 56%nat,[::89%nat]. split;[apply (List.nth_error_In alu_stability_table 42%nat);vm_compute;reflexivity|lia].
 - exists 73%nat,[::1161%nat]. split;[apply (List.nth_error_In alu_stability_table 70%nat);vm_compute;reflexivity|lia].
 - exists 72%nat,[::1160%nat]. split;[apply (List.nth_error_In alu_stability_table 69%nat);vm_compute;reflexivity|lia].
 - exists 65%nat,[::1354%nat]. split;[apply (List.nth_error_In alu_stability_table 62%nat);vm_compute;reflexivity|lia].
Qed.
Theorem alu_inputs_stable_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall node, List.In node alu_stability_targets -> forall t u,
 (128 <= t)%coq_nat -> (128 <= u)%coq_nat -> (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 alu_stability_ground (history t) node /\ VM.find (N.of_nat node) (history t) = VM.find (N.of_nat node) (history u).
Proof.
 intros Boundary Steps node Target t u LT LU UT UU.
 destruct (alu_stability_target_rank node Target) as [rank [deps [Member Bound]]].
 exact (alu_stability_from_roots inputs path history limit Steps
 (alu_stability_roots_history inputs path history limit Boundary Steps) rank node deps Member t u ltac:(lia) ltac:(lia) UT UU).
Qed.
Require Import FormalLocalHistory ALUOutputTransfer ALUAddressSemantics ReferenceLoadSemantics PipelinePCSuccessor FormalDeclaredConnection ReferenceRedirectSemantics.
Lemma alu_stable_value_at inputs path history node value time :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 List.In node alu_stability_targets -> (128 <= time)%coq_nat -> (time <= 9259)%coq_nat ->
 VM.find (N.of_nat node) (history 9259%nat) = Some value -> VM.find (N.of_nat node) (history time) = Some value.
Proof.
 intros Boundary Steps Member Lower Upper Value.
 rewrite (proj2 (alu_inputs_stable_history inputs path history 9259 Boundary Steps node Member time 9259 Lower ltac:(vm_compute;lia) Upper (le_n _))). exact Value.
Qed.
Theorem alu_add_commit_observed memory inputs k observed next left right :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size right = 32%nat ->
 VM.find 1151 (top_environment observed) = Some (Gval (Fuint 32) left) ->
 VM.find 1152 (top_environment observed) = Some (Gval (Fuint 32) right) ->
 VM.find 1153 (top_environment observed) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 VM.find 7752 (top_environment next) = Some (Gval (Fuint 32) (reference_load_address left right)).
Proof.
 intros Observe Legal Next Reset Size Left Right Mode.
 destruct (alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)
 as [history [Last [Boundary [Steps [Resets Transfer]]]]].
 assert (Values : forall node value time, List.In node alu_stability_targets -> (128 <= time)%coq_nat -> (time <= 9259)%coq_nat ->
 VM.find (N.of_nat node) (top_environment observed) = Some value -> VM.find (N.of_nat node) (history time) = Some value).
 { intros node value time Member Lower Upper Value. apply (alu_stable_value_at _ _ history node value time Boundary Steps Member Lower Upper). rewrite Last;exact Value. }
 apply (Transfer left right Size).
 - apply (Values 1152%nat);[vm_compute;tauto|vm_compute;lia|vm_compute;lia|exact Right].
 - apply (Values 1153%nat);[vm_compute;tauto|vm_compute;lia|vm_compute;lia|exact Mode].
 - apply (Values 1152%nat);[vm_compute;tauto|vm_compute;lia|vm_compute;lia|exact Right].
 - apply (Values 1151%nat);[vm_compute;tauto|vm_compute;lia|vm_compute;lia|exact Left].
 - apply (Values 1153%nat);[vm_compute;tauto|vm_compute;lia|vm_compute;lia|exact Mode].
Qed.
Theorem alu_sum_to_taken_history inputs path history left right :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 size right = 32%nat ->
 VM.find 1151 (history 9259%nat) = Some (Gval (Fuint 32) left) ->
 VM.find 1152 (history 9259%nat) = Some (Gval (Fuint 32) right) ->
 VM.find 1153 (history 9259%nat) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 VM.find 1155 (history 9253%nat) = Some (Gval (Fuint 32) (reference_load_address left right)).
Proof.
 intros Boundary Steps Size Left Right Mode.
 assert (Values : forall node value time, List.In node alu_stability_targets -> (128 <= time)%coq_nat -> (time <= 9259)%coq_nat ->
 VM.find (N.of_nat node) (history 9259%nat) = Some value -> VM.find (N.of_nat node) (history time) = Some value).
 { intros; eapply alu_stable_value_at; eassumption. }
 assert (Sum : VM.find 1161 (history 9255%nat) = Some (Gval (Fuint 32) (reference_load_address left right))).
 { apply (alu_address_add_from_inputs (formal_invalid_policy inputs path) (alu_output_add_window history) left right Size).
   - apply (Values 1152%nat);[vm_compute;tauto|vm_compute;lia|vm_compute;lia|exact Right].
   - apply (Values 1153%nat);[vm_compute;tauto|vm_compute;lia|vm_compute;lia|exact Mode].
   - apply (Values 1152%nat);[vm_compute;tauto|vm_compute;lia|vm_compute;lia|exact Right].
   - apply (Values 1151%nat);[vm_compute;tauto|vm_compute;lia|vm_compute;lia|exact Left].
   - intros i Bound; do 5 (destruct i as [|i];[apply Steps;vm_compute;lia|]);lia. }
 assert (Earlier : VM.find 1161 (history 9252%nat) = Some (Gval (Fuint 32) (reference_load_address left right))).
 { rewrite (proj2 (alu_inputs_stable_history inputs path history 9259 Boundary Steps 1161 ltac:(vm_compute;tauto) 9252 9255 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia))). exact Sum. }
 eapply (declared_connection_value 1230 flat_statements data_address_connection_1155_decl data_address_connection_1155_mid data_address_connection_1155_tail 1155 1161 32 (Gval (Fuint 32) (reference_load_address left right)));
 [exact data_address_connection_1155_position|exact data_address_connection_1155_split|exact data_address_connection_1155_straight|exact data_address_connection_1155_mid_safe|exact data_address_connection_1155_tail_safe|exact data_address_connection_1155_nonregister|reflexivity|exact Earlier| |apply Steps;vm_compute;lia].
 apply reference_redirect_adapt_word. unfold reference_load_address;rewrite size_take size_from_N;reflexivity.
Qed.
Theorem alu_taken_pc_commit_observed memory inputs k observed next left right :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 size right = 32%nat ->
 VM.find 1151 (top_environment observed) = Some (Gval (Fuint 32) left) ->
 VM.find 1152 (top_environment observed) = Some (Gval (Fuint 32) right) ->
 VM.find 1153 (top_environment observed) = Some (Gval (Fuint 4) [::false;false;false;false]) ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7771 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7752 (top_environment next) = Some (Gval (Fuint 32) (reference_load_address left right)) /\
 VM.find 7768 (top_environment next) = Some (Gval (Fuint 33) (pipeline_redirect_target (reference_load_address left right))).
Proof.
 intros Observe Legal Next Reset Size Left Right Mode Taken Eret. split.
 - exact (alu_add_commit_observed memory inputs k observed next left right Observe Legal Next Reset Size Left Right Mode).
 - destruct (pipeline_pc_taken_observed_context memory inputs k observed next Observe Legal Next Reset Taken Eret)
   as [history [Last [Boundary [Steps [Resets Transfer]]]]].
   apply Transfer.
   + unfold reference_load_address;rewrite size_take size_from_N;reflexivity.
   + apply (alu_sum_to_taken_history _ _ history left right Boundary Steps Size); rewrite Last; assumption.
Qed.
