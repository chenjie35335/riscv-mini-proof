Require Import CoreSocModel ComparisonNodes FormalGroundNodeEquation SelectedNodeSafety DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates ConcreteDecodeOperations.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition load_imm_word_1306 (instruction:bits) := instruction.
Definition load_imm_word_1307 (instruction:bits) := [::true;false;false].
Definition load_imm_word_1309 (instruction:bits) := (drop 20 (take 32 (load_imm_word_1306 instruction))).
Definition load_imm_word_1310 (instruction:bits) := (load_imm_word_1309 instruction).
Definition load_imm_word_1311 (instruction:bits) := (drop 25 (take 32 (load_imm_word_1306 instruction))).
Definition load_imm_word_1312 (instruction:bits) := (drop 7 (take 12 (load_imm_word_1306 instruction))).
Definition load_imm_word_1313 (instruction:bits) := ((load_imm_word_1312 instruction) ++ (load_imm_word_1311 instruction)).
Definition load_imm_word_1314 (instruction:bits) := (load_imm_word_1313 instruction).
Definition load_imm_word_1315 (instruction:bits) := (drop 31 (take 32 (load_imm_word_1306 instruction))).
Definition load_imm_word_1316 (instruction:bits) := (drop 7 (take 8 (load_imm_word_1306 instruction))).
Definition load_imm_word_1317 (instruction:bits) := (drop 25 (take 31 (load_imm_word_1306 instruction))).
Definition load_imm_word_1318 (instruction:bits) := (drop 8 (take 12 (load_imm_word_1306 instruction))).
Definition load_imm_word_1319 (instruction:bits) := ([::false] ++ (load_imm_word_1318 instruction)).
Definition load_imm_word_1320 (instruction:bits) := ((load_imm_word_1316 instruction) ++ (load_imm_word_1315 instruction)).
Definition load_imm_word_1321 (instruction:bits) := ((load_imm_word_1317 instruction) ++ (load_imm_word_1320 instruction)).
Definition load_imm_word_1322 (instruction:bits) := ((load_imm_word_1319 instruction) ++ (load_imm_word_1321 instruction)).
Definition load_imm_word_1323 (instruction:bits) := (load_imm_word_1322 instruction).
Definition load_imm_word_1324 (instruction:bits) := (drop 12 (take 32 (load_imm_word_1306 instruction))).
Definition load_imm_word_1325 (instruction:bits) := ([::false;false;false;false;false;false;false;false;false;false;false;false] ++ (load_imm_word_1324 instruction)).
Definition load_imm_word_1326 (instruction:bits) := (load_imm_word_1325 instruction).
Definition load_imm_word_1327 (instruction:bits) := (drop 31 (take 32 (load_imm_word_1306 instruction))).
Definition load_imm_word_1328 (instruction:bits) := (drop 12 (take 20 (load_imm_word_1306 instruction))).
Definition load_imm_word_1329 (instruction:bits) := (drop 20 (take 21 (load_imm_word_1306 instruction))).
Definition load_imm_word_1330 (instruction:bits) := (drop 25 (take 31 (load_imm_word_1306 instruction))).
Definition load_imm_word_1331 (instruction:bits) := (drop 21 (take 25 (load_imm_word_1306 instruction))).
Definition load_imm_word_1332 (instruction:bits) := ((load_imm_word_1331 instruction) ++ (load_imm_word_1330 instruction)).
Definition load_imm_word_1333 (instruction:bits) := ([::false] ++ (load_imm_word_1332 instruction)).
Definition load_imm_word_1334 (instruction:bits) := ((load_imm_word_1328 instruction) ++ (load_imm_word_1327 instruction)).
Definition load_imm_word_1335 (instruction:bits) := ((load_imm_word_1329 instruction) ++ (load_imm_word_1334 instruction)).
Definition load_imm_word_1336 (instruction:bits) := ((load_imm_word_1333 instruction) ++ (load_imm_word_1335 instruction)).
Definition load_imm_word_1337 (instruction:bits) := (load_imm_word_1336 instruction).
Definition load_imm_word_1338 (instruction:bits) := (drop 15 (take 20 (load_imm_word_1306 instruction))).
Definition load_imm_word_1339 (instruction:bits) := (zext 1 (load_imm_word_1338 instruction)).
Definition load_imm_word_1340 (instruction:bits) := (andB (load_imm_word_1310 instruction) [::false;true]).
Definition load_imm_word_1341 (instruction:bits) := (load_imm_word_1340 instruction).
Definition load_imm_word_1342 (instruction:bits) := [::true].
Definition load_imm_word_1343 (instruction:bits) := (sext_to 12 (take 12 (load_imm_word_1310 instruction))).
Definition load_imm_word_1344 (instruction:bits) := [::false].
Definition load_imm_word_1345 (instruction:bits) := (sext_to 12 (take 12 (load_imm_word_1343 instruction))).
Definition load_imm_word_1346 (instruction:bits) := [::false].
Definition load_imm_word_1347 (instruction:bits) := (sext_to 13 (take 13 (load_imm_word_1345 instruction))).
Definition load_imm_word_1348 (instruction:bits) := [::false].
Definition load_imm_word_1349 (instruction:bits) := (sext_to 32 (take 32 (load_imm_word_1347 instruction))).
Definition load_imm_word_1350 (instruction:bits) := [::false].
Definition load_imm_word_1351 (instruction:bits) := (sext_to 32 (take 32 (load_imm_word_1349 instruction))).
Definition load_imm_word_1352 (instruction:bits) := [::false].
Definition load_imm_word_1353 (instruction:bits) := (sext_to 32 (take 32 (load_imm_word_1351 instruction))).
Definition load_imm_word_1354 (instruction:bits) := (load_imm_word_1353 instruction).
Definition load_imm_value (node:nat) instruction : hvalue := match node with
| 1306%nat =>Gval(Fuint 32)(load_imm_word_1306 instruction)
| 1307%nat =>Gval(Fuint 3)(load_imm_word_1307 instruction)
| 1309%nat =>Gval(Fuint 12)(load_imm_word_1309 instruction)
| 1310%nat =>Gval(Fsint 12)(load_imm_word_1310 instruction)
| 1311%nat =>Gval(Fuint 7)(load_imm_word_1311 instruction)
| 1312%nat =>Gval(Fuint 5)(load_imm_word_1312 instruction)
| 1313%nat =>Gval(Fuint 12)(load_imm_word_1313 instruction)
| 1314%nat =>Gval(Fsint 12)(load_imm_word_1314 instruction)
| 1315%nat =>Gval(Fuint 1)(load_imm_word_1315 instruction)
| 1316%nat =>Gval(Fuint 1)(load_imm_word_1316 instruction)
| 1317%nat =>Gval(Fuint 6)(load_imm_word_1317 instruction)
| 1318%nat =>Gval(Fuint 4)(load_imm_word_1318 instruction)
| 1319%nat =>Gval(Fuint 5)(load_imm_word_1319 instruction)
| 1320%nat =>Gval(Fuint 2)(load_imm_word_1320 instruction)
| 1321%nat =>Gval(Fuint 8)(load_imm_word_1321 instruction)
| 1322%nat =>Gval(Fuint 13)(load_imm_word_1322 instruction)
| 1323%nat =>Gval(Fsint 13)(load_imm_word_1323 instruction)
| 1324%nat =>Gval(Fuint 20)(load_imm_word_1324 instruction)
| 1325%nat =>Gval(Fuint 32)(load_imm_word_1325 instruction)
| 1326%nat =>Gval(Fsint 32)(load_imm_word_1326 instruction)
| 1327%nat =>Gval(Fuint 1)(load_imm_word_1327 instruction)
| 1328%nat =>Gval(Fuint 8)(load_imm_word_1328 instruction)
| 1329%nat =>Gval(Fuint 1)(load_imm_word_1329 instruction)
| 1330%nat =>Gval(Fuint 6)(load_imm_word_1330 instruction)
| 1331%nat =>Gval(Fuint 4)(load_imm_word_1331 instruction)
| 1332%nat =>Gval(Fuint 10)(load_imm_word_1332 instruction)
| 1333%nat =>Gval(Fuint 11)(load_imm_word_1333 instruction)
| 1334%nat =>Gval(Fuint 9)(load_imm_word_1334 instruction)
| 1335%nat =>Gval(Fuint 10)(load_imm_word_1335 instruction)
| 1336%nat =>Gval(Fuint 21)(load_imm_word_1336 instruction)
| 1337%nat =>Gval(Fsint 21)(load_imm_word_1337 instruction)
| 1338%nat =>Gval(Fuint 5)(load_imm_word_1338 instruction)
| 1339%nat =>Gval(Fsint 6)(load_imm_word_1339 instruction)
| 1340%nat =>Gval(Fuint 12)(load_imm_word_1340 instruction)
| 1341%nat =>Gval(Fsint 12)(load_imm_word_1341 instruction)
| 1342%nat =>Gval(Fuint 1)(load_imm_word_1342 instruction)
| 1343%nat =>Gval(Fsint 12)(load_imm_word_1343 instruction)
| 1344%nat =>Gval(Fuint 1)(load_imm_word_1344 instruction)
| 1345%nat =>Gval(Fsint 12)(load_imm_word_1345 instruction)
| 1346%nat =>Gval(Fuint 1)(load_imm_word_1346 instruction)
| 1347%nat =>Gval(Fsint 13)(load_imm_word_1347 instruction)
| 1348%nat =>Gval(Fuint 1)(load_imm_word_1348 instruction)
| 1349%nat =>Gval(Fsint 32)(load_imm_word_1349 instruction)
| 1350%nat =>Gval(Fuint 1)(load_imm_word_1350 instruction)
| 1351%nat =>Gval(Fsint 32)(load_imm_word_1351 instruction)
| 1352%nat =>Gval(Fuint 1)(load_imm_word_1352 instruction)
| 1353%nat =>Gval(Fsint 32)(load_imm_word_1353 instruction)
| 1354%nat =>Gval(Fuint 32)(load_imm_word_1354 instruction)
| _=>Gval(Fuint 1)[::false] end.
Definition load_imm_rank (node:nat) : nat := match node with
| 1306%nat =>0%nat
| 1307%nat =>0%nat
| 1309%nat =>1%nat
| 1310%nat =>2%nat
| 1311%nat =>1%nat
| 1312%nat =>1%nat
| 1313%nat =>2%nat
| 1314%nat =>3%nat
| 1315%nat =>1%nat
| 1316%nat =>1%nat
| 1317%nat =>1%nat
| 1318%nat =>1%nat
| 1319%nat =>2%nat
| 1320%nat =>2%nat
| 1321%nat =>3%nat
| 1322%nat =>4%nat
| 1323%nat =>5%nat
| 1324%nat =>1%nat
| 1325%nat =>2%nat
| 1326%nat =>3%nat
| 1327%nat =>1%nat
| 1328%nat =>1%nat
| 1329%nat =>1%nat
| 1330%nat =>1%nat
| 1331%nat =>1%nat
| 1332%nat =>2%nat
| 1333%nat =>3%nat
| 1334%nat =>2%nat
| 1335%nat =>3%nat
| 1336%nat =>4%nat
| 1337%nat =>5%nat
| 1338%nat =>1%nat
| 1339%nat =>2%nat
| 1340%nat =>3%nat
| 1341%nat =>4%nat
| 1342%nat =>1%nat
| 1343%nat =>5%nat
| 1344%nat =>1%nat
| 1345%nat =>6%nat
| 1346%nat =>1%nat
| 1347%nat =>7%nat
| 1348%nat =>1%nat
| 1349%nat =>8%nat
| 1350%nat =>1%nat
| 1351%nat =>9%nat
| 1352%nat =>1%nat
| 1353%nat =>10%nat
| 1354%nat =>11%nat
| _=>0%nat end.
Definition load_imm_dependencies (node:nat) : list nat := match node with
| 1309%nat =>[::1306%nat]
| 1310%nat =>[::1309%nat]
| 1311%nat =>[::1306%nat]
| 1312%nat =>[::1306%nat]
| 1313%nat =>[::1311%nat;1312%nat]
| 1314%nat =>[::1313%nat]
| 1315%nat =>[::1306%nat]
| 1316%nat =>[::1306%nat]
| 1317%nat =>[::1306%nat]
| 1318%nat =>[::1306%nat]
| 1319%nat =>[::1318%nat]
| 1320%nat =>[::1315%nat;1316%nat]
| 1321%nat =>[::1320%nat;1317%nat]
| 1322%nat =>[::1321%nat;1319%nat]
| 1323%nat =>[::1322%nat]
| 1324%nat =>[::1306%nat]
| 1325%nat =>[::1324%nat]
| 1326%nat =>[::1325%nat]
| 1327%nat =>[::1306%nat]
| 1328%nat =>[::1306%nat]
| 1329%nat =>[::1306%nat]
| 1330%nat =>[::1306%nat]
| 1331%nat =>[::1306%nat]
| 1332%nat =>[::1330%nat;1331%nat]
| 1333%nat =>[::1332%nat]
| 1334%nat =>[::1327%nat;1328%nat]
| 1335%nat =>[::1334%nat;1329%nat]
| 1336%nat =>[::1335%nat;1333%nat]
| 1337%nat =>[::1336%nat]
| 1338%nat =>[::1306%nat]
| 1339%nat =>[::1338%nat]
| 1340%nat =>[::1310%nat]
| 1341%nat =>[::1340%nat]
| 1342%nat =>[::1307%nat]
| 1343%nat =>[::1342%nat;1310%nat;1341%nat]
| 1344%nat =>[::1307%nat]
| 1345%nat =>[::1344%nat;1314%nat;1343%nat]
| 1346%nat =>[::1307%nat]
| 1347%nat =>[::1346%nat;1323%nat;1345%nat]
| 1348%nat =>[::1307%nat]
| 1349%nat =>[::1348%nat;1326%nat;1347%nat]
| 1350%nat =>[::1307%nat]
| 1351%nat =>[::1350%nat;1337%nat;1349%nat]
| 1352%nat =>[::1307%nat]
| 1353%nat =>[::1352%nat;1339%nat;1351%nat]
| 1354%nat =>[::1353%nat]
| _=>nil end.
Definition load_imm_expr (index:nat) := nth (@Econst VarOrder.T(Fuint 1)[::false]) [::address_expr_1309;address_expr_1310;address_expr_1311;address_expr_1312;address_expr_1313;address_expr_1314;address_expr_1315;address_expr_1316;address_expr_1317;address_expr_1318;address_expr_1319;address_expr_1320;address_expr_1321;address_expr_1322;address_expr_1323;address_expr_1324;address_expr_1325;address_expr_1326;address_expr_1327;address_expr_1328;address_expr_1329;address_expr_1330;address_expr_1331;address_expr_1332;address_expr_1333;address_expr_1334;address_expr_1335;address_expr_1336;address_expr_1337;address_expr_1338;address_expr_1339;address_expr_1340;address_expr_1341;address_expr_1342;address_expr_1343;address_expr_1344;address_expr_1345;address_expr_1346;address_expr_1347;address_expr_1348;address_expr_1349;address_expr_1350;address_expr_1351;address_expr_1352;address_expr_1353;address_expr_1354] index.
Lemma load_imm_member index : (index<46)%coq_nat -> List.In(N.of_nat(1309+index)%nat,load_imm_expr index)data_address_expected_nodes.
Proof. intro Bound. apply(List.nth_error_In data_address_expected_nodes(76+index)%nat).
 do 46(destruct index as[|index];[vm_compute;reflexivity|]);lia. Qed.
Lemma load_imm_step index invalid old result instruction : (index<46)%coq_nat ->
 (forall dep,List.In dep(load_imm_dependencies(1309+index)%nat) -> VM.find(N.of_nat dep)old=Some(load_imm_value dep instruction)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(N.of_nat(1309+index)%nat)result=Some(load_imm_value(1309+index)%nat instruction).
Proof.
 intros Bound Values Step.
 destruct(selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe(load_imm_member index Bound))as[count[tail[Position[Safe Nonreg]]]].
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1309 old old=Some(load_imm_value 1309 instruction)).
 cbn [address_expr_1309 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1309%nat ltac:(vm_compute;tauto))as H1309.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1310 old old=Some(load_imm_value 1310 instruction)).
 cbn [address_expr_1310 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1309.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1311 old old=Some(load_imm_value 1311 instruction)).
 cbn [address_expr_1311 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1312 old old=Some(load_imm_value 1312 instruction)).
 cbn [address_expr_1312 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1311%nat ltac:(vm_compute;tauto))as H1311.
 pose proof(Values 1312%nat ltac:(vm_compute;tauto))as H1312.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1313 old old=Some(load_imm_value 1313 instruction)).
 cbn [address_expr_1313 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1311 H1312.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1313%nat ltac:(vm_compute;tauto))as H1313.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1314 old old=Some(load_imm_value 1314 instruction)).
 cbn [address_expr_1314 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1313.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1315 old old=Some(load_imm_value 1315 instruction)).
 cbn [address_expr_1315 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1316 old old=Some(load_imm_value 1316 instruction)).
 cbn [address_expr_1316 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1317 old old=Some(load_imm_value 1317 instruction)).
 cbn [address_expr_1317 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1318 old old=Some(load_imm_value 1318 instruction)).
 cbn [address_expr_1318 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1318%nat ltac:(vm_compute;tauto))as H1318.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1319 old old=Some(load_imm_value 1319 instruction)).
 cbn [address_expr_1319 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1318.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1315%nat ltac:(vm_compute;tauto))as H1315.
 pose proof(Values 1316%nat ltac:(vm_compute;tauto))as H1316.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1320 old old=Some(load_imm_value 1320 instruction)).
 cbn [address_expr_1320 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1315 H1316.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1320%nat ltac:(vm_compute;tauto))as H1320.
 pose proof(Values 1317%nat ltac:(vm_compute;tauto))as H1317.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1321 old old=Some(load_imm_value 1321 instruction)).
 cbn [address_expr_1321 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1320 H1317.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1321%nat ltac:(vm_compute;tauto))as H1321.
 pose proof(Values 1319%nat ltac:(vm_compute;tauto))as H1319.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1322 old old=Some(load_imm_value 1322 instruction)).
 cbn [address_expr_1322 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1321 H1319.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1322%nat ltac:(vm_compute;tauto))as H1322.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1323 old old=Some(load_imm_value 1323 instruction)).
 cbn [address_expr_1323 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1322.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1324 old old=Some(load_imm_value 1324 instruction)).
 cbn [address_expr_1324 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1324%nat ltac:(vm_compute;tauto))as H1324.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1325 old old=Some(load_imm_value 1325 instruction)).
 cbn [address_expr_1325 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1324.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1325%nat ltac:(vm_compute;tauto))as H1325.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1326 old old=Some(load_imm_value 1326 instruction)).
 cbn [address_expr_1326 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1325.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1327 old old=Some(load_imm_value 1327 instruction)).
 cbn [address_expr_1327 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1328 old old=Some(load_imm_value 1328 instruction)).
 cbn [address_expr_1328 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1329 old old=Some(load_imm_value 1329 instruction)).
 cbn [address_expr_1329 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1330 old old=Some(load_imm_value 1330 instruction)).
 cbn [address_expr_1330 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1331 old old=Some(load_imm_value 1331 instruction)).
 cbn [address_expr_1331 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1330%nat ltac:(vm_compute;tauto))as H1330.
 pose proof(Values 1331%nat ltac:(vm_compute;tauto))as H1331.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1332 old old=Some(load_imm_value 1332 instruction)).
 cbn [address_expr_1332 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1330 H1331.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1332%nat ltac:(vm_compute;tauto))as H1332.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1333 old old=Some(load_imm_value 1333 instruction)).
 cbn [address_expr_1333 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1332.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1327%nat ltac:(vm_compute;tauto))as H1327.
 pose proof(Values 1328%nat ltac:(vm_compute;tauto))as H1328.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1334 old old=Some(load_imm_value 1334 instruction)).
 cbn [address_expr_1334 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1327 H1328.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1334%nat ltac:(vm_compute;tauto))as H1334.
 pose proof(Values 1329%nat ltac:(vm_compute;tauto))as H1329.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1335 old old=Some(load_imm_value 1335 instruction)).
 cbn [address_expr_1335 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1334 H1329.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1335%nat ltac:(vm_compute;tauto))as H1335.
 pose proof(Values 1333%nat ltac:(vm_compute;tauto))as H1333.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1336 old old=Some(load_imm_value 1336 instruction)).
 cbn [address_expr_1336 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1335 H1333.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1336%nat ltac:(vm_compute;tauto))as H1336.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1337 old old=Some(load_imm_value 1337 instruction)).
 cbn [address_expr_1337 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1336.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1306%nat ltac:(vm_compute;tauto))as H1306.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1338 old old=Some(load_imm_value 1338 instruction)).
 cbn [address_expr_1338 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1306.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1338%nat ltac:(vm_compute;tauto))as H1338.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1339 old old=Some(load_imm_value 1339 instruction)).
 cbn [address_expr_1339 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1338.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1310%nat ltac:(vm_compute;tauto))as H1310.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1340 old old=Some(load_imm_value 1340 instruction)).
 cbn [address_expr_1340 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1310.
 cbn [load_imm_value].
 unfold eval_binop. cbn [eval_binop_basic].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1340%nat ltac:(vm_compute;tauto))as H1340.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1341 old old=Some(load_imm_value 1341 instruction)).
 cbn [address_expr_1341 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1340.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1342 old old=Some(load_imm_value 1342 instruction)).
 cbn [address_expr_1342 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1307.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1342%nat ltac:(vm_compute;tauto))as H1342.
 pose proof(Values 1310%nat ltac:(vm_compute;tauto))as H1310.
 pose proof(Values 1341%nat ltac:(vm_compute;tauto))as H1341.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1343 old old=Some(load_imm_value 1343 instruction)).
 cbn [address_expr_1343 eval_hfexpr_validif_policy eval_href_validif_policy].
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
 rewrite H1342 H1310 H1341.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1344 old old=Some(load_imm_value 1344 instruction)).
 cbn [address_expr_1344 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1307.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1344%nat ltac:(vm_compute;tauto))as H1344.
 pose proof(Values 1314%nat ltac:(vm_compute;tauto))as H1314.
 pose proof(Values 1343%nat ltac:(vm_compute;tauto))as H1343.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1345 old old=Some(load_imm_value 1345 instruction)).
 cbn [address_expr_1345 eval_hfexpr_validif_policy eval_href_validif_policy].
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
 rewrite H1344 H1314 H1343.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1346 old old=Some(load_imm_value 1346 instruction)).
 cbn [address_expr_1346 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1307.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1346%nat ltac:(vm_compute;tauto))as H1346.
 pose proof(Values 1323%nat ltac:(vm_compute;tauto))as H1323.
 pose proof(Values 1345%nat ltac:(vm_compute;tauto))as H1345.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1347 old old=Some(load_imm_value 1347 instruction)).
 cbn [address_expr_1347 eval_hfexpr_validif_policy eval_href_validif_policy].
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
 rewrite H1346 H1323 H1345.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1348 old old=Some(load_imm_value 1348 instruction)).
 cbn [address_expr_1348 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1307.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1348%nat ltac:(vm_compute;tauto))as H1348.
 pose proof(Values 1326%nat ltac:(vm_compute;tauto))as H1326.
 pose proof(Values 1347%nat ltac:(vm_compute;tauto))as H1347.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1349 old old=Some(load_imm_value 1349 instruction)).
 cbn [address_expr_1349 eval_hfexpr_validif_policy eval_href_validif_policy].
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
 rewrite H1348 H1326 H1347.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1350 old old=Some(load_imm_value 1350 instruction)).
 cbn [address_expr_1350 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1307.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1350%nat ltac:(vm_compute;tauto))as H1350.
 pose proof(Values 1337%nat ltac:(vm_compute;tauto))as H1337.
 pose proof(Values 1349%nat ltac:(vm_compute;tauto))as H1349.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1351 old old=Some(load_imm_value 1351 instruction)).
 cbn [address_expr_1351 eval_hfexpr_validif_policy eval_href_validif_policy].
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
 rewrite H1350 H1337 H1349.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1352 old old=Some(load_imm_value 1352 instruction)).
 cbn [address_expr_1352 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1307.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1352%nat ltac:(vm_compute;tauto))as H1352.
 pose proof(Values 1339%nat ltac:(vm_compute;tauto))as H1339.
 pose proof(Values 1351%nat ltac:(vm_compute;tauto))as H1351.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1353 old old=Some(load_imm_value 1353 instruction)).
 cbn [address_expr_1353 eval_hfexpr_validif_policy eval_href_validif_policy].
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
 rewrite H1352 H1339 H1351.
 cbn [load_imm_value].
 reflexivity. }
 destruct index as[|index].
 {
 pose proof(Values 1353%nat ltac:(vm_compute;tauto))as H1353.
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1354 old old=Some(load_imm_value 1354 instruction)).
 cbn [address_expr_1354 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1353.
 cbn [load_imm_value].
 reflexivity. }
 lia. Qed.
(* Semantic composition. *)
Lemma load_imm_rank_positive index : (index<46)%coq_nat -> (0<load_imm_rank(1309+index)%nat)%coq_nat.
Proof. intro Bound. do 46(destruct index as[|index];[vm_compute;lia|]);lia. Qed.
Lemma load_imm_dependency_rank index dep : (index<46)%coq_nat ->List.In dep(load_imm_dependencies(1309+index)%nat) ->
 dep=1306%nat \/dep=1307%nat \/exists prior,(prior<46)%coq_nat /\dep=(1309+prior)%nat /\(load_imm_rank dep<load_imm_rank(1309+index)%nat)%coq_nat.
Proof. intros Bound.
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 0%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 2%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 3%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 4%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 9%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 6%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 7%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 11%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 8%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 12%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 10%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 13%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 15%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 16%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 21%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 22%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 23%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 18%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 19%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 25%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 20%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 26%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 24%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 27%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 29%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 1%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 31%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 33%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 1%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 32%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 35%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 5%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 34%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 37%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 14%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 36%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 39%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 17%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 38%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 41%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 28%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 40%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;left. reflexivity. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 43%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 30%nat. vm_compute;repeat split;lia. }
 destruct H as[H|H].
 { subst dep. right;right. exists 42%nat. vm_compute;repeat split;lia. }
 contradiction. }
 destruct index as[|index]. { vm_compute. intros H.
 destruct H as[H|H].
 { subst dep. right;right. exists 44%nat. vm_compute;repeat split;lia. }
 contradiction. }
 lia. Qed.
Theorem load_imm_nodes_history invalid history (limit start:nat) instruction :
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1306(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1307(history t)=Some(Gval(Fuint 3)[::true;false;false])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time index,(index<46)%coq_nat ->(Nat.add start(load_imm_rank(1309+index)%nat)<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find(N.of_nat(1309+index)%nat)(history time)=Some(load_imm_value(1309+index)%nat instruction).
Proof.
 intros Instruction Select Steps time. induction time as[|time IH];intros index Bound Lower Upper.
 - pose proof(load_imm_rank_positive index Bound). lia.
 - eapply(load_imm_step index invalid (history time)(history(S time))instruction Bound);[|apply Steps;lia].
   intros dep Member. destruct(load_imm_dependency_rank index dep Bound Member)as[Root|[Root|[prior[Prior[Same Rank]]]]].
   + subst dep. exact(Instruction time ltac:(pose proof(load_imm_rank_positive index Bound);lia) ltac:(lia)).
   + subst dep. exact(Select time ltac:(pose proof(load_imm_rank_positive index Bound);lia) ltac:(lia)).
   + subst dep. apply IH;lia.
Qed.
Definition load_i_immediate instruction := sext_to 32(drop 20(take 32 instruction)).
Lemma load_imm_resize_id word width : size word=width ->sext_to width(take width word)=word.
Proof. intros Size. rewrite -Size take_size. unfold sext_to,sext. rewrite subnn cats0. reflexivity. Qed.
Lemma load_imm_resize_size word width : (size word<=width)%nat ->size(sext_to width(take width word))=width.
Proof. intro Bound. rewrite take_oversize;[|exact Bound]. unfold sext_to. rewrite size_sext. exact(subnKC Bound). Qed.
Lemma load_imm_final_value instruction :size instruction=32%nat ->load_imm_value 1354 instruction=Gval(Fuint 32)(load_i_immediate instruction).
Proof.
 intro Size. cbn [load_imm_value]. unfold load_imm_word_1354,load_imm_word_1353,load_imm_word_1351,load_imm_word_1349,load_imm_word_1347,load_imm_word_1345,load_imm_word_1343,load_imm_word_1310,load_imm_word_1309,load_imm_word_1306.
 assert(Raw:size(drop 20(take 32 instruction))=12%nat)by(rewrite size_drop size_take Size;reflexivity).
 rewrite(load_imm_resize_id _ 12 Raw). rewrite(load_imm_resize_id _ 12 Raw).
 assert(S13:size(sext_to 13(take 13(drop 20(take 32 instruction))))=13%nat).
 { apply load_imm_resize_size. rewrite Raw. reflexivity. }
 assert(S32:size(sext_to 32(take 32(sext_to 13(take 13(drop 20(take 32 instruction))))))=32%nat).
 { apply load_imm_resize_size. rewrite S13. reflexivity. }
 rewrite(load_imm_resize_id _ 32 S32). rewrite(load_imm_resize_id _ 32 S32).
 unfold load_i_immediate. rewrite take_oversize;[|rewrite S13;reflexivity].
 unfold sext_to at 1. rewrite S13.
 rewrite take_oversize;[|rewrite Raw;reflexivity]. unfold sext_to. rewrite Raw sext_sext. reflexivity.
Qed.

Require Import FormalDeclaredConnection DataAddressConnectionCertificates.
Definition load_imm_wire_target index : VarOrder.T := match index with O=>1306|S O=>1307|_=>1308 end.
Definition load_imm_wire_source index : VarOrder.T := match index with O=>7748|S O=>88|_=>1354 end.
Definition load_imm_wire_width index : nat := match index with S O=>3|_=>32 end.
Lemma load_imm_wire_step index invalid old result word : (index<3)%coq_nat ->size word=load_imm_wire_width index ->
 VM.find(load_imm_wire_source index)old=Some(Gval(Fuint(load_imm_wire_width index))word) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(load_imm_wire_target index)result=Some(Gval(Fuint(load_imm_wire_width index))word).
Proof.
 intros Bound Size Source Step. destruct index as[|[|[|index]]];try lia;cbn [load_imm_wire_target load_imm_wire_source load_imm_wire_width] in *.
 - eapply declared_connection_value;[exact data_address_connection_1306_position|exact data_address_connection_1306_split|exact data_address_connection_1306_straight|exact data_address_connection_1306_mid_safe|exact data_address_connection_1306_tail_safe|exact data_address_connection_1306_nonregister|reflexivity|exact Source| |exact Step].
   change(Some(Gval(Fuint 32%nat)(zext_to 32%nat(take 32%nat word)))=Some(Gval(Fuint 32%nat)word)). rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
 - eapply declared_connection_value;[exact data_address_connection_1307_position|exact data_address_connection_1307_split|exact data_address_connection_1307_straight|exact data_address_connection_1307_mid_safe|exact data_address_connection_1307_tail_safe|exact data_address_connection_1307_nonregister|reflexivity|exact Source| |exact Step].
   change(Some(Gval(Fuint 3%nat)(zext_to 3%nat(take 3%nat word)))=Some(Gval(Fuint 3%nat)word)). rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
 - eapply declared_connection_value;[exact data_address_connection_1308_position|exact data_address_connection_1308_split|exact data_address_connection_1308_straight|exact data_address_connection_1308_mid_safe|exact data_address_connection_1308_tail_safe|exact data_address_connection_1308_nonregister|reflexivity|exact Source| |exact Step].
   change(Some(Gval(Fuint 32%nat)(zext_to 32%nat(take 32%nat word)))=Some(Gval(Fuint 32%nat)word)). rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Lemma load_i_immediate_size instruction :size instruction=32%nat ->size(load_i_immediate instruction)=32%nat.
Proof. intro Size. unfold load_i_immediate,sext_to. rewrite size_sext size_drop size_take Size. reflexivity. Qed.
Theorem load_imm_selected_history invalid history (limit start:nat) instruction :size instruction=32%nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1306(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1307(history t)=Some(Gval(Fuint 3)[::true;false;false])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(Nat.add start 12<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1308(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Size Instruction Select Steps time Lower Upper. destruct time as[|time];[lia|].
 eapply(load_imm_wire_step 2 invalid (history time)(history(S time))(load_i_immediate instruction));[lia|exact(load_i_immediate_size instruction Size)| |apply Steps;lia].
 pose proof(load_imm_nodes_history invalid history limit start instruction Instruction Select Steps time 45 ltac:(lia) ltac:(change(Nat.add start 11<=time)%coq_nat;lia) ltac:(lia))as Value.
 change(VM.find 1354(history time)=Some(load_imm_value 1354 instruction))in Value.
 rewrite(load_imm_final_value instruction Size)in Value. exact Value.
Qed.
Theorem load_imm_from_front_history invalid history (limit start:nat) instruction :size instruction=32%nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7748(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 88(history t)=Some(Gval(Fuint 3)[::true;false;false])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(Nat.add start 13<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1308(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Size Front Select Steps time Lower Upper.
 eapply(load_imm_selected_history invalid history limit(S start)instruction Size);[| |exact Steps|lia|exact Upper].
 - intros t L U. destruct t as[|t];[lia|]. eapply(load_imm_wire_step 0 invalid(history t)(history(S t))instruction);[lia|exact Size|apply Front;lia|apply Steps;lia].
 - intros t L U. destruct t as[|t];[lia|]. eapply(load_imm_wire_step 1 invalid(history t)(history(S t))[::true;false;false]);[lia|reflexivity|apply Select;lia|apply Steps;lia].
Qed.
Require Import JointBoundaryRegisters JointUpdateBoundaryHistory.
Lemma load_imm_front_member : List.In(7748%nat,32%nat)joint_boundary_registers.
Proof. apply(List.nth_error_In joint_boundary_registers 53%nat). vm_compute;reflexivity. Qed.
Theorem load_imm_front_register_history invalid history (limit start:nat) instruction :size instruction=32%nat ->
 VM.find 7748(history 0%nat)=Some(Gval(Fuint 32)instruction) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 88(history t)=Some(Gval(Fuint 3)[::true;false;false])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(Nat.add start 13<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1308(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Size Front Select Steps. eapply(load_imm_from_front_history invalid history limit start instruction Size);[|exact Select|exact Steps].
 intros t Lower Upper. rewrite(joint_update_register_history_same invalid history limit 7748 32 load_imm_front_member Steps t Upper). exact Front.
Qed.
