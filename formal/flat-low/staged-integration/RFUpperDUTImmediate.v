Require Import RFUpperSemantics.
Require Import CoreSocModel ComparisonNodes LoadImmediateSemantics FormalGroundNodeEquation SelectedNodeSafety DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates ConcreteDecodeOperations.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Modes 0,1,2,3 denote I,S,B,J respectively. *)
Definition rf_upper_dut_imm_selector mode : bits := from_N 3 (nth 1 [::3] mode).
Definition rf_upper_dut_imm_mode_word_1342 (mode:nat) (instruction:bits) := [::false].
Definition rf_upper_dut_imm_mode_word_1343 (mode:nat) (instruction:bits) := (sext_to 12 (take 12 (if hd false (rf_upper_dut_imm_mode_word_1342 mode instruction) then (load_imm_word_1310 instruction) else (load_imm_word_1341 instruction)))).
Definition rf_upper_dut_imm_mode_word_1344 (mode:nat) (instruction:bits) := [::false].
Definition rf_upper_dut_imm_mode_word_1345 (mode:nat) (instruction:bits) := (sext_to 12 (take 12 (if hd false (rf_upper_dut_imm_mode_word_1344 mode instruction) then (load_imm_word_1314 instruction) else (rf_upper_dut_imm_mode_word_1343 mode instruction)))).
Definition rf_upper_dut_imm_mode_word_1346 (mode:nat) (instruction:bits) := [::false].
Definition rf_upper_dut_imm_mode_word_1347 (mode:nat) (instruction:bits) := (sext_to 13 (take 13 (if hd false (rf_upper_dut_imm_mode_word_1346 mode instruction) then (load_imm_word_1323 instruction) else (rf_upper_dut_imm_mode_word_1345 mode instruction)))).
Definition rf_upper_dut_imm_mode_word_1348 (mode:nat) (instruction:bits) := [::true].
Definition rf_upper_dut_imm_mode_word_1349 (mode:nat) (instruction:bits) := (sext_to 32 (take 32 (if hd false (rf_upper_dut_imm_mode_word_1348 mode instruction) then (load_imm_word_1326 instruction) else (rf_upper_dut_imm_mode_word_1347 mode instruction)))).
Definition rf_upper_dut_imm_mode_word_1350 (mode:nat) (instruction:bits) := [::false].
Definition rf_upper_dut_imm_mode_word_1351 (mode:nat) (instruction:bits) := (sext_to 32 (take 32 (if hd false (rf_upper_dut_imm_mode_word_1350 mode instruction) then (load_imm_word_1337 instruction) else (rf_upper_dut_imm_mode_word_1349 mode instruction)))).
Definition rf_upper_dut_imm_mode_word_1352 (mode:nat) (instruction:bits) := [::false].
Definition rf_upper_dut_imm_mode_word_1353 (mode:nat) (instruction:bits) := (sext_to 32 (take 32 (if hd false (rf_upper_dut_imm_mode_word_1352 mode instruction) then (load_imm_word_1339 instruction) else (rf_upper_dut_imm_mode_word_1351 mode instruction)))).
Definition rf_upper_dut_imm_mode_word_1354 (mode:nat) (instruction:bits) := (rf_upper_dut_imm_mode_word_1353 mode instruction).
Definition rf_upper_dut_imm_value mode (node:nat) instruction : hvalue := match node with
| 1307%nat => Gval(Fuint 3)(rf_upper_dut_imm_selector mode)
| 1342%nat =>Gval(Fuint 1)(rf_upper_dut_imm_mode_word_1342 mode instruction)
| 1343%nat =>Gval(Fsint 12)(rf_upper_dut_imm_mode_word_1343 mode instruction)
| 1344%nat =>Gval(Fuint 1)(rf_upper_dut_imm_mode_word_1344 mode instruction)
| 1345%nat =>Gval(Fsint 12)(rf_upper_dut_imm_mode_word_1345 mode instruction)
| 1346%nat =>Gval(Fuint 1)(rf_upper_dut_imm_mode_word_1346 mode instruction)
| 1347%nat =>Gval(Fsint 13)(rf_upper_dut_imm_mode_word_1347 mode instruction)
| 1348%nat =>Gval(Fuint 1)(rf_upper_dut_imm_mode_word_1348 mode instruction)
| 1349%nat =>Gval(Fsint 32)(rf_upper_dut_imm_mode_word_1349 mode instruction)
| 1350%nat =>Gval(Fuint 1)(rf_upper_dut_imm_mode_word_1350 mode instruction)
| 1351%nat =>Gval(Fsint 32)(rf_upper_dut_imm_mode_word_1351 mode instruction)
| 1352%nat =>Gval(Fuint 1)(rf_upper_dut_imm_mode_word_1352 mode instruction)
| 1353%nat =>Gval(Fsint 32)(rf_upper_dut_imm_mode_word_1353 mode instruction)
| 1354%nat =>Gval(Fuint 32)(rf_upper_dut_imm_mode_word_1354 mode instruction)
| _ =>load_imm_value node instruction end.
Lemma rf_upper_dut_imm_prefix_value mode index instruction : (index<33)%coq_nat ->
 rf_upper_dut_imm_value mode (1309+index)%nat instruction = load_imm_value (1309+index)%nat instruction.
Proof. intro Bound;do 33(destruct index as[|index];[reflexivity|]);lia. Qed.
Lemma rf_upper_dut_imm_prefix_no_selector index : (index<33)%coq_nat ->
 ~ List.In 1307%nat (load_imm_dependencies(1309+index)%nat).
Proof. intro Bound;do 33(destruct index as[|index];[vm_compute;intuition discriminate|]);lia. Qed.
Lemma rf_upper_dut_imm_prefix_dependencies_below index : (index<33)%coq_nat ->
 List.forallb (fun dep => Nat.ltb dep 1342) (load_imm_dependencies(1309+index)%nat) = true.
Proof. intro Bound;do 33(destruct index as[|index];[vm_compute;reflexivity|]);lia. Qed.
Lemma rf_upper_dut_imm_prefix_dependency mode index instruction dep : (index<33)%coq_nat ->
 List.In dep(load_imm_dependencies(1309+index)%nat) -> rf_upper_dut_imm_value mode dep instruction = load_imm_value dep instruction.
Proof.
 intros Bound Member.
 destruct(load_imm_dependency_rank index dep ltac:(lia) Member)as[Root|[Root|[prior[Prior[Same Rank]]]]].
 - subst dep;reflexivity.
 - subst dep;exfalso;exact(rf_upper_dut_imm_prefix_no_selector index Bound Member).
 - pose proof(rf_upper_dut_imm_prefix_dependencies_below index Bound)as Below.
   rewrite List.forallb_forall in Below;specialize(Below dep Member);apply Nat.ltb_lt in Below.
   subst dep;apply rf_upper_dut_imm_prefix_value;change (Nat.add 1309 prior < 1342)%coq_nat in Below;lia.
Qed.
Lemma rf_upper_dut_imm_step mode index invalid old result instruction : (mode<1)%coq_nat -> (index<46)%coq_nat ->
 (forall dep,List.In dep(load_imm_dependencies(1309+index)%nat) -> VM.find(N.of_nat dep)old=Some(rf_upper_dut_imm_value mode dep instruction)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(N.of_nat(1309+index)%nat)result=Some(rf_upper_dut_imm_value mode (1309+index)%nat instruction).
Proof.
 intros Mode Bound Values Step.
 destruct (lt_dec index 33) as [Prefix|Suffix].
 - rewrite (rf_upper_dut_imm_prefix_value mode index instruction Prefix).
   apply (load_imm_step index invalid old result instruction Bound);[|exact Step].
   intros dep Member;specialize(Values dep Member);rewrite (rf_upper_dut_imm_prefix_dependency mode index instruction dep Prefix Member) in Values;exact Values.
 - destruct(selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe(load_imm_member index Bound))as[count[tail[Position[Safe Nonreg]]]].
   do 33 (destruct index as [|index];[lia|]).
   destruct index as[|index].
   {
    pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1342 old old=Some(rf_upper_dut_imm_value mode 1342 instruction)).
    cbn [address_expr_1342 eval_hfexpr_validif_policy eval_href_validif_policy].
    rewrite H1307.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1342%nat ltac:(vm_compute;tauto))as H1342.
    pose proof(Values 1310%nat ltac:(vm_compute;tauto))as H1310.
    pose proof(Values 1341%nat ltac:(vm_compute;tauto))as H1341.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1343 old old=Some(rf_upper_dut_imm_value mode 1343 instruction)).
    cbn [address_expr_1343 eval_hfexpr_validif_policy eval_href_validif_policy].
    unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
    rewrite H1342 H1310 H1341.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1344 old old=Some(rf_upper_dut_imm_value mode 1344 instruction)).
    cbn [address_expr_1344 eval_hfexpr_validif_policy eval_href_validif_policy].
    rewrite H1307.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1344%nat ltac:(vm_compute;tauto))as H1344.
    pose proof(Values 1314%nat ltac:(vm_compute;tauto))as H1314.
    pose proof(Values 1343%nat ltac:(vm_compute;tauto))as H1343.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1345 old old=Some(rf_upper_dut_imm_value mode 1345 instruction)).
    cbn [address_expr_1345 eval_hfexpr_validif_policy eval_href_validif_policy].
    unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
    rewrite H1344 H1314 H1343.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1346 old old=Some(rf_upper_dut_imm_value mode 1346 instruction)).
    cbn [address_expr_1346 eval_hfexpr_validif_policy eval_href_validif_policy].
    rewrite H1307.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1346%nat ltac:(vm_compute;tauto))as H1346.
    pose proof(Values 1323%nat ltac:(vm_compute;tauto))as H1323.
    pose proof(Values 1345%nat ltac:(vm_compute;tauto))as H1345.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1347 old old=Some(rf_upper_dut_imm_value mode 1347 instruction)).
    cbn [address_expr_1347 eval_hfexpr_validif_policy eval_href_validif_policy].
    unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
    rewrite H1346 H1323 H1345.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1348 old old=Some(rf_upper_dut_imm_value mode 1348 instruction)).
    cbn [address_expr_1348 eval_hfexpr_validif_policy eval_href_validif_policy].
    rewrite H1307.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1348%nat ltac:(vm_compute;tauto))as H1348.
    pose proof(Values 1326%nat ltac:(vm_compute;tauto))as H1326.
    pose proof(Values 1347%nat ltac:(vm_compute;tauto))as H1347.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1349 old old=Some(rf_upper_dut_imm_value mode 1349 instruction)).
    cbn [address_expr_1349 eval_hfexpr_validif_policy eval_href_validif_policy].
    unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
    rewrite H1348 H1326 H1347.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1350 old old=Some(rf_upper_dut_imm_value mode 1350 instruction)).
    cbn [address_expr_1350 eval_hfexpr_validif_policy eval_href_validif_policy].
    rewrite H1307.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1350%nat ltac:(vm_compute;tauto))as H1350.
    pose proof(Values 1337%nat ltac:(vm_compute;tauto))as H1337.
    pose proof(Values 1349%nat ltac:(vm_compute;tauto))as H1349.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1351 old old=Some(rf_upper_dut_imm_value mode 1351 instruction)).
    cbn [address_expr_1351 eval_hfexpr_validif_policy eval_href_validif_policy].
    unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
    rewrite H1350 H1337 H1349.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1307%nat ltac:(vm_compute;tauto))as H1307.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1352 old old=Some(rf_upper_dut_imm_value mode 1352 instruction)).
    cbn [address_expr_1352 eval_hfexpr_validif_policy eval_href_validif_policy].
    rewrite H1307.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1352%nat ltac:(vm_compute;tauto))as H1352.
    pose proof(Values 1339%nat ltac:(vm_compute;tauto))as H1339.
    pose proof(Values 1351%nat ltac:(vm_compute;tauto))as H1351.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1353 old old=Some(rf_upper_dut_imm_value mode 1353 instruction)).
    cbn [address_expr_1353 eval_hfexpr_validif_policy eval_href_validif_policy].
    unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref].
    rewrite H1352 H1339 H1351.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   destruct index as[|index].
   {
    pose proof(Values 1353%nat ltac:(vm_compute;tauto))as H1353.
    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_1354 old old=Some(rf_upper_dut_imm_value mode 1354 instruction)).
    cbn [address_expr_1354 eval_hfexpr_validif_policy eval_href_validif_policy].
    rewrite H1353.
    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }
   lia.
Qed.
(* Shared mode composition. *)
Theorem rf_upper_dut_imm_nodes_history mode invalid history (limit start:nat) instruction :
 (mode<1)%coq_nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1306(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1307(history t)=Some(Gval(Fuint 3)(rf_upper_dut_imm_selector mode))) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time index,(index<46)%coq_nat ->(Nat.add start(load_imm_rank(1309+index)%nat)<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find(N.of_nat(1309+index)%nat)(history time)=Some(rf_upper_dut_imm_value mode (1309+index)%nat instruction).
Proof.
 intros Mode Instruction Select Steps time. induction time as[|time IH];intros index Bound Lower Upper.
 - pose proof(load_imm_rank_positive index Bound);lia.
 - eapply(rf_upper_dut_imm_step mode index invalid (history time)(history(S time))instruction Mode Bound);[|apply Steps;lia].
   intros dep Member. destruct(load_imm_dependency_rank index dep Bound Member)as[Root|[Root|[prior[Prior[Same Rank]]]]].
   + subst dep. exact(Instruction time ltac:(pose proof(load_imm_rank_positive index Bound);lia) ltac:(lia)).
   + subst dep. exact(Select time ltac:(pose proof(load_imm_rank_positive index Bound);lia) ltac:(lia)).
   + subst dep. apply IH;lia.
Qed.
Definition rf_upper_dut_imm_result (mode:nat) instruction :=rf_upper_immediate instruction.
Lemma rf_upper_dut_imm_result_size mode instruction :(mode<1)%coq_nat ->size instruction=32%nat ->size(rf_upper_dut_imm_result mode instruction)=32%nat.
Proof. intros Mode Size. exact(rf_upper_immediate_size instruction Size). Qed.
Lemma rf_upper_dut_imm_final_value mode instruction :(mode<1)%coq_nat ->size instruction=32%nat ->
 rf_upper_dut_imm_value mode 1354 instruction=Gval(Fuint 32)(rf_upper_dut_imm_result mode instruction).
Proof.
 intros Mode Size. destruct mode as[|mode];[|lia].
 change(Gval(Fuint 32)(rf_upper_dut_imm_mode_word_1354 0 instruction)=Gval(Fuint 32)(rf_upper_immediate instruction)).
 unfold rf_upper_dut_imm_mode_word_1354,rf_upper_dut_imm_mode_word_1353,rf_upper_dut_imm_mode_word_1352,rf_upper_dut_imm_mode_word_1351,rf_upper_dut_imm_mode_word_1350,rf_upper_dut_imm_mode_word_1349,rf_upper_dut_imm_mode_word_1348.
 cbn[nth hd]. change(load_imm_word_1326 instruction)with(rf_upper_immediate instruction).
 rewrite !(load_imm_resize_id _ 32 (rf_upper_immediate_size instruction Size)). reflexivity.
Qed.
Theorem rf_upper_dut_imm_selected_history mode invalid history (limit start:nat) instruction :
 (mode<1)%coq_nat ->size instruction=32%nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1306(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1307(history t)=Some(Gval(Fuint 3)(rf_upper_dut_imm_selector mode))) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(Nat.add start 12<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1308(history time)=Some(Gval(Fuint 32)(rf_upper_dut_imm_result mode instruction)).
Proof.
 intros Mode Size Instruction Select Steps time Lower Upper. destruct time as[|time];[lia|].
 eapply(load_imm_wire_step 2 invalid (history time)(history(S time))(rf_upper_dut_imm_result mode instruction));[lia|exact(rf_upper_dut_imm_result_size mode instruction Mode Size)| |apply Steps;lia].
 pose proof(rf_upper_dut_imm_nodes_history mode invalid history limit start instruction Mode Instruction Select Steps time 45 ltac:(lia) ltac:(change(Nat.add start 11<=time)%coq_nat;lia) ltac:(lia))as Value.
 change(VM.find 1354(history time)=Some(rf_upper_dut_imm_value mode 1354 instruction))in Value.
 rewrite(rf_upper_dut_imm_final_value mode instruction Mode Size)in Value;exact Value.
Qed.
Theorem rf_upper_dut_imm_from_front_history mode invalid history (limit start:nat) instruction :
 (mode<1)%coq_nat ->size instruction=32%nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7748(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 88(history t)=Some(Gval(Fuint 3)(rf_upper_dut_imm_selector mode))) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(Nat.add start 13<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1308(history time)=Some(Gval(Fuint 32)(rf_upper_dut_imm_result mode instruction)).
Proof.
 intros Mode Size Front Select Steps time Lower Upper.
 eapply(rf_upper_dut_imm_selected_history mode invalid history limit(S start)instruction Mode Size);[| |exact Steps|lia|exact Upper].
 - intros t L U. destruct t as[|t];[lia|]. eapply(load_imm_wire_step 0 invalid(history t)(history(S t))instruction);[lia|exact Size|apply Front;lia|apply Steps;lia].
 - intros t L U. destruct t as[|t];[lia|]. eapply(load_imm_wire_step 1 invalid(history t)(history(S t))(rf_upper_dut_imm_selector mode));[lia|unfold rf_upper_dut_imm_selector;rewrite size_from_N;reflexivity|apply Select;lia|apply Steps;lia].
Qed.
Require Import FormalObservedHistory FormalLocalHistory JointUpdateBoundaryHistory JointBoundaryRegisters LoadExecuteControl.
Theorem rf_upper_dut_imm_observed mode memory inputs k observed instruction :
 (mode<1)%coq_nat -> generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->size instruction=32%nat ->
 VM.find 88(top_environment observed)=Some(Gval(Fuint 3)(rf_upper_dut_imm_selector mode)) ->
 VM.find 1308(top_environment observed)=Some(Gval(Fuint 32)(rf_upper_dut_imm_result mode instruction)).
Proof.
 intros Mode Observe Legal Front Size Select.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(FrontLast:VM.find 7748(history 9259%nat)=Some(Gval(Fuint 32)instruction))by(rewrite Last;exact Front).
 pose proof(load_execute_decode_history (generated_observation_input inputs k) nil history 9259 instruction 2 ltac:(lia) Steps FrontLast Size 9259 ltac:(vm_compute;lia) (le_n _))as Decode.
 change(VM.find 88(history 9259%nat)=Some(Gval(Fuint 3)(load_execute_decode 2(to_N instruction)49)))in Decode.
 rewrite Last Select in Decode.
 pose proof(f_equal(fun value => match value with Some(Gval _ bits) => bits | _ => [::] end)Decode)as Match.
 change(rf_upper_dut_imm_selector mode=load_execute_decode 2(to_N instruction)49)in Match; symmetry in Match.
 rewrite <-Last.
 eapply(rf_upper_dut_imm_from_front_history mode (formal_invalid_policy (generated_observation_input inputs k) nil) history 9259 55 instruction Mode Size);[| |exact Steps|vm_compute;lia|exact(le_n _) ].
 - intros time Lower Upper.
   rewrite(joint_update_register_history_same _ history 9259 7748 32 load_imm_front_member Steps time Upper).
   rewrite <-(joint_update_register_history_same _ history 9259 7748 32 load_imm_front_member Steps 9259 (le_n _));exact FrontLast.
 - intros time Lower Upper.
   pose proof(load_execute_decode_history (generated_observation_input inputs k) nil history 9259 instruction 2 ltac:(lia) Steps FrontLast Size time Lower Upper)as Value.
   change(VM.find 88(history time)=Some(Gval(Fuint 3)(load_execute_decode 2(to_N instruction)49)))in Value.
   rewrite Match in Value;exact Value.
Qed.
