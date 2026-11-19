Require Import DUTRedirectSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
Local Open Scope N_scope.
(* Priority is source order: LUI, AUIPC, JAL, JALR, six branches,
   then nonbranch integer/load/store/CSR/system instructions. *)
Definition dut_decode_rows : seq (N * N * N * N) := [::
 (127,55,0,0);
 (127,23,0,0);
 (127,111,1,0);
 (28799,103,1,0);
 (28799,99,0,3);
 (28799,4195,0,6);
 (28799,16483,0,2);
 (28799,20579,0,5);
 (28799,24675,0,1);
 (28799,28771,0,4);
 (28799,3,2,0);
 (28799,4099,2,0);
 (28799,8195,2,0);
 (28799,16387,2,0);
 (28799,20483,2,0);
 (28799,35,0,0);
 (28799,4131,0,0);
 (28799,8227,0,0);
 (28799,19,0,0);
 (28799,8211,0,0);
 (28799,12307,0,0);
 (28799,16403,0,0);
 (28799,24595,0,0);
 (28799,28691,0,0);
 (4261441663,4115,0,0);
 (4261441663,20499,0,0);
 (4261441663,1073762323,0,0);
 (4261441663,51,0,0);
 (4261441663,1073741875,0,0);
 (4261441663,4147,0,0);
 (4261441663,8243,0,0);
 (4261441663,12339,0,0);
 (4261441663,16435,0,0);
 (4261441663,20531,0,0);
 (4261441663,1073762355,0,0);
 (4261441663,24627,0,0);
 (4261441663,28723,0,0);
 (4027580415,15,0,0);
 (4294967295,4111,2,0);
 (28799,4211,2,0);
 (28799,8307,2,0);
 (28799,12403,2,0);
 (28799,20595,2,0);
 (28799,24691,2,0);
 (28799,28787,2,0);
 (4294967295,115,0,0);
 (4294967295,1048691,0,0);
 (4294967295,268435571,3,0);
 (4294967295,270532723,0,0)].
Fixpoint dut_decode_priority (instruction : N) (rows : seq (N * N * N * N)) : N * N :=
 match rows with
 | [::] => (0,0)
 | (mask,code,selector,kind)::rest =>
   if N.eqb (N.land instruction mask) code then (selector,kind)
   else dut_decode_priority instruction rest
 end.
Definition dut_decode_function instruction := dut_decode_priority instruction dut_decode_rows.
Lemma dut_decode_priority_projection (test : N * N -> bool) instruction rows :
 test (dut_decode_priority instruction rows) =
 fold_right (fun row tail => let '(mask,code,selector,kind) := row in
  if N.eqb (N.land instruction mask) code then test (selector,kind) else tail)
 (test (0,0)) rows.
Proof.
 induction rows as [|[[[mask code] selector] kind] rest IH]; [reflexivity|].
 cbn [dut_decode_priority fold_right]. destruct (N.eqb (N.land instruction mask) code); [reflexivity|exact IH].
Qed.
Lemma dut_decode_if_same (test value : bool) : (if test then value else value) = value.
Proof. destruct test; reflexivity. Qed.
Theorem dut_decode_controls instruction :
 dut_redirect_controls_match instruction (fst (dut_decode_function instruction)) (snd (dut_decode_function instruction)).
Proof.
 unfold dut_redirect_controls_match. repeat split.
 all: match goal with
 | |- N.eqb (snd (dut_decode_function ?ins)) ?kind = ?rhs =>
   change ((fun pair : N*N => N.eqb (snd pair) kind) (dut_decode_priority ins dut_decode_rows) = rhs)
 | |- N.eqb (fst (dut_decode_function ?ins)) ?kind = ?rhs =>
   change ((fun pair : N*N => N.eqb (fst pair) kind) (dut_decode_priority ins dut_decode_rows) = rhs)
 end;
 rewrite dut_decode_priority_projection;
 cbn [dut_decode_rows fold_right fst snd];
 repeat rewrite dut_decode_if_same;
 assert (Low : N.land (N.land instruction 28799) 127 = N.land instruction 127) by (rewrite <- N.land_assoc; reflexivity);
 repeat match goal with
 | |- context [N.eqb (N.land ?ins ?mask) ?code] => destruct (N.eqb_spec (N.land ins mask) code)
 end; try reflexivity;
 repeat match goal with H : N.land ?ins ?mask = ?code |- _ => rewrite H in Low end;
 vm_compute in Low; congruence.
Qed.

Require Import ReferenceRedirectSpine DataAddressPositionCertificate DataAddressSafetyCertificate
 JointUpdateNodePositions JointUpdateExpressionCertificates CoreSocModel ComparisonNodes.
From nbits Require Import NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Record dut_decode_certificate_row := {
 dd_mask : N; dd_code : N; dd_selector : N; dd_kind : N;
 dd_mask_width : nat; dd_code_width : nat;
 dd_and_index : nat; dd_eq_index : nat; dd_selector_index : nat; dd_kind_index : nat
}.
Definition dut_decode_certificate_rows : seq dut_decode_certificate_row := [::
 {| dd_mask := 127; dd_code := 55; dd_selector := 0; dd_kind := 0; dd_mask_width := 7%nat; dd_code_width := 6%nat; dd_and_index := 149%nat; dd_eq_index := 150%nat; dd_selector_index := 1094%nat; dd_kind_index := 1143%nat |};
 {| dd_mask := 127; dd_code := 23; dd_selector := 0; dd_kind := 0; dd_mask_width := 7%nat; dd_code_width := 5%nat; dd_and_index := 151%nat; dd_eq_index := 152%nat; dd_selector_index := 1093%nat; dd_kind_index := 1142%nat |};
 {| dd_mask := 127; dd_code := 111; dd_selector := 1; dd_kind := 0; dd_mask_width := 7%nat; dd_code_width := 7%nat; dd_and_index := 153%nat; dd_eq_index := 154%nat; dd_selector_index := 1092%nat; dd_kind_index := 1141%nat |};
 {| dd_mask := 28799; dd_code := 103; dd_selector := 1; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 7%nat; dd_and_index := 155%nat; dd_eq_index := 156%nat; dd_selector_index := 1091%nat; dd_kind_index := 1140%nat |};
 {| dd_mask := 28799; dd_code := 99; dd_selector := 0; dd_kind := 3; dd_mask_width := 15%nat; dd_code_width := 7%nat; dd_and_index := 157%nat; dd_eq_index := 158%nat; dd_selector_index := 1090%nat; dd_kind_index := 1139%nat |};
 {| dd_mask := 28799; dd_code := 4195; dd_selector := 0; dd_kind := 6; dd_mask_width := 15%nat; dd_code_width := 13%nat; dd_and_index := 159%nat; dd_eq_index := 160%nat; dd_selector_index := 1089%nat; dd_kind_index := 1138%nat |};
 {| dd_mask := 28799; dd_code := 16483; dd_selector := 0; dd_kind := 2; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 161%nat; dd_eq_index := 162%nat; dd_selector_index := 1088%nat; dd_kind_index := 1137%nat |};
 {| dd_mask := 28799; dd_code := 20579; dd_selector := 0; dd_kind := 5; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 163%nat; dd_eq_index := 164%nat; dd_selector_index := 1087%nat; dd_kind_index := 1136%nat |};
 {| dd_mask := 28799; dd_code := 24675; dd_selector := 0; dd_kind := 1; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 165%nat; dd_eq_index := 166%nat; dd_selector_index := 1086%nat; dd_kind_index := 1135%nat |};
 {| dd_mask := 28799; dd_code := 28771; dd_selector := 0; dd_kind := 4; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 167%nat; dd_eq_index := 168%nat; dd_selector_index := 1085%nat; dd_kind_index := 1134%nat |};
 {| dd_mask := 28799; dd_code := 3; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 2%nat; dd_and_index := 169%nat; dd_eq_index := 170%nat; dd_selector_index := 1084%nat; dd_kind_index := 1133%nat |};
 {| dd_mask := 28799; dd_code := 4099; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 13%nat; dd_and_index := 171%nat; dd_eq_index := 172%nat; dd_selector_index := 1083%nat; dd_kind_index := 1132%nat |};
 {| dd_mask := 28799; dd_code := 8195; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 14%nat; dd_and_index := 173%nat; dd_eq_index := 174%nat; dd_selector_index := 1082%nat; dd_kind_index := 1131%nat |};
 {| dd_mask := 28799; dd_code := 16387; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 175%nat; dd_eq_index := 176%nat; dd_selector_index := 1081%nat; dd_kind_index := 1130%nat |};
 {| dd_mask := 28799; dd_code := 20483; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 177%nat; dd_eq_index := 178%nat; dd_selector_index := 1080%nat; dd_kind_index := 1129%nat |};
 {| dd_mask := 28799; dd_code := 35; dd_selector := 0; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 6%nat; dd_and_index := 179%nat; dd_eq_index := 180%nat; dd_selector_index := 1079%nat; dd_kind_index := 1128%nat |};
 {| dd_mask := 28799; dd_code := 4131; dd_selector := 0; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 13%nat; dd_and_index := 181%nat; dd_eq_index := 182%nat; dd_selector_index := 1078%nat; dd_kind_index := 1127%nat |};
 {| dd_mask := 28799; dd_code := 8227; dd_selector := 0; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 14%nat; dd_and_index := 183%nat; dd_eq_index := 184%nat; dd_selector_index := 1077%nat; dd_kind_index := 1126%nat |};
 {| dd_mask := 28799; dd_code := 19; dd_selector := 0; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 5%nat; dd_and_index := 185%nat; dd_eq_index := 186%nat; dd_selector_index := 1076%nat; dd_kind_index := 1125%nat |};
 {| dd_mask := 28799; dd_code := 8211; dd_selector := 0; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 14%nat; dd_and_index := 187%nat; dd_eq_index := 188%nat; dd_selector_index := 1075%nat; dd_kind_index := 1124%nat |};
 {| dd_mask := 28799; dd_code := 12307; dd_selector := 0; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 14%nat; dd_and_index := 189%nat; dd_eq_index := 190%nat; dd_selector_index := 1074%nat; dd_kind_index := 1123%nat |};
 {| dd_mask := 28799; dd_code := 16403; dd_selector := 0; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 191%nat; dd_eq_index := 192%nat; dd_selector_index := 1073%nat; dd_kind_index := 1122%nat |};
 {| dd_mask := 28799; dd_code := 24595; dd_selector := 0; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 193%nat; dd_eq_index := 194%nat; dd_selector_index := 1072%nat; dd_kind_index := 1121%nat |};
 {| dd_mask := 28799; dd_code := 28691; dd_selector := 0; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 195%nat; dd_eq_index := 196%nat; dd_selector_index := 1071%nat; dd_kind_index := 1120%nat |};
 {| dd_mask := 4261441663; dd_code := 4115; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 13%nat; dd_and_index := 197%nat; dd_eq_index := 198%nat; dd_selector_index := 1070%nat; dd_kind_index := 1119%nat |};
 {| dd_mask := 4261441663; dd_code := 20499; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 15%nat; dd_and_index := 199%nat; dd_eq_index := 200%nat; dd_selector_index := 1069%nat; dd_kind_index := 1118%nat |};
 {| dd_mask := 4261441663; dd_code := 1073762323; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 31%nat; dd_and_index := 201%nat; dd_eq_index := 202%nat; dd_selector_index := 1068%nat; dd_kind_index := 1117%nat |};
 {| dd_mask := 4261441663; dd_code := 51; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 6%nat; dd_and_index := 203%nat; dd_eq_index := 204%nat; dd_selector_index := 1067%nat; dd_kind_index := 1116%nat |};
 {| dd_mask := 4261441663; dd_code := 1073741875; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 31%nat; dd_and_index := 205%nat; dd_eq_index := 206%nat; dd_selector_index := 1066%nat; dd_kind_index := 1115%nat |};
 {| dd_mask := 4261441663; dd_code := 4147; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 13%nat; dd_and_index := 207%nat; dd_eq_index := 208%nat; dd_selector_index := 1065%nat; dd_kind_index := 1114%nat |};
 {| dd_mask := 4261441663; dd_code := 8243; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 14%nat; dd_and_index := 209%nat; dd_eq_index := 210%nat; dd_selector_index := 1064%nat; dd_kind_index := 1113%nat |};
 {| dd_mask := 4261441663; dd_code := 12339; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 14%nat; dd_and_index := 211%nat; dd_eq_index := 212%nat; dd_selector_index := 1063%nat; dd_kind_index := 1112%nat |};
 {| dd_mask := 4261441663; dd_code := 16435; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 15%nat; dd_and_index := 213%nat; dd_eq_index := 214%nat; dd_selector_index := 1062%nat; dd_kind_index := 1111%nat |};
 {| dd_mask := 4261441663; dd_code := 20531; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 15%nat; dd_and_index := 215%nat; dd_eq_index := 216%nat; dd_selector_index := 1061%nat; dd_kind_index := 1110%nat |};
 {| dd_mask := 4261441663; dd_code := 1073762355; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 31%nat; dd_and_index := 217%nat; dd_eq_index := 218%nat; dd_selector_index := 1060%nat; dd_kind_index := 1109%nat |};
 {| dd_mask := 4261441663; dd_code := 24627; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 15%nat; dd_and_index := 219%nat; dd_eq_index := 220%nat; dd_selector_index := 1059%nat; dd_kind_index := 1108%nat |};
 {| dd_mask := 4261441663; dd_code := 28723; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 15%nat; dd_and_index := 221%nat; dd_eq_index := 222%nat; dd_selector_index := 1058%nat; dd_kind_index := 1107%nat |};
 {| dd_mask := 4027580415; dd_code := 15; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 4%nat; dd_and_index := 223%nat; dd_eq_index := 224%nat; dd_selector_index := 1057%nat; dd_kind_index := 1106%nat |};
 {| dd_mask := 4294967295; dd_code := 4111; dd_selector := 2; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 13%nat; dd_and_index := 225%nat; dd_eq_index := 226%nat; dd_selector_index := 1056%nat; dd_kind_index := 1105%nat |};
 {| dd_mask := 28799; dd_code := 4211; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 13%nat; dd_and_index := 227%nat; dd_eq_index := 228%nat; dd_selector_index := 1055%nat; dd_kind_index := 1104%nat |};
 {| dd_mask := 28799; dd_code := 8307; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 14%nat; dd_and_index := 229%nat; dd_eq_index := 230%nat; dd_selector_index := 1054%nat; dd_kind_index := 1103%nat |};
 {| dd_mask := 28799; dd_code := 12403; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 14%nat; dd_and_index := 231%nat; dd_eq_index := 232%nat; dd_selector_index := 1053%nat; dd_kind_index := 1102%nat |};
 {| dd_mask := 28799; dd_code := 20595; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 233%nat; dd_eq_index := 234%nat; dd_selector_index := 1052%nat; dd_kind_index := 1101%nat |};
 {| dd_mask := 28799; dd_code := 24691; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 235%nat; dd_eq_index := 236%nat; dd_selector_index := 1051%nat; dd_kind_index := 1100%nat |};
 {| dd_mask := 28799; dd_code := 28787; dd_selector := 2; dd_kind := 0; dd_mask_width := 15%nat; dd_code_width := 15%nat; dd_and_index := 237%nat; dd_eq_index := 238%nat; dd_selector_index := 1050%nat; dd_kind_index := 1099%nat |};
 {| dd_mask := 4294967295; dd_code := 115; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 7%nat; dd_and_index := 239%nat; dd_eq_index := 240%nat; dd_selector_index := 1049%nat; dd_kind_index := 1098%nat |};
 {| dd_mask := 4294967295; dd_code := 1048691; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 21%nat; dd_and_index := 241%nat; dd_eq_index := 242%nat; dd_selector_index := 1048%nat; dd_kind_index := 1097%nat |};
 {| dd_mask := 4294967295; dd_code := 268435571; dd_selector := 3; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 29%nat; dd_and_index := 243%nat; dd_eq_index := 244%nat; dd_selector_index := 1047%nat; dd_kind_index := 1096%nat |};
 {| dd_mask := 4294967295; dd_code := 270532723; dd_selector := 0; dd_kind := 0; dd_mask_width := 32%nat; dd_code_width := 29%nat; dd_and_index := 245%nat; dd_eq_index := 246%nat; dd_selector_index := 1046%nat; dd_kind_index := 1095%nat |}
 ].
Definition dut_decode_row n := nth (hd (Build_dut_decode_certificate_row 0 0 0 0 0 0 0 0 0 0) dut_decode_certificate_rows) dut_decode_certificate_rows n.
Definition dut_decode_mask_node n := 8263 + 2 * N.of_nat n.
Definition dut_decode_guard_node n := 8264 + 2 * N.of_nat n.
Definition dut_decode_mask_expression n :=
 Eprim_binop Band (@Eref VarOrder.T (@Eid VarOrder.T 8249))
 (@Econst VarOrder.T (Fuint (dd_mask_width (dut_decode_row n))) (from_N (dd_mask_width (dut_decode_row n)) (dd_mask (dut_decode_row n)))).
Definition dut_decode_guard_expression n :=
 Eprim_binop (Bcomp Beq)
 (@Econst VarOrder.T (Fuint (dd_code_width (dut_decode_row n))) (from_N (dd_code_width (dut_decode_row n)) (dd_code (dut_decode_row n))))
 (@Eref VarOrder.T (@Eid VarOrder.T (dut_decode_mask_node n))).
Lemma dut_decode_test_certificates n : (n < 49)%coq_nat ->
 nth_error data_address_expected_nodes (dd_and_index (dut_decode_row n)) = Some (dut_decode_mask_node n, dut_decode_mask_expression n) /\
 nth_error data_address_expected_nodes (dd_eq_index (dut_decode_row n)) = Some (dut_decode_guard_node n, dut_decode_guard_expression n) /\
 maxn 32 (dd_mask_width (dut_decode_row n)) = 32%nat /\
 to_N (from_N (dd_mask_width (dut_decode_row n)) (dd_mask (dut_decode_row n))) = dd_mask (dut_decode_row n) /\
 to_N (from_N (dd_code_width (dut_decode_row n)) (dd_code (dut_decode_row n))) = dd_code (dut_decode_row n).
Proof.
 intro Bound. do 49 (destruct n as [|n]; [vm_compute; repeat split; reflexivity|]); lia.
Qed.
Definition dut_decode_test instruction n := N.eqb (N.land instruction (dd_mask (dut_decode_row n))) (dd_code (dut_decode_row n)).
Theorem dut_decode_guard_history inputs path history limit instruction n :
 (n < 49)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)) ->
 forall time, ((4 <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
 VM.find (dut_decode_guard_node n) (history time) = Some (Gval (Fuint 1) [::dut_decode_test (to_N instruction) n]).
Proof.
 intros Bound Steps Instruction time Time.
 destruct time as [|[|time]]; try lia.
 destruct (dut_decode_test_certificates n Bound) as [MaskCertificate [GuardCertificate [Width [MaskValue CodeValue]]]].
 assert (Mask : VM.find (dut_decode_mask_node n) (history (S time)) = Some (Gval (Fuint 32)
 (andB instruction (from_N (dd_mask_width (dut_decode_row n)) (dd_mask (dut_decode_row n)))))).
 { eapply (reference_redirect_ground_step data_address_node_offsets data_address_expected_nodes (dut_decode_mask_node n) (dut_decode_mask_expression n));
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|eapply List.nth_error_In; exact MaskCertificate| |apply Steps; lia].
 intros site. unfold dut_decode_mask_expression.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite (Instruction time ltac:(lia)).
 rewrite size_from_N.
 rewrite ltnn. unfold zext_to. rewrite size_from_N subnn. unfold zext. rewrite zeros0 cats0.
 unfold eval_binop. cbn [eval_binop_basic]. rewrite Width. reflexivity. }
 eapply (reference_redirect_ground_step data_address_node_offsets data_address_expected_nodes (dut_decode_guard_node n) (dut_decode_guard_expression n));
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|eapply List.nth_error_In; exact GuardCertificate| |apply Steps; lia].
 intros site. unfold dut_decode_guard_expression.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite size_from_N ltnn. unfold zext_to. rewrite size_from_N subnn. unfold zext. rewrite zeros0 cats0 Mask.
 rewrite <- Width. rewrite redirect_mask_decode. rewrite MaskValue CodeValue. reflexivity.
Qed.
Definition dut_decode_width branch : nat := if branch then 3%nat else 2%nat.
Definition dut_decode_output branch row := if branch then dd_kind row else dd_selector row.
Definition dut_decode_mux_node branch n := (if branch then 8606 else 8361) + N.of_nat n.
Definition dut_decode_mux_expression branch n :=
 let row := dut_decode_row (Nat.sub 48 n) in
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (dut_decode_guard_node (Nat.sub 48 n))))
 (@Econst VarOrder.T (Fuint (dut_decode_width branch)) (from_N (dut_decode_width branch) (dut_decode_output branch row)))
 (match n with O => @Econst VarOrder.T (Fuint (dut_decode_width branch)) (from_N (dut_decode_width branch) 0)
 | S before => @Eref VarOrder.T (@Eid VarOrder.T (dut_decode_mux_node branch before)) end).
Fixpoint dut_decode_mux_value branch instruction count :=
 match count with O => from_N (dut_decode_width branch) 0
 | S n => if dut_decode_test instruction (Nat.sub 48 n) then
  from_N (dut_decode_width branch) (dut_decode_output branch (dut_decode_row (Nat.sub 48 n)))
  else dut_decode_mux_value branch instruction n end.
Lemma dut_decode_mux_certificates branch n : (n < 49)%coq_nat ->
 nth_error joint_update_expected_nodes
 ((if branch then dd_kind_index else dd_selector_index) (dut_decode_row (Nat.sub 48 n))) =
 Some (dut_decode_mux_node branch n,dut_decode_mux_expression branch n).
Proof.
 intro Bound. destruct branch; do 49 (destruct n as [|n]; [vm_compute; reflexivity|]); lia.
Qed.
Lemma dut_decode_mux_value_size branch instruction count :
 size (dut_decode_mux_value branch instruction count) = dut_decode_width branch.
Proof.
 induction count as [|count IH]; cbn [dut_decode_mux_value]; [apply size_from_N|].
 destruct (dut_decode_test instruction (Nat.sub 48 count)); [apply size_from_N|exact IH].
Qed.
Lemma dut_decode_adapt width bits : size bits = width ->
 adapt_hvalue_as_type (Gval (Fuint width) bits) (Gtyp (Fuint width)) = Some (Gval (Fuint width) bits).
Proof.
 intro Size. cbn [adapt_hvalue_as_type]. rewrite <- Size, take_size.
 unfold zext_to. rewrite subnn. unfold zext. rewrite zeros0 cats0. reflexivity.
Qed.
Lemma dut_decode_constant invalid site memories old current width value :
 eval_hfexpr_validif_policy invalid site memories (@Econst VarOrder.T (Fuint width) (from_N width value)) old current = Some (Gval (Fuint width) (from_N width value)).
Proof.
 cbn [eval_hfexpr_validif_policy]. rewrite size_from_N ltnn.
 unfold zext_to. rewrite size_from_N subnn. unfold zext. rewrite zeros0 cats0. reflexivity.
Qed.
Lemma dut_decode_constant_type old width value :
 eval_type_of_expr (@Econst VarOrder.T (Fuint width) (from_N width value)) old = Some (Gtyp (Fuint width)).
Proof. unfold eval_type_of_expr. cbn [type_of_expr']. rewrite size_from_N ltnn. reflexivity. Qed.
Lemma dut_decode_mux_eval invalid site memories old condition yes no width yesbits nobits bit :
 (forall inner, eval_hfexpr_validif_policy invalid inner memories condition old old = Some (Gval (Fuint 1) [::bit])) ->
 (forall inner, eval_hfexpr_validif_policy invalid inner memories yes old old = Some (Gval (Fuint width) yesbits)) ->
 (forall inner, eval_hfexpr_validif_policy invalid inner memories no old old = Some (Gval (Fuint width) nobits)) ->
 eval_type_of_expr yes old = Some (Gtyp (Fuint width)) ->
 eval_type_of_expr no old = Some (Gtyp (Fuint width)) ->
 size yesbits = width -> size nobits = width ->
 eval_hfexpr_validif_policy invalid site memories (@Emux VarOrder.T condition yes no) old old = Some (Gval (Fuint width) (if bit then yesbits else nobits)).
Proof.
 intros Condition Yes No YesType NoType YesSize NoSize.
 cbn [eval_hfexpr_validif_policy]. rewrite Condition.
 destruct bit; cbn; [rewrite Yes NoType|rewrite No YesType]; cbn; rewrite maxnn;
 apply dut_decode_adapt; assumption.
Qed.
Theorem dut_decode_mux_history inputs path history limit instruction branch :
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)) ->
 forall n time, (n < 49)%coq_nat -> (Nat.add 5 n <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (dut_decode_mux_node branch n) (history time) = Some (Gval (Fuint (dut_decode_width branch)) (dut_decode_mux_value branch (to_N instruction) (S n))).
Proof.
 intros Steps Instruction n. induction n as [|n IH]; intros time Bound Lower Upper; destruct time as [|time]; try lia.
 - eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes _ (dut_decode_mux_expression branch 0));
   [exact joint_update_node_positions|exact joint_update_node_safety|eapply List.nth_error_In; apply dut_decode_mux_certificates; lia| |apply Steps; lia].
   intros site. unfold dut_decode_mux_expression. change (48-0)%nat with 48%nat.
   cbn [dut_decode_mux_value]. eapply dut_decode_mux_eval.
   + intros inner. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction 48 ltac:(lia) Steps Instruction time); lia.
   + intro inner. apply dut_decode_constant.
   + intro inner. apply dut_decode_constant.
   + apply dut_decode_constant_type.
   + apply dut_decode_constant_type.
   + apply size_from_N.
   + apply size_from_N.
 - pose proof (IH time ltac:(lia) ltac:(lia) ltac:(lia)) as Previous.
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes _ (dut_decode_mux_expression branch (S n)));
   [exact joint_update_node_positions|exact joint_update_node_safety|eapply List.nth_error_In; apply dut_decode_mux_certificates; lia| |apply Steps; lia].
   intros site. unfold dut_decode_mux_expression. cbn [dut_decode_mux_value]. eapply dut_decode_mux_eval.
   + intros inner. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply (dut_decode_guard_history inputs path history limit instruction (Nat.sub 48 (S n)) ltac:(lia) Steps Instruction time); lia.
   + intro inner. apply dut_decode_constant.
   + intro inner. exact Previous.
   + apply dut_decode_constant_type.
   + unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Previous. reflexivity.
   + apply size_from_N.
   + exact (dut_decode_mux_value_size branch (to_N instruction) (S n)).
Qed.
Lemma dut_decode_numeric_projection (test : N * N -> N) instruction rows :
 test (dut_decode_priority instruction rows) =
 fold_right (fun row tail => let '(mask,code,selector,kind) := row in
  if N.eqb (N.land instruction mask) code then test (selector,kind) else tail)
 (test (0,0)) rows.
Proof.
 induction rows as [|[[[mask code] selector] kind] rest IH]; [reflexivity|].
 cbn [dut_decode_priority fold_right]. destruct (N.eqb (N.land instruction mask) code); [reflexivity|exact IH].
Qed.
Lemma dut_decode_to_N_if bit yes no : to_N (if bit then yes else no) = if bit then to_N yes else to_N no.
Proof. destruct bit; reflexivity. Qed.
Lemma dut_decode_mux_function branch instruction :
 to_N (dut_decode_mux_value branch instruction 49) =
 (if branch then snd else fst) (dut_decode_function instruction).
Proof.
 unfold dut_decode_function. destruct branch;
 rewrite dut_decode_numeric_projection;
 cbn [dut_decode_mux_value dut_decode_test dut_decode_row dut_decode_certificate_rows
   nth hd dd_mask dd_code dd_selector dd_kind dut_decode_width dut_decode_output
   dut_decode_rows fold_right fst snd];
 repeat rewrite dut_decode_to_N_if; reflexivity.
Qed.
Require Import FormalPCDecodeInputConnections FormalPCDecodeConnections FormalDeclaredConnection
 JointUpdateConnectionCertificates JointUpdateBoundaryHistory JointBoundaryRegisters FormalObservedHistory FormalLocalHistory.
Theorem dut_decode_history inputs path history limit instruction :
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction) ->
 size instruction = 32%nat ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 84 (history time) = Some (Gval (Fuint 2) (dut_decode_mux_value false (to_N instruction) 49)) /\
 VM.find 1359 (history time) = Some (Gval (Fuint 3) (dut_decode_mux_value true (to_N instruction) 49)).
Proof.
 intros Steps Front Size time Lower Upper.
 assert (Source : forall i, (i <= limit)%coq_nat -> VM.find 7748 (history i) = Some (Gval (Fuint 32) instruction)).
 { intros i Bound.
   pose proof (joint_update_register_history_same (formal_invalid_policy inputs path) history limit 7748 32
     ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat); vm_compute; reflexivity) Steps) as Hold.
   rewrite (Hold i Bound). rewrite <- (Hold limit ltac:(lia)). exact Front. }
 assert (Instruction : forall i, ((2 <= i)%coq_nat /\ (i <= limit)%coq_nat) -> VM.find 8249 (history i) = Some (Gval (Fuint 32) instruction)).
 { intros [|[|i]] Bound; try lia.
   eapply decode_input_connection_8249; [|apply dut_decode_adapt; exact Size|apply Steps; lia].
   eapply decode_input_connection_83; [|apply dut_decode_adapt; exact Size|apply Steps; lia]. apply Source; lia. }
 destruct time as [|[|[|time]]]; try lia. split.
 - eapply pc_decode_connection_84; [|apply dut_decode_adapt; apply (dut_decode_mux_value_size false)|apply Steps; lia].
   eapply pc_decode_connection_8250; [|apply dut_decode_adapt; apply (dut_decode_mux_value_size false)|apply Steps; lia].
   exact (dut_decode_mux_history inputs path history limit instruction false Steps Instruction 48 (S time) ltac:(lia) ltac:(lia) ltac:(lia)).
 - eapply (declared_connection_value 1437 flat_statements joint_update_connection_1359_decl joint_update_connection_1359_mid joint_update_connection_1359_tail 1359 90 3 (Gval (Fuint 3) (dut_decode_mux_value true (to_N instruction) 49)));
   [exact joint_update_connection_1359_position|exact joint_update_connection_1359_split|exact joint_update_connection_1359_straight|exact joint_update_connection_1359_mid_safe|exact joint_update_connection_1359_tail_safe|exact joint_update_connection_1359_nonregister|reflexivity| |apply dut_decode_adapt; apply (dut_decode_mux_value_size true)|apply Steps; lia].
   eapply (declared_connection_value 67 flat_statements joint_update_connection_90_decl joint_update_connection_90_mid joint_update_connection_90_tail 90 8256 3 (Gval (Fuint 3) (dut_decode_mux_value true (to_N instruction) 49)));
   [exact joint_update_connection_90_position|exact joint_update_connection_90_split|exact joint_update_connection_90_straight|exact joint_update_connection_90_mid_safe|exact joint_update_connection_90_tail_safe|exact joint_update_connection_90_nonregister|reflexivity| |apply dut_decode_adapt; apply (dut_decode_mux_value_size true)|apply Steps; lia].
   eapply (declared_connection_value 9016 flat_statements joint_update_connection_8256_decl joint_update_connection_8256_mid joint_update_connection_8256_tail 8256 8654 3 (Gval (Fuint 3) (dut_decode_mux_value true (to_N instruction) 49)));
   [exact joint_update_connection_8256_position|exact joint_update_connection_8256_split|exact joint_update_connection_8256_straight|exact joint_update_connection_8256_mid_safe|exact joint_update_connection_8256_tail_safe|exact joint_update_connection_8256_nonregister|reflexivity| |apply dut_decode_adapt; apply (dut_decode_mux_value_size true)|apply Steps; lia].
   exact (dut_decode_mux_history inputs path history limit instruction true Steps Instruction 48 time ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.
Local Opaque dut_decode_mux_value dut_decode_function.
Theorem dut_decode_controls_observed memory inputs k observed instruction selector kind :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 84 (top_environment observed) = Some (Gval (Fuint 2) selector) ->
 VM.find 1359 (top_environment observed) = Some (Gval (Fuint 3) kind) ->
 size instruction = 32%nat ->
 dut_redirect_controls_match (to_N instruction) (to_N selector) (to_N kind).
Proof.
 intros Observe Legal Front Selector Kind Size.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 rewrite <- Last in Front, Selector, Kind.
 destruct (dut_decode_history (generated_observation_input inputs k) nil history 9259 instruction Steps Front Size 9259 ltac:(vm_compute;lia) (le_n 9259)) as [S K].
 rewrite Selector in S. rewrite Kind in K. inversion S; inversion K; subst selector kind.
 pose proof (dut_decode_mux_function false (to_N instruction)) as SelectorValue.
 pose proof (dut_decode_mux_function true (to_N instruction)) as KindValue.
 exact (eq_ind_r (fun selector => dut_redirect_controls_match (to_N instruction) selector
   (to_N (dut_decode_mux_value true (to_N instruction) 49)))
   (eq_ind_r (fun kind => dut_redirect_controls_match (to_N instruction)
     (fst (dut_decode_function (to_N instruction))) kind)
     (dut_decode_controls (to_N instruction)) KindValue) SelectorValue).
Qed.

Require Import DelayedDUTRedirectSemantics ReferenceRedirectSemantics.
Theorem delayed_decoded_reference_redirect_observed memory inputs k observed committed next_observed
 instruction dut_left dut_right kind selector ref_left ref_right immediate pc csr :
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some committed ->
 generated_observe memory inputs (S k) = Some next_observed ->
 generated_legal_trace memory inputs (S k) ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 generated_legal_trace memory inputs k ->
 VM.find 1357 (top_environment observed) = Some (Gval (Fuint 32) dut_left) ->
 VM.find 1358 (top_environment observed) = Some (Gval (Fuint 32) dut_right) ->
 VM.find 1359 (top_environment observed) = Some (Gval (Fuint 3) kind) ->
 VM.find 84 (top_environment observed) = Some (Gval (Fuint 2) selector) ->
 VM.find 7748 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1395 (top_environment next_observed) = Some (Gval (Fuint 1) [::true]) ->
 size instruction = 32%nat ->
 VM.find 2209 (top_environment next_observed) = Some (Gval (Fuint 32) ref_left) ->
 VM.find 2804 (top_environment next_observed) = Some (Gval (Fuint 32) ref_right) ->
 VM.find 2552 (top_environment next_observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (top_environment next_observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (top_environment next_observed) = Some (Gval (Fuint 32) csr) ->
 size dut_left = 32%nat -> size dut_right = 32%nat ->
 size ref_left = 32%nat -> size ref_right = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 dut_operand_tests_match (to_N kind) (to_N dut_left) (to_N dut_right) (to_N ref_left) (to_N ref_right) ->
 (dut_reference_taken (to_N instruction) (to_N ref_left) (to_N ref_right) = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate) = true) ->
 (N.eqb (N.land (to_N instruction) 28799) 103 = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (N.clearbit (to_N ref_left + to_N immediate) 0) = true) ->
 VM.find 7760 (top_environment next_observed) = VM.find 6507 (top_environment next_observed).
Proof.
 intros Observe Run NextObserve NextLegal Reset Legal DutLeft DutRight Kind Selector Front Enabled InstructionSize RefLeft RefRight Immediate Pc Csr
 DutLeftSize DutRightSize RefLeftSize RefRightSize PcSize CsrSize Operands BranchAligned JalrAligned.
 pose proof (dut_decode_controls_observed memory inputs k observed instruction selector kind Observe Legal Front Selector Kind InstructionSize) as Controls.
 exact (delayed_enabled_reference_redirect_observed memory inputs k observed committed next_observed instruction dut_left dut_right kind selector ref_left ref_right immediate pc csr Observe Run NextObserve NextLegal Reset Legal DutLeft DutRight Kind Selector Front Enabled InstructionSize RefLeft RefRight Immediate Pc Csr DutLeftSize DutRightSize RefLeftSize RefRightSize PcSize CsrSize Controls Operands BranchAligned JalrAligned).
Qed.
