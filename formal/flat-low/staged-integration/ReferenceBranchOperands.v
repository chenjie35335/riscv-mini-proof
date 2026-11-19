Require Import CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceRs1Types ReferenceRs2Types ReferenceLoadRs1 ReferenceStoreRs2 ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlExpressions ReferenceRedirectSpine RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.

Require Import RFALUReferencePorts ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence0 ReferenceControlNodeCertificates2 ReferenceControlNodeCongruence2 RFReferenceNopHistory ReferenceSecondRegisterRead.

Definition branch_operand_match instruction lane :=N.land(to_N instruction)(reference_instruction_mask(Nat.add 23 lane))=reference_instruction_code(Nat.add 23 lane).
Lemma branch_operands_raw inputs path history limit reset time instruction lane :(lane<6)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(rf_alu_rs1_yes(Nat.add 17 lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)) /\
 VM.find(rf_alu_rs2_yes(Nat.add 7 lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof. intros Lane Resets Steps Lower Upper Source.

destruct lane as[|lane]. {

assert(V0:VM.find 2005(history time)=Some(Gval(Fuint 31)(drop 0(take 31 instruction)))).
 { rewrite(reference_control_stable_2005_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2005 reference_control_expr_2005);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2005| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2005 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }

assert(V1:VM.find 2006(history time)=Some(Gval(Fuint 25)(drop 0(take 25 (drop 0(take 31 instruction)))))).
 { rewrite(reference_control_stable_2006_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2006 reference_control_expr_2006);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2006| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2006 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0;reflexivity. }

assert(V2:VM.find 2007(history time)=Some(Gval(Fuint 20)(drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_2007_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2007 reference_control_expr_2007);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2007| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2007 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

assert(V3:VM.find 2008(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))))).
 { rewrite(reference_control_stable_2008_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2008 reference_control_expr_2008);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2008| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2008 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2;reflexivity. }

assert(V4:VM.find 2583(history time)=Some(Gval(Fuint 5)(drop 20(take 25 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_2583_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2583 reference_control_expr_2583);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2583| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2583 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs2_yes nth]. rewrite !drop0 !take_take in V3,V4;try reflexivity. split;assumption. }

destruct lane as[|lane]. {

assert(V0:VM.find 1999(history time)=Some(Gval(Fuint 31)(drop 0(take 31 instruction)))).
 { rewrite(reference_control_stable_1999_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1999 reference_control_expr_1999);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1999| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1999 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }

assert(V1:VM.find 2000(history time)=Some(Gval(Fuint 25)(drop 0(take 25 (drop 0(take 31 instruction)))))).
 { rewrite(reference_control_stable_2000_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2000 reference_control_expr_2000);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2000| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2000 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0;reflexivity. }

assert(V2:VM.find 2001(history time)=Some(Gval(Fuint 20)(drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_2001_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2001 reference_control_expr_2001);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2001| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2001 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

assert(V3:VM.find 2002(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))))).
 { rewrite(reference_control_stable_2002_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2002 reference_control_expr_2002);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2002| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2002 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2;reflexivity. }

assert(V4:VM.find 2582(history time)=Some(Gval(Fuint 5)(drop 20(take 25 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_2582_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2582 reference_control_expr_2582);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2582| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2582 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs2_yes nth]. rewrite !drop0 !take_take in V3,V4;try reflexivity. split;assumption. }

destruct lane as[|lane]. {

assert(V0:VM.find 1993(history time)=Some(Gval(Fuint 31)(drop 0(take 31 instruction)))).
 { rewrite(reference_control_stable_1993_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1993 reference_control_expr_1993);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1993| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1993 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }

assert(V1:VM.find 1994(history time)=Some(Gval(Fuint 25)(drop 0(take 25 (drop 0(take 31 instruction)))))).
 { rewrite(reference_control_stable_1994_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1994 reference_control_expr_1994);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1994| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1994 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0;reflexivity. }

assert(V2:VM.find 1995(history time)=Some(Gval(Fuint 20)(drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_1995_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1995 reference_control_expr_1995);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1995| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1995 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

assert(V3:VM.find 1996(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))))).
 { rewrite(reference_control_stable_1996_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1996 reference_control_expr_1996);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1996| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1996 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2;reflexivity. }

assert(V4:VM.find 2581(history time)=Some(Gval(Fuint 5)(drop 20(take 25 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_2581_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2581 reference_control_expr_2581);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2581| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2581 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs2_yes nth]. rewrite !drop0 !take_take in V3,V4;try reflexivity. split;assumption. }

destruct lane as[|lane]. {

assert(V0:VM.find 1987(history time)=Some(Gval(Fuint 31)(drop 0(take 31 instruction)))).
 { rewrite(reference_control_stable_1987_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1987 reference_control_expr_1987);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1987| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1987 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }

assert(V1:VM.find 1988(history time)=Some(Gval(Fuint 25)(drop 0(take 25 (drop 0(take 31 instruction)))))).
 { rewrite(reference_control_stable_1988_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1988 reference_control_expr_1988);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1988| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1988 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0;reflexivity. }

assert(V2:VM.find 1989(history time)=Some(Gval(Fuint 20)(drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_1989_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1989 reference_control_expr_1989);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1989| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1989 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

assert(V3:VM.find 1990(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))))).
 { rewrite(reference_control_stable_1990_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1990 reference_control_expr_1990);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1990| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1990 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2;reflexivity. }

assert(V4:VM.find 2580(history time)=Some(Gval(Fuint 5)(drop 20(take 25 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_2580_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2580 reference_control_expr_2580);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2580| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2580 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs2_yes nth]. rewrite !drop0 !take_take in V3,V4;try reflexivity. split;assumption. }

destruct lane as[|lane]. {

assert(V0:VM.find 1981(history time)=Some(Gval(Fuint 31)(drop 0(take 31 instruction)))).
 { rewrite(reference_control_stable_1981_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1981 reference_control_expr_1981);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1981| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1981 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }

assert(V1:VM.find 1982(history time)=Some(Gval(Fuint 25)(drop 0(take 25 (drop 0(take 31 instruction)))))).
 { rewrite(reference_control_stable_1982_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1982 reference_control_expr_1982);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1982| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1982 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0;reflexivity. }

assert(V2:VM.find 1983(history time)=Some(Gval(Fuint 20)(drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_1983_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1983 reference_control_expr_1983);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1983| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1983 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

assert(V3:VM.find 1984(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))))).
 { rewrite(reference_control_stable_1984_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1984 reference_control_expr_1984);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1984| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1984 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2;reflexivity. }

assert(V4:VM.find 2579(history time)=Some(Gval(Fuint 5)(drop 20(take 25 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_2579_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2579 reference_control_expr_2579);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2579| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2579 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs2_yes nth]. rewrite !drop0 !take_take in V3,V4;try reflexivity. split;assumption. }

destruct lane as[|lane]. {

assert(V0:VM.find 1975(history time)=Some(Gval(Fuint 31)(drop 0(take 31 instruction)))).
 { rewrite(reference_control_stable_1975_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1975 reference_control_expr_1975);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1975| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1975 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }

assert(V1:VM.find 1976(history time)=Some(Gval(Fuint 25)(drop 0(take 25 (drop 0(take 31 instruction)))))).
 { rewrite(reference_control_stable_1976_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1976 reference_control_expr_1976);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1976| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1976 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V0;reflexivity. }

assert(V2:VM.find 1977(history time)=Some(Gval(Fuint 20)(drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_1977_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1977 reference_control_expr_1977);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1977| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1977 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

assert(V3:VM.find 1978(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 (drop 0(take 25 (drop 0(take 31 instruction)))))))))).
 { rewrite(reference_control_stable_1978_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1978 reference_control_expr_1978);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1978| |apply Steps;lia].
 intro site. cbn[reference_control_expr_1978 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2;reflexivity. }

assert(V4:VM.find 2578(history time)=Some(Gval(Fuint 5)(drop 20(take 25 (drop 0(take 25 (drop 0(take 31 instruction)))))))).
 { rewrite(reference_control_stable_2578_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2578 reference_control_expr_2578);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2578| |apply Steps;lia].
 intro site. cbn[reference_control_expr_2578 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V1;reflexivity. }

cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs2_yes nth]. rewrite !drop0 !take_take in V3,V4;try reflexivity. split;assumption. }

lia. Qed.

Theorem branch_rs1_history inputs path history limit reset time instruction lane :(lane<6)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.add 17 lane)])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(proj1(branch_operands_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia))))as Raw.
 assert(Target:(Nat.add 17 lane<42)%coq_nat).
 { lia. }
 assert(Selected:VM.find 2143(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { change(VM.find(rf_alu_rs1_node 41)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))42 (Nat.add 17 lane)5(rf_instruction_address false instruction)2101 rf_alu_rs1_node rf_alu_rs1_guard rf_alu_rs1_yes);[exact Target|exact(rf_instruction_address_size false instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(rf_alu_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(rf_alu_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2144(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(rf_alu_rs1_value 15 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size false instruction Size). }
 eapply(rf_alu_rs1_value 16 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Lemma branch_rs1_decode instruction lane n :(lane<6)%coq_nat ->(n<42)%coq_nat ->branch_operand_match instruction lane ->
 N.eqb(reference_instruction_code(rf_alu_rs1_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_alu_rs1_decoder n)))=Nat.eqb n(Nat.add 17 lane).
Proof. intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction(Nat.add 23 lane)(rf_alu_rs1_decoder n)ltac:(lia)ltac:(do 42(destruct n as[|n];[cbn[rf_alu_rs1_decoder nth];lia|]);lia)Match).
 do 6(destruct lane as[|lane];[do 42(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.

Theorem branch_rs2_history inputs path history limit reset time instruction lane :(lane<6)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.add 7 lane)])) ->
 VM.find 2622(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(proj2(branch_operands_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia))))as Raw.
 assert(Target:(Nat.add 7 lane<24)%coq_nat).
 { lia. }
 assert(Selected:VM.find 2620(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { change(VM.find(rf_alu_rs2_node 23)(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))24 (Nat.add 7 lane)5(rf_instruction_address true instruction)2596 rf_alu_rs2_node rf_alu_rs2_guard rf_alu_rs2_yes);[exact Target|exact(rf_instruction_address_size true instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(rf_alu_rs2_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(rf_alu_rs2_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2621(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(rf_alu_rs2_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2621 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size true instruction Size). }
 eapply(rf_alu_rs2_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.

Lemma branch_rs2_decode instruction lane n :(lane<6)%coq_nat ->(n<24)%coq_nat ->branch_operand_match instruction lane ->
 N.eqb(reference_instruction_code(rf_alu_rs2_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_alu_rs2_decoder n)))=Nat.eqb n(Nat.add 7 lane).
Proof. intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction(Nat.add 23 lane)(rf_alu_rs2_decoder n)ltac:(lia)ltac:(do 24(destruct n as[|n];[cbn[rf_alu_rs2_decoder nth];lia|]);lia)Match).
 do 6(destruct lane as[|lane];[do 24(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.

Require Import ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalObservedHistory FormalLocalHistory MemoryRequestObservedSemantics LoadTypeCorrespondence.

Theorem branch_rs1_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane < 6)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 branch_operand_match instruction lane ->
 VM.find 2145 (top_environment observed) = Some (Gval (Fuint 5) (rf_instruction_address false instruction)).
Proof.
 intros Observe Legal Enabled Lane Instruction Load.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (195 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert (Source : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Lower Upper. exact (memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert (Guards : forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.add 17 lane)])).
 { intros n Bound.
   set (h := fun t:nat => history (match t with O=>9248%nat | S O=>9249%nat | _=>9250%nat end)).
   assert (HS : forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
   { intros [|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
   assert (HI : forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
   { intros [|[|t]] T;unfold h;apply Source;vm_compute;lia. }
   pose proof(reference_instruction_decode_history _ h 2 instruction (rf_alu_rs1_decoder n) ltac:(do 42 (destruct n as [|n];[cbn [rf_alu_rs1_decoder nth];lia|]);lia) HS HI 2 ltac:(lia) ltac:(lia))as Decode.
   rewrite(branch_rs1_decode instruction lane n Lane Bound Load)in Decode. exact Decode. }
 pose proof(branch_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Guards)as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem reference_branch_rs1_bank_active_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 branch_operand_match instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction)))).
Proof.
 intros Observe Legal Enabled Lane Instruction Match Bank.
 assert(Size:size instruction=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[W V]]. rewrite Instruction in V;inversion V;subst;exact W. }
 eapply(reference_register_read_observed memory inputs k observed bank (rf_instruction_address false instruction));[exact Observe|exact Legal|exact Bank|exact(rf_instruction_address_size false instruction Size)|].
 exact(branch_rs1_observed memory inputs k observed instruction lane Observe Legal Enabled Lane Instruction Match).
Qed.

Theorem branch_rs2_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane < 6)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 branch_operand_match instruction lane ->
 VM.find 2622 (top_environment observed) = Some (Gval (Fuint 5) (rf_instruction_address true instruction)).
Proof.
 intros Observe Legal Enabled Lane Instruction Load.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (195 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert (Source : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Lower Upper. exact (memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert (Guards : forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.add 7 lane)])).
 { intros n Bound.
   set (h := fun t:nat => history (match t with O=>9248%nat | S O=>9249%nat | _=>9250%nat end)).
   assert (HS : forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
   { intros [|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
   assert (HI : forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
   { intros [|[|t]] T;unfold h;apply Source;vm_compute;lia. }
   pose proof(reference_instruction_decode_history _ h 2 instruction (rf_alu_rs2_decoder n) ltac:(do 24 (destruct n as [|n];[cbn [rf_alu_rs2_decoder nth];lia|]);lia) HS HI 2 ltac:(lia) ltac:(lia))as Decode.
   rewrite(branch_rs2_decode instruction lane n Lane Bound Load)in Decode. exact Decode. }
 pose proof(branch_rs2_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Guards)as Value.
 rewrite(reference_control_stable_2622_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem reference_branch_rs2_bank_active_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 branch_operand_match instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address true instruction)))).
Proof.
 intros Observe Legal Enabled Lane Instruction Match Bank.
 assert(Size:size instruction=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[W V]]. rewrite Instruction in V;inversion V;subst;exact W. }
 eapply(reference_second_register_read_observed memory inputs k observed bank (rf_instruction_address true instruction));[exact Observe|exact Legal|exact Bank|exact(rf_instruction_address_size true instruction Size)|].
 exact(branch_rs2_observed memory inputs k observed instruction lane Observe Legal Enabled Lane Instruction Match).
Qed.

Require Import ReferenceIllegalObserved LoadPipelineClassification FormalInstructionResetConstants.
Theorem reference_branch_operands_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->branch_operand_match instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction)))) /\
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address true instruction)))).
Proof.
 intros Observe Legal Reset Lane Instruction Match Bank.
 assert(Enabled:VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true])).
 { destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Late Nop]].
 destruct bit.
 - specialize(Nop(Logic.eq_refl _)). rewrite Nop in Instruction;inversion Instruction;subst instruction.
 do 6(destruct lane as[|lane];[vm_compute in Match;discriminate|]);lia.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late). }
 split.
 - exact(reference_branch_rs1_bank_active_observed memory inputs k observed instruction lane bank Observe Legal Enabled Lane Instruction Match Bank).
 - exact(reference_branch_rs2_bank_active_observed memory inputs k observed instruction lane bank Observe Legal Enabled Lane Instruction Match Bank).
Qed.
