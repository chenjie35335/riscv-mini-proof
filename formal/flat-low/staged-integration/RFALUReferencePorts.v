Require Import CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceRs1Types ReferenceRs2Types ReferenceLoadRs1 ReferenceStoreRs2 ReferenceLoadImmediate ReferenceImmediateTypes ReferenceInstructionDecode ReferenceControlStabilityHistory ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates2 ReferenceControlExpressions ReferenceRedirectSpine RFReadPorts DUTRedirectDecode.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_alu_rs1_node n :VarOrder.T:=N.of_nat(Nat.add 2102 n).
Definition rf_alu_rs1_decoder n:=nth 0%nat [::3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;22%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat] n.
Definition rf_alu_rs1_guard n:=reference_instruction_guard(rf_alu_rs1_decoder n).
Definition rf_alu_rs1_yes n :VarOrder.T:=nth 0 [::2086;2082;2078;2074;2070;2066;2062;2057;2052;2047;2042;2037;2032;2027;2022;2017;2012;2008;2002;1996;1990;1984;1978;1972;1968;1964;1960;1956;1954;1949;1944;1939;1935;1931;1927;1922;1917;1912;1907;1902;1897;1892] n.
Definition rf_alu_rs1_target lane:=nth 0%nat [::9%nat;10%nat;11%nat;0%nat;1%nat;2%nat] lane.
Definition rf_alu_rs1_expression n:=@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T(rf_alu_rs1_guard n)))(@Eref VarOrder.T(@Eid VarOrder.T(rf_alu_rs1_yes n)))(@Eref VarOrder.T(@Eid VarOrder.T(match n with O=>2101|S n=>rf_alu_rs1_node n end))).
Lemma rf_alu_rs1_member n :(n<42)%coq_nat ->List.In(rf_alu_rs1_node n,rf_alu_rs1_expression n)reference_control_0_nodes.
Proof. intro Bound.
destruct n as[|n];[exact reference_control_member_2102|].
destruct n as[|n];[exact reference_control_member_2103|].
destruct n as[|n];[exact reference_control_member_2104|].
destruct n as[|n];[exact reference_control_member_2105|].
destruct n as[|n];[exact reference_control_member_2106|].
destruct n as[|n];[exact reference_control_member_2107|].
destruct n as[|n];[exact reference_control_member_2108|].
destruct n as[|n];[exact reference_control_member_2109|].
destruct n as[|n];[exact reference_control_member_2110|].
destruct n as[|n];[exact reference_control_member_2111|].
destruct n as[|n];[exact reference_control_member_2112|].
destruct n as[|n];[exact reference_control_member_2113|].
destruct n as[|n];[exact reference_control_member_2114|].
destruct n as[|n];[exact reference_control_member_2115|].
destruct n as[|n];[exact reference_control_member_2116|].
destruct n as[|n];[exact reference_control_member_2117|].
destruct n as[|n];[exact reference_control_member_2118|].
destruct n as[|n];[exact reference_control_member_2119|].
destruct n as[|n];[exact reference_control_member_2120|].
destruct n as[|n];[exact reference_control_member_2121|].
destruct n as[|n];[exact reference_control_member_2122|].
destruct n as[|n];[exact reference_control_member_2123|].
destruct n as[|n];[exact reference_control_member_2124|].
destruct n as[|n];[exact reference_control_member_2125|].
destruct n as[|n];[exact reference_control_member_2126|].
destruct n as[|n];[exact reference_control_member_2127|].
destruct n as[|n];[exact reference_control_member_2128|].
destruct n as[|n];[exact reference_control_member_2129|].
destruct n as[|n];[exact reference_control_member_2130|].
destruct n as[|n];[exact reference_control_member_2131|].
destruct n as[|n];[exact reference_control_member_2132|].
destruct n as[|n];[exact reference_control_member_2133|].
destruct n as[|n];[exact reference_control_member_2134|].
destruct n as[|n];[exact reference_control_member_2135|].
destruct n as[|n];[exact reference_control_member_2136|].
destruct n as[|n];[exact reference_control_member_2137|].
destruct n as[|n];[exact reference_control_member_2138|].
destruct n as[|n];[exact reference_control_member_2139|].
destruct n as[|n];[exact reference_control_member_2140|].
destruct n as[|n];[exact reference_control_member_2141|].
destruct n as[|n];[exact reference_control_member_2142|].
destruct n as[|n];[exact reference_control_member_2143|].
lia. Qed.
Lemma rf_alu_rs1_step n invalid old result word :(n<42)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(rf_alu_rs1_expression n)old old=Some(Gval(Fuint 5)word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find(rf_alu_rs1_node n)result=Some(Gval(Fuint 5)word).
Proof. intros Bound Eval Step. eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes _ (rf_alu_rs1_expression n));[exact reference_control_0_positions|exact reference_control_0_safety|apply rf_alu_rs1_member;exact Bound|exact Eval|exact Step]. Qed.
Lemma rf_alu_rs1_same n inputs path history limit reset time :(n<42)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find(rf_alu_rs1_node n)(history time)=VM.find(rf_alu_rs1_node n)(history(S time)).
Proof. intros Bound Resets Steps Lower Upper.
destruct n as[|n];[apply(reference_control_stable_2102_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2103_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2104_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2105_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2106_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2107_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2108_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2109_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2110_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2111_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2112_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2113_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2114_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2115_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2116_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2117_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2118_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2119_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2120_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2121_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2122_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2123_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2124_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2125_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2126_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2127_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2128_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2129_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2130_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2131_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2132_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2133_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2134_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2135_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2136_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2137_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2138_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2139_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2140_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2141_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2142_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2143_history inputs path history limit reset Resets Steps time(S time));lia|].
lia. Qed.
Lemma rf_alu_rs1_types n invalid history limit time :(n<42)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find(rf_alu_rs1_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)) /\
 (exists v,VM.find(match n with O=>2101|S n=>rf_alu_rs1_node n end)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)).
Proof. intros Bound Steps Source Lower Upper.
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 116%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 125%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 114%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 126%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 112%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 127%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 110%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 128%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 108%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 129%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 106%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 130%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 104%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 131%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 101%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 132%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 98%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 133%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 95%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 134%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 92%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 135%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 89%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 136%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 86%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 137%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 83%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 138%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 80%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 139%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 77%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 140%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 74%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 141%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 72%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 142%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 68%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 143%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 64%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 144%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 60%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 145%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 56%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 146%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 52%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 147%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 48%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 148%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 46%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 149%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 44%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 150%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 42%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 151%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 40%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 152%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 38%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 153%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 35%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 154%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 32%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 155%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 29%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 156%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 27%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 157%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 25%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 158%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 23%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 159%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 20%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 160%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 17%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 161%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 14%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 162%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 11%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 163%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 8%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 164%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 5%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 165%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 2%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
- exact(reference_rs1_types_history invalid history limit 200 Steps Source 166%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs1_rank reference_rs1_ranks nth];lia)Upper).
}
lia. Qed.
Definition rf_alu_rs1_aux_node i :VarOrder.T:=nth 0 [::2035;2036;2037;2040;2041;2042;2045;2046;2047;2077;2078;2081;2082;2085;2086;2144;2145] i.
Definition rf_alu_rs1_aux_expr i:=nth(@Econst VarOrder.T(Fuint 1)[::false]) [::reference_control_expr_2035;reference_control_expr_2036;reference_control_expr_2037;reference_control_expr_2040;reference_control_expr_2041;reference_control_expr_2042;reference_control_expr_2045;reference_control_expr_2046;reference_control_expr_2047;reference_control_expr_2077;reference_control_expr_2078;reference_control_expr_2081;reference_control_expr_2082;reference_control_expr_2085;reference_control_expr_2086;reference_control_expr_2144;reference_control_expr_2145] i.
Lemma rf_alu_rs1_value i inputs path history limit reset time width word :(i<17)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(rf_alu_rs1_aux_expr i)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(rf_alu_rs1_aux_node i)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
destruct i as[|i]. { change(VM.find 2035(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2035_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2035 reference_control_expr_2035);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2035|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2036(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2036_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2036 reference_control_expr_2036);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2036|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2037(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2037_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2037 reference_control_expr_2037);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2037|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2040(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2040_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2040 reference_control_expr_2040);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2040|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2041(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2041_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2041 reference_control_expr_2041);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2041|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2042(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2042_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2042 reference_control_expr_2042);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2042|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2045(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2045_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2045 reference_control_expr_2045);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2045|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2046(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2046_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2046 reference_control_expr_2046);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2046|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2047(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2047_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2047 reference_control_expr_2047);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2047|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2077(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2077_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2077 reference_control_expr_2077);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2077|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2078(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2078_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2078 reference_control_expr_2078);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2078|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2081(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2081_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2081 reference_control_expr_2081);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2081|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2082(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2082_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2082 reference_control_expr_2082);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2082|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2085(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2085_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2085 reference_control_expr_2085);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2085|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2086(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2086_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2086 reference_control_expr_2086);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2086|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2144(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2144_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2144 reference_control_expr_2144);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2144|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2145(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2145_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2145 reference_control_expr_2145);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2145|exact Eval|apply Steps;lia]. }
lia. Qed.
Lemma rf_alu_rs1_raw inputs path history limit reset time instruction lane :(lane<6)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(rf_alu_rs1_yes(rf_alu_rs1_target lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof. intros Lane Resets Steps Lower Upper Source.
destruct lane as[|lane]. {
assert(V2045:VM.find 2045(history time)=Some(Gval(Fuint 25)(drop 0(take 25 instruction)))).
{ eapply(rf_alu_rs1_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2045 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2046:VM.find 2046(history time)=Some(Gval(Fuint 20)(drop 0(take 20 (drop 0(take 25 instruction)))))).
{ eapply(rf_alu_rs1_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2046 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2045. reflexivity. }
assert(V2047:VM.find 2047(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 (drop 0(take 25 instruction)))))))).
{ eapply(rf_alu_rs1_value 8 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2047 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2046. reflexivity. }
cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs1_target nth]. rewrite !drop0 !take_take in V2047;try reflexivity. exact V2047. }
destruct lane as[|lane]. {
assert(V2040:VM.find 2040(history time)=Some(Gval(Fuint 25)(drop 0(take 25 instruction)))).
{ eapply(rf_alu_rs1_value 3 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2040 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2041:VM.find 2041(history time)=Some(Gval(Fuint 20)(drop 0(take 20 (drop 0(take 25 instruction)))))).
{ eapply(rf_alu_rs1_value 4 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2041 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2040. reflexivity. }
assert(V2042:VM.find 2042(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 (drop 0(take 25 instruction)))))))).
{ eapply(rf_alu_rs1_value 5 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2042 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2041. reflexivity. }
cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs1_target nth]. rewrite !drop0 !take_take in V2042;try reflexivity. exact V2042. }
destruct lane as[|lane]. {
assert(V2035:VM.find 2035(history time)=Some(Gval(Fuint 25)(drop 0(take 25 instruction)))).
{ eapply(rf_alu_rs1_value 0 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2035 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2036:VM.find 2036(history time)=Some(Gval(Fuint 20)(drop 0(take 20 (drop 0(take 25 instruction)))))).
{ eapply(rf_alu_rs1_value 1 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2036 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2035. reflexivity. }
assert(V2037:VM.find 2037(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 (drop 0(take 25 instruction)))))))).
{ eapply(rf_alu_rs1_value 2 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2037 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2036. reflexivity. }
cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs1_target nth]. rewrite !drop0 !take_take in V2037;try reflexivity. exact V2037. }
destruct lane as[|lane]. {
assert(V2085:VM.find 2085(history time)=Some(Gval(Fuint 20)(drop 0(take 20 instruction)))).
{ eapply(rf_alu_rs1_value 13 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2085 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2086:VM.find 2086(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 instruction)))))).
{ eapply(rf_alu_rs1_value 14 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2086 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2085. reflexivity. }
cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs1_target nth]. rewrite !drop0 !take_take in V2086;try reflexivity. exact V2086. }
destruct lane as[|lane]. {
assert(V2081:VM.find 2081(history time)=Some(Gval(Fuint 20)(drop 0(take 20 instruction)))).
{ eapply(rf_alu_rs1_value 11 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2081 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2082:VM.find 2082(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 instruction)))))).
{ eapply(rf_alu_rs1_value 12 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2082 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2081. reflexivity. }
cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs1_target nth]. rewrite !drop0 !take_take in V2082;try reflexivity. exact V2082. }
destruct lane as[|lane]. {
assert(V2077:VM.find 2077(history time)=Some(Gval(Fuint 20)(drop 0(take 20 instruction)))).
{ eapply(rf_alu_rs1_value 9 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2077 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2078:VM.find 2078(history time)=Some(Gval(Fuint 5)(drop 15(take 20 (drop 0(take 20 instruction)))))).
{ eapply(rf_alu_rs1_value 10 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2078 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2077. reflexivity. }
cbn[rf_instruction_address rf_alu_rs1_yes rf_alu_rs1_target nth]. rewrite !drop0 !take_take in V2078;try reflexivity. exact V2078. }
lia. Qed.
Definition rf_alu_rs2_node n :VarOrder.T:=N.of_nat(Nat.add 2597 n).
Definition rf_alu_rs2_decoder n:=nth 0%nat [::14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;34%nat;35%nat;36%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat] n.
Definition rf_alu_rs2_guard n:=reference_instruction_guard(rf_alu_rs2_decoder n).
Definition rf_alu_rs2_yes n :VarOrder.T:=nth 0 [::2590;2589;2588;2587;2586;2585;2584;2583;2582;2581;2580;2579;2578;2577;2576;2575;2574;2573;2572;2571;2570;2569;2568;2567] n.
Definition rf_alu_rs2_target lane:=nth 0%nat [::0%nat;1%nat;2%nat] lane.
Definition rf_alu_rs2_expression n:=@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T(rf_alu_rs2_guard n)))(@Eref VarOrder.T(@Eid VarOrder.T(rf_alu_rs2_yes n)))(@Eref VarOrder.T(@Eid VarOrder.T(match n with O=>2596|S n=>rf_alu_rs2_node n end))).
Lemma rf_alu_rs2_member n :(n<24)%coq_nat ->List.In(rf_alu_rs2_node n,rf_alu_rs2_expression n)reference_control_2_nodes.
Proof. intro Bound.
destruct n as[|n];[exact reference_control_member_2597|].
destruct n as[|n];[exact reference_control_member_2598|].
destruct n as[|n];[exact reference_control_member_2599|].
destruct n as[|n];[exact reference_control_member_2600|].
destruct n as[|n];[exact reference_control_member_2601|].
destruct n as[|n];[exact reference_control_member_2602|].
destruct n as[|n];[exact reference_control_member_2603|].
destruct n as[|n];[exact reference_control_member_2604|].
destruct n as[|n];[exact reference_control_member_2605|].
destruct n as[|n];[exact reference_control_member_2606|].
destruct n as[|n];[exact reference_control_member_2607|].
destruct n as[|n];[exact reference_control_member_2608|].
destruct n as[|n];[exact reference_control_member_2609|].
destruct n as[|n];[exact reference_control_member_2610|].
destruct n as[|n];[exact reference_control_member_2611|].
destruct n as[|n];[exact reference_control_member_2612|].
destruct n as[|n];[exact reference_control_member_2613|].
destruct n as[|n];[exact reference_control_member_2614|].
destruct n as[|n];[exact reference_control_member_2615|].
destruct n as[|n];[exact reference_control_member_2616|].
destruct n as[|n];[exact reference_control_member_2617|].
destruct n as[|n];[exact reference_control_member_2618|].
destruct n as[|n];[exact reference_control_member_2619|].
destruct n as[|n];[exact reference_control_member_2620|].
lia. Qed.
Lemma rf_alu_rs2_step n invalid old result word :(n<24)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(rf_alu_rs2_expression n)old old=Some(Gval(Fuint 5)word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find(rf_alu_rs2_node n)result=Some(Gval(Fuint 5)word).
Proof. intros Bound Eval Step. eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes _ (rf_alu_rs2_expression n));[exact reference_control_2_positions|exact reference_control_2_safety|apply rf_alu_rs2_member;exact Bound|exact Eval|exact Step]. Qed.
Lemma rf_alu_rs2_same n inputs path history limit reset time :(n<24)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find(rf_alu_rs2_node n)(history time)=VM.find(rf_alu_rs2_node n)(history(S time)).
Proof. intros Bound Resets Steps Lower Upper.
destruct n as[|n];[apply(reference_control_stable_2597_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2598_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2599_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2600_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2601_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2602_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2603_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2604_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2605_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2606_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2607_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2608_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2609_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2610_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2611_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2612_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2613_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2614_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2615_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2616_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2617_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2618_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2619_history inputs path history limit reset Resets Steps time(S time));lia|].
destruct n as[|n];[apply(reference_control_stable_2620_history inputs path history limit reset Resets Steps time(S time));lia|].
lia. Qed.
Lemma rf_alu_rs2_types n invalid history limit time :(n<24)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find(rf_alu_rs2_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)) /\
 (exists v,VM.find(match n with O=>2596|S n=>rf_alu_rs2_node n end)(history time)=Some v /\type_of_val v=Gtyp(Fuint 5)).
Proof. intros Bound Steps Source Lower Upper.
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 56%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 62%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 55%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 63%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 54%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 64%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 53%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 65%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 52%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 66%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 51%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 67%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 50%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 68%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 49%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 69%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 48%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 70%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 47%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 71%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 46%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 72%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 45%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 73%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 44%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 74%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 43%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 75%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 42%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 76%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 41%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 77%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 40%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 78%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 39%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 79%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 38%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 80%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 37%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 81%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 36%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 82%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 35%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 83%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 34%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 84%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 33%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
- exact(reference_rs2_types_history invalid history limit 200 Steps Source 85%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs2_rank reference_rs2_ranks nth];lia)Upper).
}
lia. Qed.
Definition rf_alu_rs2_aux_node i :VarOrder.T:=nth 0 [::2035;2040;2045;2588;2589;2590;2621;2622] i.
Definition rf_alu_rs2_aux_expr i:=nth(@Econst VarOrder.T(Fuint 1)[::false]) [::reference_control_expr_2035;reference_control_expr_2040;reference_control_expr_2045;reference_control_expr_2588;reference_control_expr_2589;reference_control_expr_2590;reference_control_expr_2621;reference_control_expr_2622] i.
Lemma rf_alu_rs2_value i inputs path history limit reset time width word :(i<8)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(rf_alu_rs2_aux_expr i)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(rf_alu_rs2_aux_node i)(history time)=Some(Gval(Fuint width)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
destruct i as[|i]. { change(VM.find 2035(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2035_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2035 reference_control_expr_2035);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2035|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2040(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2040_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2040 reference_control_expr_2040);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2040|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2045(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2045_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2045 reference_control_expr_2045);[exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2045|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2588(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2588_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2588 reference_control_expr_2588);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2588|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2589(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2589_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2589 reference_control_expr_2589);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2589|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2590(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2590_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2590 reference_control_expr_2590);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2590|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2621(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2621_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2621 reference_control_expr_2621);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2621|exact Eval|apply Steps;lia]. }
destruct i as[|i]. { change(VM.find 2622(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_2622_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2622 reference_control_expr_2622);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2622|exact Eval|apply Steps;lia]. }
lia. Qed.
Lemma rf_alu_rs2_raw inputs path history limit reset time instruction lane :(lane<3)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(rf_alu_rs2_yes(rf_alu_rs2_target lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof. intros Lane Resets Steps Lower Upper Source.
destruct lane as[|lane]. {
assert(V2045:VM.find 2045(history time)=Some(Gval(Fuint 25)(drop 0(take 25 instruction)))).
{ eapply(rf_alu_rs2_value 2 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2045 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2590:VM.find 2590(history time)=Some(Gval(Fuint 5)(drop 20(take 25 (drop 0(take 25 instruction)))))).
{ eapply(rf_alu_rs2_value 5 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2590 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2045. reflexivity. }
cbn[rf_instruction_address rf_alu_rs2_yes rf_alu_rs2_target nth]. rewrite !drop0 !take_take in V2590;try reflexivity. exact V2590. }
destruct lane as[|lane]. {
assert(V2040:VM.find 2040(history time)=Some(Gval(Fuint 25)(drop 0(take 25 instruction)))).
{ eapply(rf_alu_rs2_value 1 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2040 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2589:VM.find 2589(history time)=Some(Gval(Fuint 5)(drop 20(take 25 (drop 0(take 25 instruction)))))).
{ eapply(rf_alu_rs2_value 4 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2589 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2040. reflexivity. }
cbn[rf_instruction_address rf_alu_rs2_yes rf_alu_rs2_target nth]. rewrite !drop0 !take_take in V2589;try reflexivity. exact V2589. }
destruct lane as[|lane]. {
assert(V2035:VM.find 2035(history time)=Some(Gval(Fuint 25)(drop 0(take 25 instruction)))).
{ eapply(rf_alu_rs2_value 0 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2035 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity. }
assert(V2588:VM.find 2588(history time)=Some(Gval(Fuint 5)(drop 20(take 25 (drop 0(take 25 instruction)))))).
{ eapply(rf_alu_rs2_value 3 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2588 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2035. reflexivity. }
cbn[rf_instruction_address rf_alu_rs2_yes rf_alu_rs2_target nth]. rewrite !drop0 !take_take in V2588;try reflexivity. exact V2588. }
lia. Qed.
(* Semantic port composition. *)
Theorem rf_alu_rs1_history inputs path history limit reset time instruction lane :(lane<6)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(rf_alu_rs1_target lane)])) ->
 VM.find 2145(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(rf_alu_rs1_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as Raw.
 assert(Target:(rf_alu_rs1_target lane<42)%coq_nat).
 { do 6(destruct lane as[|lane];[cbn[rf_alu_rs1_target nth];lia|]);lia. }
 assert(Selected:VM.find 2143(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { change(VM.find(rf_alu_rs1_node 41)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))42 (rf_alu_rs1_target lane)5(rf_instruction_address false instruction)2101 rf_alu_rs1_node rf_alu_rs1_guard rf_alu_rs1_yes);[exact Target|exact(rf_instruction_address_size false instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(rf_alu_rs1_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(rf_alu_rs1_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_alu_rs1_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2144(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction))).
 { eapply(rf_alu_rs1_value 15 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs1_aux_expr nth reference_control_expr_2144 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size false instruction Size). }
 eapply(rf_alu_rs1_value 16 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Lemma rf_alu_rs1_decode instruction lane n :(lane<6)%coq_nat ->(n<42)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 N.eqb(reference_instruction_code(rf_alu_rs1_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_alu_rs1_decoder n)))=Nat.eqb n(rf_alu_rs1_target lane).
Proof.
 intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction(rf_bitwise_class lane)(rf_alu_rs1_decoder n)ltac:(do 6(destruct lane as[|lane];[vm_compute;lia|]);lia)ltac:(do 42(destruct n as[|n];[cbn[rf_alu_rs1_decoder nth];lia|]);lia)Match).
 do 6(destruct lane as[|lane];[do 42(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.
Theorem rf_alu_rs2_history inputs path history limit reset time instruction lane :(lane<3)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(rf_alu_rs2_target lane)])) ->
 VM.find 2622(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(rf_alu_rs2_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as Raw.
 assert(Target:(rf_alu_rs2_target lane<24)%coq_nat).
 { do 3(destruct lane as[|lane];[cbn[rf_alu_rs2_target nth];lia|]);lia. }
 assert(Selected:VM.find 2620(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { change(VM.find(rf_alu_rs2_node 23)(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))24 (rf_alu_rs2_target lane)5(rf_instruction_address true instruction)2596 rf_alu_rs2_node rf_alu_rs2_guard rf_alu_rs2_yes);[exact Target|exact(rf_instruction_address_size true instruction Size)| | |exact Guards| | |exact Raw|lia|lia].
 - intros n Bound. exact(rf_alu_rs2_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(rf_alu_rs2_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
 assert(Gate:VM.find 2621(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { eapply(rf_alu_rs2_value 6 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs2_aux_expr nth reference_control_expr_2621 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact(rf_instruction_address_size true instruction Size). }
 eapply(rf_alu_rs2_value 7 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Lemma rf_alu_rs2_decode instruction lane n :(lane<3)%coq_nat ->(n<24)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 N.eqb(reference_instruction_code(rf_alu_rs2_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_alu_rs2_decoder n)))=Nat.eqb n(rf_alu_rs2_target lane).
Proof.
 intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction(rf_bitwise_class lane)(rf_alu_rs2_decoder n)ltac:(do 3(destruct lane as[|lane];[vm_compute;lia|]);lia)ltac:(do 24(destruct n as[|n];[cbn[rf_alu_rs2_decoder nth];lia|]);lia)Match).
 do 3(destruct lane as[|lane];[do 24(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.

Require Import RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory MemoryRequestObservedSemantics LoadTypeCorrespondence ReferenceSecondRegisterRead.
Theorem rf_alu_rs1_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane < 6)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
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
 assert (Guards : forall n,(n<42)%coq_nat ->VM.find(rf_alu_rs1_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(rf_alu_rs1_target lane)])).
 { intros n Bound.
   set (h := fun t:nat => history (match t with O=>9248%nat | S O=>9249%nat | _=>9250%nat end)).
   assert (HS : forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
   { intros [|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
   assert (HI : forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
   { intros [|[|t]] T;unfold h;apply Source;vm_compute;lia. }
   pose proof(reference_instruction_decode_history _ h 2 instruction (rf_alu_rs1_decoder n) ltac:(do 42 (destruct n as [|n];[cbn [rf_alu_rs1_decoder nth];lia|]);lia) HS HI 2 ltac:(lia) ltac:(lia))as Decode.
   rewrite(rf_alu_rs1_decode instruction lane n Lane Bound Load)in Decode. exact Decode. }
 pose proof(rf_alu_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Guards)as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem rf_alu_rs1_bank_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address false instruction)))).
Proof.
 intros Observe Legal Enabled Lane Instruction Match Bank.
 assert(Size:size instruction=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[W V]]. rewrite Instruction in V;inversion V;subst;exact W. }
 eapply(reference_register_read_observed memory inputs k observed bank (rf_instruction_address false instruction));[exact Observe|exact Legal|exact Bank|exact(rf_instruction_address_size false instruction Size)|].
 exact(rf_alu_rs1_observed memory inputs k observed instruction lane Observe Legal Enabled Lane Instruction Match).
Qed.
Theorem rf_alu_rs2_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane < 3)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
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
 assert (Guards : forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n(rf_alu_rs2_target lane)])).
 { intros n Bound.
   set (h := fun t:nat => history (match t with O=>9248%nat | S O=>9249%nat | _=>9250%nat end)).
   assert (HS : forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
   { intros [|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
   assert (HI : forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
   { intros [|[|t]] T;unfold h;apply Source;vm_compute;lia. }
   pose proof(reference_instruction_decode_history _ h 2 instruction (rf_alu_rs2_decoder n) ltac:(do 24 (destruct n as [|n];[cbn [rf_alu_rs2_decoder nth];lia|]);lia) HS HI 2 ltac:(lia) ltac:(lia))as Decode.
   rewrite(rf_alu_rs2_decode instruction lane n Lane Bound Load)in Decode. exact Decode. }
 pose proof(rf_alu_rs2_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Guards)as Value.
 rewrite(reference_control_stable_2622_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
Theorem rf_alu_rs2_bank_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address true instruction)))).
Proof.
 intros Observe Legal Enabled Lane Instruction Match Bank.
 assert(Size:size instruction=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[W V]]. rewrite Instruction in V;inversion V;subst;exact W. }
 eapply(reference_second_register_read_observed memory inputs k observed bank (rf_instruction_address true instruction));[exact Observe|exact Legal|exact Bank|exact(rf_instruction_address_size true instruction Size)|].
 exact(rf_alu_rs2_observed memory inputs k observed instruction lane Observe Legal Enabled Lane Instruction Match).
Qed.
