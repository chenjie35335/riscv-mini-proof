Require Import ReferenceControlNodeCongruence2 ReferenceRedirectSpine DUTRedirectDecode CoreSocModel ComparisonNodes RFALUData RFScalarControl ReferenceBranchImmediate ReferenceImmediateTypes ReferenceLoadImmediate ReferenceControlExpressions ReferenceInstructionDecode LoadImmediateSemantics ReferenceLoadSemantics.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_i_low_node n :VarOrder.T:=N.of_nat(Nat.add 2232 n).
Definition rf_i_low_decoder n :=nth 0%nat [::3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;22%nat;29%nat;30%nat;31%nat;32%nat;33%nat;37%nat;38%nat;39%nat] n.
Definition rf_i_low_guard n :=reference_instruction_guard(rf_i_low_decoder n).
Definition rf_i_low_yes n :VarOrder.T:=nth 0 [::2225;2224;2223;2222;2221;2220;2219;2218;2217;2216;2215;2214;2213;2212;2211] n.
Definition rf_i_low_expression n :=@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T(rf_i_low_guard n)))(@Eref VarOrder.T(@Eid VarOrder.T(rf_i_low_yes n)))(@Eref VarOrder.T(@Eid VarOrder.T(match n with O=>2231|S n=>rf_i_low_node n end))).
Lemma rf_i_low_value n inputs path history limit reset time word :(n<15)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(rf_i_low_expression n)(history time)(history time)=Some(Gval(Fuint 12)word)) ->
 VM.find(rf_i_low_node n)(history time)=Some(Gval(Fuint 12)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
destruct n as[|n];[exact(reference_immediate_value_history 45 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 46 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 47 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 48 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 49 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 50 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 51 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 52 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 53 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 54 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 55 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 56 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 57 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 58 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 59 inputs path history limit reset time 12 word ltac:(lia)Resets Steps Lower Upper Eval)|].
lia. Qed.
Lemma rf_i_low_types n invalid history limit time :(n<15)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find(rf_i_low_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint 12)) /\
 (exists v,VM.find(match n with O=>2231|S n=>rf_i_low_node n end)(history time)=Some v /\type_of_val v=Gtyp(Fuint 12)).
Proof. intros Bound Steps Source Lower Upper.
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 38%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 44%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 37%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 45%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 36%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 46%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 35%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 47%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 34%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 48%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 33%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 49%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 32%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 50%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 31%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 51%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 30%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 52%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 29%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 53%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 28%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 54%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 27%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 55%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 26%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 56%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 25%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 57%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 24%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 58%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
lia. Qed.
Lemma rf_i_low_decode instruction lane n :(lane<3)%coq_nat ->(n<15)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(Nat.add 3 lane))=reference_instruction_code(Nat.add 3 lane) ->
 N.eqb(reference_instruction_code(rf_i_low_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_i_low_decoder n)))=Nat.eqb n lane.
Proof. intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction(Nat.add 3 lane)(rf_i_low_decoder n)ltac:(lia)ltac:(do 15(destruct n as[|n];[vm_compute;lia|]);lia)Match).
 do 3(destruct lane as[|lane];[do 15(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.
Definition rf_i_high_node n :VarOrder.T:=N.of_nat(Nat.add 2524 n).
Definition rf_i_high_decoder n :=nth 0%nat [::3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;21%nat;22%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat] n.
Definition rf_i_high_guard n :=reference_instruction_guard(rf_i_high_decoder n).
Definition rf_i_high_yes n :VarOrder.T:=nth 0 [::2508;2504;2500;2496;2492;2488;2484;2482;2470;2449;2445;2437;2429;2421;2413;2405;2317;2313;2309;2305;2301;2297;2292;2287;2260;2256;2252] n.
Definition rf_i_high_expression n :=@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T(rf_i_high_guard n)))(@Eref VarOrder.T(@Eid VarOrder.T(rf_i_high_yes n)))(@Eref VarOrder.T(@Eid VarOrder.T(match n with O=>2523|S n=>rf_i_high_node n end))).
Lemma rf_i_high_value n inputs path history limit reset time word :(n<27)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(rf_i_high_expression n)(history time)(history time)=Some(Gval(Fuint 32)word)) ->
 VM.find(rf_i_high_node n)(history time)=Some(Gval(Fuint 32)word).
Proof. intros Bound Resets Steps Lower Upper Eval.
destruct n as[|n];[exact(reference_immediate_value_history 275 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 276 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 277 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 278 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 279 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 280 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 281 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 282 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 283 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 284 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 285 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 286 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 287 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 288 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 289 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 290 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 291 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 292 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 293 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 294 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 295 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 296 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 297 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 298 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 299 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 300 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
destruct n as[|n];[exact(reference_immediate_value_history 301 inputs path history limit reset time 32 word ltac:(lia)Resets Steps Lower Upper Eval)|].
lia. Qed.
Lemma rf_i_high_types n invalid history limit time :(n<27)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 (exists v,VM.find(rf_i_high_yes n)(history time)=Some v /\type_of_val v=Gtyp(Fuint 32)) /\
 (exists v,VM.find(match n with O=>2523|S n=>rf_i_high_node n end)(history time)=Some v /\type_of_val v=Gtyp(Fuint 32)).
Proof. intros Bound Steps Source Lower Upper.
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 265%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 274%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 263%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 275%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 261%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 276%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 259%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 277%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 257%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 278%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 255%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 279%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 253%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 280%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 251%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 281%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 243%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 282%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 224%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 283%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 222%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 284%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 216%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 285%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 210%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 286%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 204%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 287%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 198%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 288%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 192%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 289%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 108%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 290%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 106%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 291%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 104%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 292%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 102%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 293%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 100%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 294%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 98%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 295%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 95%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 296%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 92%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 297%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 67%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 298%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 65%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 299%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
destruct n as[|n]. { split.
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 63%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
- exact(reference_immediate_types_history invalid history limit 200 Steps Source 300%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)Upper).
}
lia. Qed.
Lemma rf_i_high_decode instruction lane n :(lane<3)%coq_nat ->(n<27)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(Nat.add 3 lane))=reference_instruction_code(Nat.add 3 lane) ->
 N.eqb(reference_instruction_code(rf_i_high_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_i_high_decoder n)))=Nat.eqb n lane.
Proof. intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction(Nat.add 3 lane)(rf_i_high_decoder n)ltac:(lia)ltac:(do 27(destruct n as[|n];[vm_compute;lia|]);lia)Match).
 do 3(destruct lane as[|lane];[do 27(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.
(* Actual I-format semantics. *)
Require Import ReferenceControlStabilityHistory ReferenceControlNodeCertificates2.
Lemma rf_i_low_selected inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word=12%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 VM.find(rf_i_low_yes lane)(history time)=Some(Gval(Fuint 12)word) ->
 VM.find 2248(history time)=Some(Gval(Fuint 12)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards Raw.
 assert(Selected:VM.find 2246(history time)=Some(Gval(Fuint 12)word)).
 { change(VM.find(rf_i_low_node 14)(history time)=Some(Gval(Fuint 12)word)).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history time)15 lane 12 word 2231 rf_i_low_node rf_i_low_guard rf_i_low_yes);[lia|exact Size| | |exact Guards| | |exact Raw|lia|lia].
 - intros;reflexivity.
 - intros n Bound value Eval. exact(rf_i_low_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_low_types n _ history limit time Bound Steps Source Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_i_low_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(Gate:VM.find 2247(history time)=Some(Gval(Fuint 12)word)).
 { eapply(reference_immediate_value_history 60 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2247 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact Size. }
 eapply(reference_immediate_value_history 61 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Lemma rf_i_high_selected inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 VM.find(rf_i_high_yes lane)(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards Raw.
 assert(Selected:VM.find 2550(history time)=Some(Gval(Fuint 32)word)).
 { change(VM.find(rf_i_high_node 26)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history time)27 lane 32 word 2523 rf_i_high_node rf_i_high_guard rf_i_high_yes);[lia|exact Size| | |exact Guards| | |exact Raw|lia|lia].
 - intros;reflexivity.
 - intros n Bound value Eval. exact(rf_i_high_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_high_types n _ history limit time Bound Steps Source Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_i_high_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }
 assert(Gate:VM.find 2551(history time)=Some(Gval(Fuint 32)word)).
 { eapply(reference_immediate_value_history 302 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. apply dut_decode_adapt;exact Size. }
 eapply(reference_immediate_value_history 303 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
Lemma rf_i_raw inputs path history limit reset time instruction lane :(lane<3)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(rf_i_low_yes lane)(history time)=Some(Gval(Fuint 12)(drop 20(take 32 instruction))).
Proof. intros Lane Resets Steps Lower Upper Source.
destruct lane as[|lane]. { eapply(reference_immediate_value_history 38 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2225 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }
destruct lane as[|lane]. { eapply(reference_immediate_value_history 37 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2224 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }
destruct lane as[|lane]. { eapply(reference_immediate_value_history 36 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2223 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source;reflexivity. }
lia. Qed.
Lemma rf_i_sign inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word=12%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 2248(history time)=Some(Gval(Fuint 12)word) ->
 VM.find(rf_i_high_yes lane)(history time)=Some(Gval(Fuint 32)(sext_to 32 word)).
Proof. intros Lane Size Resets Steps Lower Upper Low.
destruct lane as[|lane]. {
assert(V0:VM.find 2505(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2505_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2505 reference_control_expr_2505);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2505| |apply Steps;lia]. intro site. cbn[reference_control_expr_2505 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2506(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2506_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2506 reference_control_expr_2506);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2506| |apply Steps;lia]. intro site. cbn[reference_control_expr_2506 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2507(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 264 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2507 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2508(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 265 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2508 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3. }
destruct lane as[|lane]. {
assert(V0:VM.find 2501(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2501_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2501 reference_control_expr_2501);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2501| |apply Steps;lia]. intro site. cbn[reference_control_expr_2501 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2502(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2502_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2502 reference_control_expr_2502);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2502| |apply Steps;lia]. intro site. cbn[reference_control_expr_2502 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2503(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 262 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2503 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2504(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 263 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2504 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3. }
destruct lane as[|lane]. {
assert(V0:VM.find 2497(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2497_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2497 reference_control_expr_2497);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2497| |apply Steps;lia]. intro site. cbn[reference_control_expr_2497 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite Low. change(Some(Gval(Fuint 1)(drop(12-1)%nat(take 12 word)))=Some(Gval(Fuint 1)[::msb word])). rewrite(reference_load_sign_bit 12 word Size(eq_refl true));reflexivity. }
assert(V1:VM.find 2498(history time)=Some(Gval(Fuint 1)([::msb word]))).
{ rewrite(reference_control_stable_2498_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)). eapply(reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2498 reference_control_expr_2498);[exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2498| |apply Steps;lia]. intro site. cbn[reference_control_expr_2498 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V0;reflexivity. }
assert(V2:VM.find 2499(history time)=Some(Gval(Fuint 20)(nseq 20(msb word)))).
{ eapply(reference_immediate_value_history 260 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2499 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V1;destruct(msb word);reflexivity. }
assert(V3:VM.find 2500(history time)=Some(Gval(Fuint 32)(sext_to 32 word))).
{ eapply(reference_immediate_value_history 261 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site. cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_2500 eval_hfexpr_validif_policy eval_href_validif_policy].
rewrite V2 Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size;reflexivity. }
exact V3. }
lia. Qed.
Theorem rf_i_immediate_history inputs path history limit reset time instruction lane :
 (lane<3)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 (forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled LowGuards HighGuards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 assert(RawSize:size(drop 20(take 32 instruction))=12%nat).
 { rewrite size_drop size_take Size;reflexivity. }
 pose proof(rf_i_raw inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia)))as Raw.
 pose proof(rf_i_low_selected inputs path history limit reset time(drop 20(take 32 instruction))lane Lane RawSize Resets Steps Typed Lower Upper Enabled LowGuards Raw)as Low.
 pose proof(rf_i_sign inputs path history limit reset time(drop 20(take 32 instruction))lane Lane RawSize Resets Steps Lower Upper Low)as Sign.
 exact(rf_i_high_selected inputs path history limit reset time(load_i_immediate instruction)lane Lane(load_i_immediate_size instruction Size)Resets Steps Typed Lower Upper Enabled HighGuards Sign).
Qed.
Require Import ReferenceIllegalObserved LoadPipelineClassification FormalInstructionResetConstants RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory MemoryRequestObservedSemantics LoadTypeCorrespondence.
Lemma rf_bitwise_reference_enabled memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<6)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset Lane Instruction Match.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Late Nop]].
 destruct bit.
 - specialize(Nop(Logic.eq_refl _)). rewrite Nop in Instruction;inversion Instruction;subst instruction.
 do 6(destruct lane as[|lane];[vm_compute in Match;discriminate|]);lia.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late).
Qed.
Theorem rf_bitwise_immediate_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(Nat.add 3 lane))=reference_instruction_code(Nat.add 3 lane) ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(load_i_immediate instruction)).
Proof.
 intros Observe Legal Reset Lane Instruction Match.
 assert(Enabled:VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true])).
 { apply(rf_bitwise_reference_enabled memory inputs k observed instruction(Nat.add 3 lane)Observe Legal Reset ltac:(lia)Instruction).
 do 3(destruct lane as[|lane];[exact Match|]);lia. }
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Inst:forall t,(t<=9259)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite<-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Instruction. }
 assert(Enable:forall t,(195<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::true])).
 { intros t Lower Upper. rewrite(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat ltac:(lia)ltac:(lia)Upper ltac:(lia))Last;exact Enabled. }
 assert(Source:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Lower Upper. exact(memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert(Decode:forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)(history 9250%nat)=Some(Gval(Fuint 1)[::N.eqb(reference_instruction_code row)(N.land(to_N instruction)(reference_instruction_mask row))])).
 { intros row Row. set(h:=fun t:nat=>history(match t with O=>9248%nat|S O=>9249%nat|_=>9250%nat end)).
 assert(HS:forall t,(t<2)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h t)false(h t)flat_statements=Some(h(S t))).
 { intros[|[|t]] T;[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia]. }
 assert(HI:forall t,(t<=2)%coq_nat ->VM.find 1884(h t)=Some(Gval(Fuint 32)instruction)).
 { intros[|[|t]] T;unfold h;apply Source;vm_compute;lia. }
 exact(reference_instruction_decode_history _ h 2 instruction row Row HS HI 2 ltac:(lia)ltac:(lia)). }
 assert(Low:forall n,(n<15)%coq_nat ->VM.find(rf_i_low_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n lane])).
 { intros n Bound. unfold rf_i_low_guard. rewrite(Decode (rf_i_low_decoder n)ltac:(do 15(destruct n as[|n];[vm_compute;lia|]);lia))(rf_i_low_decode instruction lane n Lane Bound Match);reflexivity. }
 assert(High:forall n,(n<27)%coq_nat ->VM.find(rf_i_high_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n lane])).
 { intros n Bound. unfold rf_i_high_guard. rewrite(Decode (rf_i_high_decoder n)ltac:(do 27(destruct n as[|n];[vm_compute;lia|]);lia))(rf_i_high_decode instruction lane n Lane Bound Match);reflexivity. }
 pose proof(rf_i_immediate_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)(Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))Low High)as Value.
 rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value;exact Value.
Qed.
