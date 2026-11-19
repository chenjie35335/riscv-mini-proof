Require Import RFReferenceNopHistory ReferenceBankCycleInputs RFReferenceWriteEffect RFReferenceNopStorageCertificates ReferenceControlStabilityHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition ref_bank_control_nodes := [::2096;2092;2088;2084;2080;2076;2072;2068;2064;2475;2472;2059;2054;2049;2044;2039;2034;2029;2024;2019;2014;2357;2010;1970;1966;1962;1958;1886;1924;1919;1914;1909;1904;1899;1894;1889;2966;2949;2679;2664;2649;2565;1707].
Definition ref_bank_controls_concrete env :=forall node,List.In node ref_bank_control_nodes ->VM.find node env=Some(Gval(Fuint 1)[::ref_write_bit env node]).
Lemma ref_bank_guard_member stage :(stage<36)%coq_nat ->List.In(rf_reference_chain_guard stage)ref_bank_control_nodes.
Proof. intro Bound. do 36(destruct stage as[|stage];[vm_compute;tauto|]);lia. Qed.
Lemma ref_bank_permission_member stage :(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->List.In(rf_reference_permission_node stage)ref_bank_control_nodes.
Proof. intro Bound. do 36(destruct stage as[|stage];[vm_compute;intuition discriminate|]);lia. Qed.
Theorem ref_bank_controls_stable inputs path history limit bit :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall node,List.In node ref_bank_control_nodes ->forall t u,(200<=t)%coq_nat ->(200<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find node(history t)=VM.find node(history u).
Proof.
 intros Resets Steps node Member t u Lower Other Upper OtherUpper.
 cbn [ref_bank_control_nodes List.In]in Member.
 repeat destruct Member as[<-|Member];try contradiction.
 - apply(reference_control_stable_2096_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2092_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2088_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2084_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2080_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2076_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2072_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2068_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2064_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2475_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2472_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2059_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2054_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2049_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2044_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2039_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2034_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2029_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2024_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2019_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2014_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2357_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2010_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1970_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1966_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1962_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1958_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1886_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1924_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1919_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1914_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1909_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1904_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1899_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1894_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1889_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2966_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2949_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2679_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2664_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2649_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_2565_history inputs path history limit bit Resets Steps t u);lia.
 - apply(reference_control_stable_1707_history inputs path history limit bit Resets Steps t u);lia.
Qed.
