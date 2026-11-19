Require Import ReferenceControlRegisters CoreSocModel ComparisonNodes ReferenceBankCycleStability ReferenceControlStabilityHistory SharedLoadInput RFWritebackSelection.
From Coq Require Import NArith List Lia Arith.Wf_nat PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem ref_bank_raw_history invalid history limit raw :size raw=32%nat ->
 VM.find 9222(history 0%nat)=Some(Gval(Fuint 32)raw) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3347(history t)=Some(Gval(Fuint 32)raw).
Proof.
 intros Size Initial Steps t Lower Upper.
 pose proof(reference_control_register_history_same invalid history limit 9222 rf_load_raw_register Steps(Nat.sub t 9)ltac:(lia))as Hold.
 rewrite Initial in Hold.
 destruct(shared_load_same_inputs invalid(fun i=>history(Nat.add(Nat.sub t 9)i))raw Size ltac:(change(VM.find 9222(history(Nat.add(Nat.sub t 9)0))=Some(Gval(Fuint 32)raw));rewrite Nat.add_0_r;exact Hold)ltac:(intros i Bound;cbv beta;rewrite Nat.add_succ_r;apply Steps;lia))as[_ Result].
 replace(Nat.add(Nat.sub t 9)9)with t in Result by lia. exact Result.
Qed.
(* Shared existing cuts. *)
Theorem ref_bank_cycle_cut_facts inputs path history limit bit raw :size raw=32%nat ->
 VM.find 9222(history 0%nat)=Some(Gval(Fuint 32)raw) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall node,List.In node ref_bank_cycle_cuts ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value ground,VM.find node(history t)=Some value /\type_of_val value=Gtyp ground) /\
 (forall t u,(200<=t)%coq_nat ->(200<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find node(history t)=VM.find node(history u)).
Proof. intros Size Initial Resets Steps node Member.
 cbn[ref_bank_cycle_cuts List.In]in Member. repeat destruct Member as[<-|Member];try contradiction.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1707_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1707_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1884_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1884_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1886_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1886_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1889_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1889_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1891_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1891_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1894_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1894_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1896_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1896_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1899_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1899_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1901_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1901_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1904_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1904_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1906_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1906_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1909_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1909_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1911_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1911_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1914_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1914_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1916_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1916_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1919_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1919_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1921_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1921_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1924_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1924_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1926_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1926_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1929_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1929_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1930_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1930_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1933_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1933_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1934_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1934_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1937_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1937_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1938_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1938_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1955_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1955_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1958_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1958_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1959_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1959_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1962_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1962_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1963_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1963_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1966_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1966_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1967_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1967_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1970_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1970_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1971_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1971_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2010_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2010_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2011_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2011_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2014_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2014_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2016_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2016_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2019_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2019_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2021_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2021_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2024_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2024_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2026_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2026_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2029_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2029_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2031_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2031_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2034_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2034_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2036_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2036_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2039_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2039_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2041_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2041_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2044_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2044_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2046_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2046_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2049_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2049_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2051_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2051_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2054_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2054_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2056_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2056_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2059_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2059_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2061_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2061_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2064_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2064_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2065_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2065_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2068_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2068_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2069_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2069_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2072_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2072_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2073_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2073_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2076_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2076_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2077_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2077_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2080_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2080_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2081_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2081_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2084_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2084_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2085_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2085_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2088_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2088_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2089_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2089_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2092_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2092_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2093_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2093_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2096_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2096_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2097_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2097_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2209_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2209_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2357_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2357_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2454_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2454_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2472_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2472_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2475_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2475_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2552_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2552_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2804_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2804_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2812_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2812_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. exists(Gval(Fuint 32)raw),(Fuint 32). split;[apply(ref_bank_raw_history _ history limit raw Size Initial Steps);lia|reflexivity].
 + intros t u Lower Other Upper OtherUpper. rewrite(ref_bank_raw_history _ history limit raw Size Initial Steps t ltac:(lia)Upper)(ref_bank_raw_history _ history limit raw Size Initial Steps u ltac:(lia)OtherUpper);reflexivity.
Qed.
