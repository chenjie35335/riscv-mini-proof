Require Import JointRegisterCommits2 JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6 CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rfa_reset_commit_875 invalid old current result old_value word :
 VM.find 875 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1109 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 875 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 884 flat_statements joint_register_875_decl joint_register_875_mid joint_register_875_tail
 875 joint_register_875_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1109)) (@Eref VarOrder.T (@Eid VarOrder.T 1045)) invalid flat_memories old current result old_value 32
 joint_register_875_position joint_register_875_split joint_register_875_straight joint_register_875_mid_safe joint_register_875_tail_safe Old Typed joint_register_875_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1109)) (@Eref VarOrder.T (@Eid VarOrder.T 1045))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1109 1045 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7323_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7323)))).
Definition rfa_register_7323_decl := match straight_drop 7495 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7323_tail := match straight_drop 7914 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7323_mid := take_statements 418 rfa_register_7323_decl.
Lemma rfa_register_7323_position : straight_drop 7494 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7323 rfa_register_7323_reg) rfa_register_7323_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7323_split : rfa_register_7323_decl = statement_append rfa_register_7323_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7323) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7418)) (@Eref VarOrder.T (@Eid VarOrder.T 1811)))) rfa_register_7323_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7323_straight : straight_statements rfa_register_7323_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7323_mid_safe : formal_typed_suffix_safe flat_memories 7323 rfa_register_7323_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7323_tail_safe : formal_typed_suffix_safe flat_memories 7323 rfa_register_7323_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7323_identity : register_identity_b 7323 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7323 invalid old current result old_value word :
 VM.find 7323 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7418 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7323 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7494 flat_statements rfa_register_7323_decl rfa_register_7323_mid rfa_register_7323_tail
 7323 rfa_register_7323_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7418)) (@Eref VarOrder.T (@Eid VarOrder.T 1811)) invalid flat_memories old current result old_value 32
 rfa_register_7323_position rfa_register_7323_split rfa_register_7323_straight rfa_register_7323_mid_safe rfa_register_7323_tail_safe Old Typed rfa_register_7323_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7418)) (@Eref VarOrder.T (@Eid VarOrder.T 1811))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7418 1811 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_876 invalid old current result old_value word :
 VM.find 876 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1110 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 876 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 885 flat_statements joint_register_876_decl joint_register_876_mid joint_register_876_tail
 876 joint_register_876_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1110)) (@Eref VarOrder.T (@Eid VarOrder.T 1046)) invalid flat_memories old current result old_value 32
 joint_register_876_position joint_register_876_split joint_register_876_straight joint_register_876_mid_safe joint_register_876_tail_safe Old Typed joint_register_876_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1110)) (@Eref VarOrder.T (@Eid VarOrder.T 1046))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1110 1046 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7324_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7324)))).
Definition rfa_register_7324_decl := match straight_drop 7496 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7324_tail := match straight_drop 7915 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7324_mid := take_statements 418 rfa_register_7324_decl.
Lemma rfa_register_7324_position : straight_drop 7495 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7324 rfa_register_7324_reg) rfa_register_7324_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7324_split : rfa_register_7324_decl = statement_append rfa_register_7324_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7324) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7420)) (@Eref VarOrder.T (@Eid VarOrder.T 1812)))) rfa_register_7324_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7324_straight : straight_statements rfa_register_7324_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7324_mid_safe : formal_typed_suffix_safe flat_memories 7324 rfa_register_7324_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7324_tail_safe : formal_typed_suffix_safe flat_memories 7324 rfa_register_7324_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7324_identity : register_identity_b 7324 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7324 invalid old current result old_value word :
 VM.find 7324 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7420 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7324 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7495 flat_statements rfa_register_7324_decl rfa_register_7324_mid rfa_register_7324_tail
 7324 rfa_register_7324_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7420)) (@Eref VarOrder.T (@Eid VarOrder.T 1812)) invalid flat_memories old current result old_value 32
 rfa_register_7324_position rfa_register_7324_split rfa_register_7324_straight rfa_register_7324_mid_safe rfa_register_7324_tail_safe Old Typed rfa_register_7324_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7420)) (@Eref VarOrder.T (@Eid VarOrder.T 1812))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7420 1812 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_877 invalid old current result old_value word :
 VM.find 877 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1111 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 877 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 886 flat_statements joint_register_877_decl joint_register_877_mid joint_register_877_tail
 877 joint_register_877_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1111)) (@Eref VarOrder.T (@Eid VarOrder.T 1047)) invalid flat_memories old current result old_value 32
 joint_register_877_position joint_register_877_split joint_register_877_straight joint_register_877_mid_safe joint_register_877_tail_safe Old Typed joint_register_877_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1111)) (@Eref VarOrder.T (@Eid VarOrder.T 1047))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1111 1047 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7325_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7325)))).
Definition rfa_register_7325_decl := match straight_drop 7497 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7325_tail := match straight_drop 7916 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7325_mid := take_statements 418 rfa_register_7325_decl.
Lemma rfa_register_7325_position : straight_drop 7496 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7325 rfa_register_7325_reg) rfa_register_7325_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7325_split : rfa_register_7325_decl = statement_append rfa_register_7325_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7325) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7422)) (@Eref VarOrder.T (@Eid VarOrder.T 1813)))) rfa_register_7325_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7325_straight : straight_statements rfa_register_7325_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7325_mid_safe : formal_typed_suffix_safe flat_memories 7325 rfa_register_7325_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7325_tail_safe : formal_typed_suffix_safe flat_memories 7325 rfa_register_7325_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7325_identity : register_identity_b 7325 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7325 invalid old current result old_value word :
 VM.find 7325 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7422 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7325 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7496 flat_statements rfa_register_7325_decl rfa_register_7325_mid rfa_register_7325_tail
 7325 rfa_register_7325_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7422)) (@Eref VarOrder.T (@Eid VarOrder.T 1813)) invalid flat_memories old current result old_value 32
 rfa_register_7325_position rfa_register_7325_split rfa_register_7325_straight rfa_register_7325_mid_safe rfa_register_7325_tail_safe Old Typed rfa_register_7325_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7422)) (@Eref VarOrder.T (@Eid VarOrder.T 1813))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7422 1813 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_878 invalid old current result old_value word :
 VM.find 878 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1112 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 878 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 887 flat_statements joint_register_878_decl joint_register_878_mid joint_register_878_tail
 878 joint_register_878_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1112)) (@Eref VarOrder.T (@Eid VarOrder.T 1048)) invalid flat_memories old current result old_value 32
 joint_register_878_position joint_register_878_split joint_register_878_straight joint_register_878_mid_safe joint_register_878_tail_safe Old Typed joint_register_878_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1112)) (@Eref VarOrder.T (@Eid VarOrder.T 1048))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1112 1048 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7326_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7326)))).
Definition rfa_register_7326_decl := match straight_drop 7498 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7326_tail := match straight_drop 7917 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7326_mid := take_statements 418 rfa_register_7326_decl.
Lemma rfa_register_7326_position : straight_drop 7497 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7326 rfa_register_7326_reg) rfa_register_7326_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7326_split : rfa_register_7326_decl = statement_append rfa_register_7326_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7326) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7424)) (@Eref VarOrder.T (@Eid VarOrder.T 1814)))) rfa_register_7326_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7326_straight : straight_statements rfa_register_7326_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7326_mid_safe : formal_typed_suffix_safe flat_memories 7326 rfa_register_7326_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7326_tail_safe : formal_typed_suffix_safe flat_memories 7326 rfa_register_7326_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7326_identity : register_identity_b 7326 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7326 invalid old current result old_value word :
 VM.find 7326 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7424 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7326 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7497 flat_statements rfa_register_7326_decl rfa_register_7326_mid rfa_register_7326_tail
 7326 rfa_register_7326_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7424)) (@Eref VarOrder.T (@Eid VarOrder.T 1814)) invalid flat_memories old current result old_value 32
 rfa_register_7326_position rfa_register_7326_split rfa_register_7326_straight rfa_register_7326_mid_safe rfa_register_7326_tail_safe Old Typed rfa_register_7326_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7424)) (@Eref VarOrder.T (@Eid VarOrder.T 1814))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7424 1814 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
