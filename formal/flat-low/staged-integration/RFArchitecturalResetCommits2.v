Require Import JointRegisterCommits2 JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6 CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rfa_reset_commit_859 invalid old current result old_value word :
 VM.find 859 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1093 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 859 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 868 flat_statements joint_register_859_decl joint_register_859_mid joint_register_859_tail
 859 joint_register_859_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1093)) (@Eref VarOrder.T (@Eid VarOrder.T 1029)) invalid flat_memories old current result old_value 32
 joint_register_859_position joint_register_859_split joint_register_859_straight joint_register_859_mid_safe joint_register_859_tail_safe Old Typed joint_register_859_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1093)) (@Eref VarOrder.T (@Eid VarOrder.T 1029))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1093 1029 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7307_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7307)))).
Definition rfa_register_7307_decl := match straight_drop 7479 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7307_tail := match straight_drop 7898 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7307_mid := take_statements 418 rfa_register_7307_decl.
Lemma rfa_register_7307_position : straight_drop 7478 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7307 rfa_register_7307_reg) rfa_register_7307_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7307_split : rfa_register_7307_decl = statement_append rfa_register_7307_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7307) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7386)) (@Eref VarOrder.T (@Eid VarOrder.T 1795)))) rfa_register_7307_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7307_straight : straight_statements rfa_register_7307_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7307_mid_safe : formal_typed_suffix_safe flat_memories 7307 rfa_register_7307_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7307_tail_safe : formal_typed_suffix_safe flat_memories 7307 rfa_register_7307_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7307_identity : register_identity_b 7307 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7307 invalid old current result old_value word :
 VM.find 7307 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7386 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7307 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7478 flat_statements rfa_register_7307_decl rfa_register_7307_mid rfa_register_7307_tail
 7307 rfa_register_7307_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7386)) (@Eref VarOrder.T (@Eid VarOrder.T 1795)) invalid flat_memories old current result old_value 32
 rfa_register_7307_position rfa_register_7307_split rfa_register_7307_straight rfa_register_7307_mid_safe rfa_register_7307_tail_safe Old Typed rfa_register_7307_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7386)) (@Eref VarOrder.T (@Eid VarOrder.T 1795))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7386 1795 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_860 invalid old current result old_value word :
 VM.find 860 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1094 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 860 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 869 flat_statements joint_register_860_decl joint_register_860_mid joint_register_860_tail
 860 joint_register_860_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1094)) (@Eref VarOrder.T (@Eid VarOrder.T 1030)) invalid flat_memories old current result old_value 32
 joint_register_860_position joint_register_860_split joint_register_860_straight joint_register_860_mid_safe joint_register_860_tail_safe Old Typed joint_register_860_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1094)) (@Eref VarOrder.T (@Eid VarOrder.T 1030))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1094 1030 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7308_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7308)))).
Definition rfa_register_7308_decl := match straight_drop 7480 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7308_tail := match straight_drop 7899 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7308_mid := take_statements 418 rfa_register_7308_decl.
Lemma rfa_register_7308_position : straight_drop 7479 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7308 rfa_register_7308_reg) rfa_register_7308_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7308_split : rfa_register_7308_decl = statement_append rfa_register_7308_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7308) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7388)) (@Eref VarOrder.T (@Eid VarOrder.T 1796)))) rfa_register_7308_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7308_straight : straight_statements rfa_register_7308_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7308_mid_safe : formal_typed_suffix_safe flat_memories 7308 rfa_register_7308_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7308_tail_safe : formal_typed_suffix_safe flat_memories 7308 rfa_register_7308_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7308_identity : register_identity_b 7308 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7308 invalid old current result old_value word :
 VM.find 7308 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7388 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7308 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7479 flat_statements rfa_register_7308_decl rfa_register_7308_mid rfa_register_7308_tail
 7308 rfa_register_7308_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7388)) (@Eref VarOrder.T (@Eid VarOrder.T 1796)) invalid flat_memories old current result old_value 32
 rfa_register_7308_position rfa_register_7308_split rfa_register_7308_straight rfa_register_7308_mid_safe rfa_register_7308_tail_safe Old Typed rfa_register_7308_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7388)) (@Eref VarOrder.T (@Eid VarOrder.T 1796))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7388 1796 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_861 invalid old current result old_value word :
 VM.find 861 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1095 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 861 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 870 flat_statements joint_register_861_decl joint_register_861_mid joint_register_861_tail
 861 joint_register_861_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1095)) (@Eref VarOrder.T (@Eid VarOrder.T 1031)) invalid flat_memories old current result old_value 32
 joint_register_861_position joint_register_861_split joint_register_861_straight joint_register_861_mid_safe joint_register_861_tail_safe Old Typed joint_register_861_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1095)) (@Eref VarOrder.T (@Eid VarOrder.T 1031))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1095 1031 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7309_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7309)))).
Definition rfa_register_7309_decl := match straight_drop 7481 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7309_tail := match straight_drop 7900 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7309_mid := take_statements 418 rfa_register_7309_decl.
Lemma rfa_register_7309_position : straight_drop 7480 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7309 rfa_register_7309_reg) rfa_register_7309_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7309_split : rfa_register_7309_decl = statement_append rfa_register_7309_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7309) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7390)) (@Eref VarOrder.T (@Eid VarOrder.T 1797)))) rfa_register_7309_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7309_straight : straight_statements rfa_register_7309_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7309_mid_safe : formal_typed_suffix_safe flat_memories 7309 rfa_register_7309_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7309_tail_safe : formal_typed_suffix_safe flat_memories 7309 rfa_register_7309_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7309_identity : register_identity_b 7309 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7309 invalid old current result old_value word :
 VM.find 7309 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7390 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7309 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7480 flat_statements rfa_register_7309_decl rfa_register_7309_mid rfa_register_7309_tail
 7309 rfa_register_7309_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7390)) (@Eref VarOrder.T (@Eid VarOrder.T 1797)) invalid flat_memories old current result old_value 32
 rfa_register_7309_position rfa_register_7309_split rfa_register_7309_straight rfa_register_7309_mid_safe rfa_register_7309_tail_safe Old Typed rfa_register_7309_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7390)) (@Eref VarOrder.T (@Eid VarOrder.T 1797))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7390 1797 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_862 invalid old current result old_value word :
 VM.find 862 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1096 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 862 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 871 flat_statements joint_register_862_decl joint_register_862_mid joint_register_862_tail
 862 joint_register_862_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1096)) (@Eref VarOrder.T (@Eid VarOrder.T 1032)) invalid flat_memories old current result old_value 32
 joint_register_862_position joint_register_862_split joint_register_862_straight joint_register_862_mid_safe joint_register_862_tail_safe Old Typed joint_register_862_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1096)) (@Eref VarOrder.T (@Eid VarOrder.T 1032))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1096 1032 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7310_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7310)))).
Definition rfa_register_7310_decl := match straight_drop 7482 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7310_tail := match straight_drop 7901 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7310_mid := take_statements 418 rfa_register_7310_decl.
Lemma rfa_register_7310_position : straight_drop 7481 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7310 rfa_register_7310_reg) rfa_register_7310_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7310_split : rfa_register_7310_decl = statement_append rfa_register_7310_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7310) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7392)) (@Eref VarOrder.T (@Eid VarOrder.T 1798)))) rfa_register_7310_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7310_straight : straight_statements rfa_register_7310_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7310_mid_safe : formal_typed_suffix_safe flat_memories 7310 rfa_register_7310_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7310_tail_safe : formal_typed_suffix_safe flat_memories 7310 rfa_register_7310_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7310_identity : register_identity_b 7310 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7310 invalid old current result old_value word :
 VM.find 7310 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7392 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7310 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7481 flat_statements rfa_register_7310_decl rfa_register_7310_mid rfa_register_7310_tail
 7310 rfa_register_7310_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7392)) (@Eref VarOrder.T (@Eid VarOrder.T 1798)) invalid flat_memories old current result old_value 32
 rfa_register_7310_position rfa_register_7310_split rfa_register_7310_straight rfa_register_7310_mid_safe rfa_register_7310_tail_safe Old Typed rfa_register_7310_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7392)) (@Eref VarOrder.T (@Eid VarOrder.T 1798))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7392 1798 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
