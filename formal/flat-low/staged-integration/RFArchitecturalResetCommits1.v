Require Import JointRegisterCommits2 JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6 CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rfa_reset_commit_855 invalid old current result old_value word :
 VM.find 855 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1089 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 855 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 864 flat_statements joint_register_855_decl joint_register_855_mid joint_register_855_tail
 855 joint_register_855_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1089)) (@Eref VarOrder.T (@Eid VarOrder.T 1025)) invalid flat_memories old current result old_value 32
 joint_register_855_position joint_register_855_split joint_register_855_straight joint_register_855_mid_safe joint_register_855_tail_safe Old Typed joint_register_855_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1089)) (@Eref VarOrder.T (@Eid VarOrder.T 1025))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1089 1025 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7303_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7303)))).
Definition rfa_register_7303_decl := match straight_drop 7475 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7303_tail := match straight_drop 7894 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7303_mid := take_statements 418 rfa_register_7303_decl.
Lemma rfa_register_7303_position : straight_drop 7474 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7303 rfa_register_7303_reg) rfa_register_7303_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7303_split : rfa_register_7303_decl = statement_append rfa_register_7303_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7303) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7378)) (@Eref VarOrder.T (@Eid VarOrder.T 1791)))) rfa_register_7303_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7303_straight : straight_statements rfa_register_7303_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7303_mid_safe : formal_typed_suffix_safe flat_memories 7303 rfa_register_7303_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7303_tail_safe : formal_typed_suffix_safe flat_memories 7303 rfa_register_7303_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7303_identity : register_identity_b 7303 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7303 invalid old current result old_value word :
 VM.find 7303 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7378 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7303 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7474 flat_statements rfa_register_7303_decl rfa_register_7303_mid rfa_register_7303_tail
 7303 rfa_register_7303_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7378)) (@Eref VarOrder.T (@Eid VarOrder.T 1791)) invalid flat_memories old current result old_value 32
 rfa_register_7303_position rfa_register_7303_split rfa_register_7303_straight rfa_register_7303_mid_safe rfa_register_7303_tail_safe Old Typed rfa_register_7303_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7378)) (@Eref VarOrder.T (@Eid VarOrder.T 1791))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7378 1791 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_856 invalid old current result old_value word :
 VM.find 856 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1090 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 856 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 865 flat_statements joint_register_856_decl joint_register_856_mid joint_register_856_tail
 856 joint_register_856_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1090)) (@Eref VarOrder.T (@Eid VarOrder.T 1026)) invalid flat_memories old current result old_value 32
 joint_register_856_position joint_register_856_split joint_register_856_straight joint_register_856_mid_safe joint_register_856_tail_safe Old Typed joint_register_856_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1090)) (@Eref VarOrder.T (@Eid VarOrder.T 1026))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1090 1026 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7304_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7304)))).
Definition rfa_register_7304_decl := match straight_drop 7476 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7304_tail := match straight_drop 7895 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7304_mid := take_statements 418 rfa_register_7304_decl.
Lemma rfa_register_7304_position : straight_drop 7475 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7304 rfa_register_7304_reg) rfa_register_7304_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7304_split : rfa_register_7304_decl = statement_append rfa_register_7304_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7304) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7380)) (@Eref VarOrder.T (@Eid VarOrder.T 1792)))) rfa_register_7304_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7304_straight : straight_statements rfa_register_7304_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7304_mid_safe : formal_typed_suffix_safe flat_memories 7304 rfa_register_7304_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7304_tail_safe : formal_typed_suffix_safe flat_memories 7304 rfa_register_7304_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7304_identity : register_identity_b 7304 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7304 invalid old current result old_value word :
 VM.find 7304 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7380 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7304 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7475 flat_statements rfa_register_7304_decl rfa_register_7304_mid rfa_register_7304_tail
 7304 rfa_register_7304_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7380)) (@Eref VarOrder.T (@Eid VarOrder.T 1792)) invalid flat_memories old current result old_value 32
 rfa_register_7304_position rfa_register_7304_split rfa_register_7304_straight rfa_register_7304_mid_safe rfa_register_7304_tail_safe Old Typed rfa_register_7304_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7380)) (@Eref VarOrder.T (@Eid VarOrder.T 1792))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7380 1792 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_857 invalid old current result old_value word :
 VM.find 857 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1091 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 857 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 866 flat_statements joint_register_857_decl joint_register_857_mid joint_register_857_tail
 857 joint_register_857_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1091)) (@Eref VarOrder.T (@Eid VarOrder.T 1027)) invalid flat_memories old current result old_value 32
 joint_register_857_position joint_register_857_split joint_register_857_straight joint_register_857_mid_safe joint_register_857_tail_safe Old Typed joint_register_857_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1091)) (@Eref VarOrder.T (@Eid VarOrder.T 1027))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1091 1027 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7305_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7305)))).
Definition rfa_register_7305_decl := match straight_drop 7477 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7305_tail := match straight_drop 7896 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7305_mid := take_statements 418 rfa_register_7305_decl.
Lemma rfa_register_7305_position : straight_drop 7476 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7305 rfa_register_7305_reg) rfa_register_7305_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7305_split : rfa_register_7305_decl = statement_append rfa_register_7305_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7305) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7382)) (@Eref VarOrder.T (@Eid VarOrder.T 1793)))) rfa_register_7305_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7305_straight : straight_statements rfa_register_7305_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7305_mid_safe : formal_typed_suffix_safe flat_memories 7305 rfa_register_7305_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7305_tail_safe : formal_typed_suffix_safe flat_memories 7305 rfa_register_7305_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7305_identity : register_identity_b 7305 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7305 invalid old current result old_value word :
 VM.find 7305 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7382 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7305 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7476 flat_statements rfa_register_7305_decl rfa_register_7305_mid rfa_register_7305_tail
 7305 rfa_register_7305_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7382)) (@Eref VarOrder.T (@Eid VarOrder.T 1793)) invalid flat_memories old current result old_value 32
 rfa_register_7305_position rfa_register_7305_split rfa_register_7305_straight rfa_register_7305_mid_safe rfa_register_7305_tail_safe Old Typed rfa_register_7305_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7382)) (@Eref VarOrder.T (@Eid VarOrder.T 1793))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7382 1793 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_858 invalid old current result old_value word :
 VM.find 858 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1092 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 858 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 867 flat_statements joint_register_858_decl joint_register_858_mid joint_register_858_tail
 858 joint_register_858_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1092)) (@Eref VarOrder.T (@Eid VarOrder.T 1028)) invalid flat_memories old current result old_value 32
 joint_register_858_position joint_register_858_split joint_register_858_straight joint_register_858_mid_safe joint_register_858_tail_safe Old Typed joint_register_858_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1092)) (@Eref VarOrder.T (@Eid VarOrder.T 1028))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1092 1028 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7306_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7306)))).
Definition rfa_register_7306_decl := match straight_drop 7478 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7306_tail := match straight_drop 7897 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7306_mid := take_statements 418 rfa_register_7306_decl.
Lemma rfa_register_7306_position : straight_drop 7477 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7306 rfa_register_7306_reg) rfa_register_7306_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7306_split : rfa_register_7306_decl = statement_append rfa_register_7306_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7306) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7384)) (@Eref VarOrder.T (@Eid VarOrder.T 1794)))) rfa_register_7306_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7306_straight : straight_statements rfa_register_7306_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7306_mid_safe : formal_typed_suffix_safe flat_memories 7306 rfa_register_7306_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7306_tail_safe : formal_typed_suffix_safe flat_memories 7306 rfa_register_7306_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7306_identity : register_identity_b 7306 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7306 invalid old current result old_value word :
 VM.find 7306 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7384 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7306 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7477 flat_statements rfa_register_7306_decl rfa_register_7306_mid rfa_register_7306_tail
 7306 rfa_register_7306_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7384)) (@Eref VarOrder.T (@Eid VarOrder.T 1794)) invalid flat_memories old current result old_value 32
 rfa_register_7306_position rfa_register_7306_split rfa_register_7306_straight rfa_register_7306_mid_safe rfa_register_7306_tail_safe Old Typed rfa_register_7306_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7384)) (@Eref VarOrder.T (@Eid VarOrder.T 1794))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7384 1794 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
