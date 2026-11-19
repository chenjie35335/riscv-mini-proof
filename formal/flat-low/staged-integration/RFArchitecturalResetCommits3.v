Require Import JointRegisterCommits2 JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6 CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rfa_reset_commit_863 invalid old current result old_value word :
 VM.find 863 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1097 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 863 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 872 flat_statements joint_register_863_decl joint_register_863_mid joint_register_863_tail
 863 joint_register_863_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1097)) (@Eref VarOrder.T (@Eid VarOrder.T 1033)) invalid flat_memories old current result old_value 32
 joint_register_863_position joint_register_863_split joint_register_863_straight joint_register_863_mid_safe joint_register_863_tail_safe Old Typed joint_register_863_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1097)) (@Eref VarOrder.T (@Eid VarOrder.T 1033))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1097 1033 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7311_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7311)))).
Definition rfa_register_7311_decl := match straight_drop 7483 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7311_tail := match straight_drop 7902 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7311_mid := take_statements 418 rfa_register_7311_decl.
Lemma rfa_register_7311_position : straight_drop 7482 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7311 rfa_register_7311_reg) rfa_register_7311_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7311_split : rfa_register_7311_decl = statement_append rfa_register_7311_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7311) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7394)) (@Eref VarOrder.T (@Eid VarOrder.T 1799)))) rfa_register_7311_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7311_straight : straight_statements rfa_register_7311_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7311_mid_safe : formal_typed_suffix_safe flat_memories 7311 rfa_register_7311_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7311_tail_safe : formal_typed_suffix_safe flat_memories 7311 rfa_register_7311_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7311_identity : register_identity_b 7311 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7311 invalid old current result old_value word :
 VM.find 7311 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7394 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7311 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7482 flat_statements rfa_register_7311_decl rfa_register_7311_mid rfa_register_7311_tail
 7311 rfa_register_7311_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7394)) (@Eref VarOrder.T (@Eid VarOrder.T 1799)) invalid flat_memories old current result old_value 32
 rfa_register_7311_position rfa_register_7311_split rfa_register_7311_straight rfa_register_7311_mid_safe rfa_register_7311_tail_safe Old Typed rfa_register_7311_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7394)) (@Eref VarOrder.T (@Eid VarOrder.T 1799))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7394 1799 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_864 invalid old current result old_value word :
 VM.find 864 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1098 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 864 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 873 flat_statements joint_register_864_decl joint_register_864_mid joint_register_864_tail
 864 joint_register_864_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1098)) (@Eref VarOrder.T (@Eid VarOrder.T 1034)) invalid flat_memories old current result old_value 32
 joint_register_864_position joint_register_864_split joint_register_864_straight joint_register_864_mid_safe joint_register_864_tail_safe Old Typed joint_register_864_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1098)) (@Eref VarOrder.T (@Eid VarOrder.T 1034))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1098 1034 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7312_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7312)))).
Definition rfa_register_7312_decl := match straight_drop 7484 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7312_tail := match straight_drop 7903 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7312_mid := take_statements 418 rfa_register_7312_decl.
Lemma rfa_register_7312_position : straight_drop 7483 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7312 rfa_register_7312_reg) rfa_register_7312_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7312_split : rfa_register_7312_decl = statement_append rfa_register_7312_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7312) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7396)) (@Eref VarOrder.T (@Eid VarOrder.T 1800)))) rfa_register_7312_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7312_straight : straight_statements rfa_register_7312_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7312_mid_safe : formal_typed_suffix_safe flat_memories 7312 rfa_register_7312_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7312_tail_safe : formal_typed_suffix_safe flat_memories 7312 rfa_register_7312_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7312_identity : register_identity_b 7312 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7312 invalid old current result old_value word :
 VM.find 7312 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7396 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7312 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7483 flat_statements rfa_register_7312_decl rfa_register_7312_mid rfa_register_7312_tail
 7312 rfa_register_7312_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7396)) (@Eref VarOrder.T (@Eid VarOrder.T 1800)) invalid flat_memories old current result old_value 32
 rfa_register_7312_position rfa_register_7312_split rfa_register_7312_straight rfa_register_7312_mid_safe rfa_register_7312_tail_safe Old Typed rfa_register_7312_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7396)) (@Eref VarOrder.T (@Eid VarOrder.T 1800))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7396 1800 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_865 invalid old current result old_value word :
 VM.find 865 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1099 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 865 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 874 flat_statements joint_register_865_decl joint_register_865_mid joint_register_865_tail
 865 joint_register_865_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1099)) (@Eref VarOrder.T (@Eid VarOrder.T 1035)) invalid flat_memories old current result old_value 32
 joint_register_865_position joint_register_865_split joint_register_865_straight joint_register_865_mid_safe joint_register_865_tail_safe Old Typed joint_register_865_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1099)) (@Eref VarOrder.T (@Eid VarOrder.T 1035))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1099 1035 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7313_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7313)))).
Definition rfa_register_7313_decl := match straight_drop 7485 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7313_tail := match straight_drop 7904 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7313_mid := take_statements 418 rfa_register_7313_decl.
Lemma rfa_register_7313_position : straight_drop 7484 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7313 rfa_register_7313_reg) rfa_register_7313_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7313_split : rfa_register_7313_decl = statement_append rfa_register_7313_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7313) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7398)) (@Eref VarOrder.T (@Eid VarOrder.T 1801)))) rfa_register_7313_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7313_straight : straight_statements rfa_register_7313_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7313_mid_safe : formal_typed_suffix_safe flat_memories 7313 rfa_register_7313_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7313_tail_safe : formal_typed_suffix_safe flat_memories 7313 rfa_register_7313_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7313_identity : register_identity_b 7313 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7313 invalid old current result old_value word :
 VM.find 7313 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7398 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7313 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7484 flat_statements rfa_register_7313_decl rfa_register_7313_mid rfa_register_7313_tail
 7313 rfa_register_7313_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7398)) (@Eref VarOrder.T (@Eid VarOrder.T 1801)) invalid flat_memories old current result old_value 32
 rfa_register_7313_position rfa_register_7313_split rfa_register_7313_straight rfa_register_7313_mid_safe rfa_register_7313_tail_safe Old Typed rfa_register_7313_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7398)) (@Eref VarOrder.T (@Eid VarOrder.T 1801))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7398 1801 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_866 invalid old current result old_value word :
 VM.find 866 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1100 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 866 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 875 flat_statements joint_register_866_decl joint_register_866_mid joint_register_866_tail
 866 joint_register_866_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1100)) (@Eref VarOrder.T (@Eid VarOrder.T 1036)) invalid flat_memories old current result old_value 32
 joint_register_866_position joint_register_866_split joint_register_866_straight joint_register_866_mid_safe joint_register_866_tail_safe Old Typed joint_register_866_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1100)) (@Eref VarOrder.T (@Eid VarOrder.T 1036))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1100 1036 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7314_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7314)))).
Definition rfa_register_7314_decl := match straight_drop 7486 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7314_tail := match straight_drop 7905 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7314_mid := take_statements 418 rfa_register_7314_decl.
Lemma rfa_register_7314_position : straight_drop 7485 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7314 rfa_register_7314_reg) rfa_register_7314_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7314_split : rfa_register_7314_decl = statement_append rfa_register_7314_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7314) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7400)) (@Eref VarOrder.T (@Eid VarOrder.T 1802)))) rfa_register_7314_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7314_straight : straight_statements rfa_register_7314_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7314_mid_safe : formal_typed_suffix_safe flat_memories 7314 rfa_register_7314_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7314_tail_safe : formal_typed_suffix_safe flat_memories 7314 rfa_register_7314_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7314_identity : register_identity_b 7314 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7314 invalid old current result old_value word :
 VM.find 7314 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7400 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7314 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7485 flat_statements rfa_register_7314_decl rfa_register_7314_mid rfa_register_7314_tail
 7314 rfa_register_7314_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7400)) (@Eref VarOrder.T (@Eid VarOrder.T 1802)) invalid flat_memories old current result old_value 32
 rfa_register_7314_position rfa_register_7314_split rfa_register_7314_straight rfa_register_7314_mid_safe rfa_register_7314_tail_safe Old Typed rfa_register_7314_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7400)) (@Eref VarOrder.T (@Eid VarOrder.T 1802))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7400 1802 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
