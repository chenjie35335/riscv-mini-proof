Require Import JointRegisterCommits2 JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6 CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rfa_reset_commit_871 invalid old current result old_value word :
 VM.find 871 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1105 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 871 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 880 flat_statements joint_register_871_decl joint_register_871_mid joint_register_871_tail
 871 joint_register_871_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1105)) (@Eref VarOrder.T (@Eid VarOrder.T 1041)) invalid flat_memories old current result old_value 32
 joint_register_871_position joint_register_871_split joint_register_871_straight joint_register_871_mid_safe joint_register_871_tail_safe Old Typed joint_register_871_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1105)) (@Eref VarOrder.T (@Eid VarOrder.T 1041))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1105 1041 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7319_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7319)))).
Definition rfa_register_7319_decl := match straight_drop 7491 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7319_tail := match straight_drop 7910 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7319_mid := take_statements 418 rfa_register_7319_decl.
Lemma rfa_register_7319_position : straight_drop 7490 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7319 rfa_register_7319_reg) rfa_register_7319_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7319_split : rfa_register_7319_decl = statement_append rfa_register_7319_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7319) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7410)) (@Eref VarOrder.T (@Eid VarOrder.T 1807)))) rfa_register_7319_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7319_straight : straight_statements rfa_register_7319_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7319_mid_safe : formal_typed_suffix_safe flat_memories 7319 rfa_register_7319_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7319_tail_safe : formal_typed_suffix_safe flat_memories 7319 rfa_register_7319_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7319_identity : register_identity_b 7319 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7319 invalid old current result old_value word :
 VM.find 7319 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7410 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7319 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7490 flat_statements rfa_register_7319_decl rfa_register_7319_mid rfa_register_7319_tail
 7319 rfa_register_7319_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7410)) (@Eref VarOrder.T (@Eid VarOrder.T 1807)) invalid flat_memories old current result old_value 32
 rfa_register_7319_position rfa_register_7319_split rfa_register_7319_straight rfa_register_7319_mid_safe rfa_register_7319_tail_safe Old Typed rfa_register_7319_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7410)) (@Eref VarOrder.T (@Eid VarOrder.T 1807))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7410 1807 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_872 invalid old current result old_value word :
 VM.find 872 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1106 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 872 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 881 flat_statements joint_register_872_decl joint_register_872_mid joint_register_872_tail
 872 joint_register_872_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1106)) (@Eref VarOrder.T (@Eid VarOrder.T 1042)) invalid flat_memories old current result old_value 32
 joint_register_872_position joint_register_872_split joint_register_872_straight joint_register_872_mid_safe joint_register_872_tail_safe Old Typed joint_register_872_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1106)) (@Eref VarOrder.T (@Eid VarOrder.T 1042))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1106 1042 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7320_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7320)))).
Definition rfa_register_7320_decl := match straight_drop 7492 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7320_tail := match straight_drop 7911 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7320_mid := take_statements 418 rfa_register_7320_decl.
Lemma rfa_register_7320_position : straight_drop 7491 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7320 rfa_register_7320_reg) rfa_register_7320_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7320_split : rfa_register_7320_decl = statement_append rfa_register_7320_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7320) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7412)) (@Eref VarOrder.T (@Eid VarOrder.T 1808)))) rfa_register_7320_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7320_straight : straight_statements rfa_register_7320_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7320_mid_safe : formal_typed_suffix_safe flat_memories 7320 rfa_register_7320_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7320_tail_safe : formal_typed_suffix_safe flat_memories 7320 rfa_register_7320_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7320_identity : register_identity_b 7320 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7320 invalid old current result old_value word :
 VM.find 7320 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7412 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7320 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7491 flat_statements rfa_register_7320_decl rfa_register_7320_mid rfa_register_7320_tail
 7320 rfa_register_7320_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7412)) (@Eref VarOrder.T (@Eid VarOrder.T 1808)) invalid flat_memories old current result old_value 32
 rfa_register_7320_position rfa_register_7320_split rfa_register_7320_straight rfa_register_7320_mid_safe rfa_register_7320_tail_safe Old Typed rfa_register_7320_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7412)) (@Eref VarOrder.T (@Eid VarOrder.T 1808))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7412 1808 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_873 invalid old current result old_value word :
 VM.find 873 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1107 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 873 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 882 flat_statements joint_register_873_decl joint_register_873_mid joint_register_873_tail
 873 joint_register_873_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1107)) (@Eref VarOrder.T (@Eid VarOrder.T 1043)) invalid flat_memories old current result old_value 32
 joint_register_873_position joint_register_873_split joint_register_873_straight joint_register_873_mid_safe joint_register_873_tail_safe Old Typed joint_register_873_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1107)) (@Eref VarOrder.T (@Eid VarOrder.T 1043))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1107 1043 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7321_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7321)))).
Definition rfa_register_7321_decl := match straight_drop 7493 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7321_tail := match straight_drop 7912 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7321_mid := take_statements 418 rfa_register_7321_decl.
Lemma rfa_register_7321_position : straight_drop 7492 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7321 rfa_register_7321_reg) rfa_register_7321_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7321_split : rfa_register_7321_decl = statement_append rfa_register_7321_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7321) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7414)) (@Eref VarOrder.T (@Eid VarOrder.T 1809)))) rfa_register_7321_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7321_straight : straight_statements rfa_register_7321_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7321_mid_safe : formal_typed_suffix_safe flat_memories 7321 rfa_register_7321_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7321_tail_safe : formal_typed_suffix_safe flat_memories 7321 rfa_register_7321_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7321_identity : register_identity_b 7321 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7321 invalid old current result old_value word :
 VM.find 7321 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7414 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7321 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7492 flat_statements rfa_register_7321_decl rfa_register_7321_mid rfa_register_7321_tail
 7321 rfa_register_7321_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7414)) (@Eref VarOrder.T (@Eid VarOrder.T 1809)) invalid flat_memories old current result old_value 32
 rfa_register_7321_position rfa_register_7321_split rfa_register_7321_straight rfa_register_7321_mid_safe rfa_register_7321_tail_safe Old Typed rfa_register_7321_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7414)) (@Eref VarOrder.T (@Eid VarOrder.T 1809))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7414 1809 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_874 invalid old current result old_value word :
 VM.find 874 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1108 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 874 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 883 flat_statements joint_register_874_decl joint_register_874_mid joint_register_874_tail
 874 joint_register_874_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1108)) (@Eref VarOrder.T (@Eid VarOrder.T 1044)) invalid flat_memories old current result old_value 32
 joint_register_874_position joint_register_874_split joint_register_874_straight joint_register_874_mid_safe joint_register_874_tail_safe Old Typed joint_register_874_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1108)) (@Eref VarOrder.T (@Eid VarOrder.T 1044))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1108 1044 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7322_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7322)))).
Definition rfa_register_7322_decl := match straight_drop 7494 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7322_tail := match straight_drop 7913 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7322_mid := take_statements 418 rfa_register_7322_decl.
Lemma rfa_register_7322_position : straight_drop 7493 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7322 rfa_register_7322_reg) rfa_register_7322_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7322_split : rfa_register_7322_decl = statement_append rfa_register_7322_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7322) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7416)) (@Eref VarOrder.T (@Eid VarOrder.T 1810)))) rfa_register_7322_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7322_straight : straight_statements rfa_register_7322_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7322_mid_safe : formal_typed_suffix_safe flat_memories 7322 rfa_register_7322_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7322_tail_safe : formal_typed_suffix_safe flat_memories 7322 rfa_register_7322_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7322_identity : register_identity_b 7322 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7322 invalid old current result old_value word :
 VM.find 7322 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7416 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7322 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7493 flat_statements rfa_register_7322_decl rfa_register_7322_mid rfa_register_7322_tail
 7322 rfa_register_7322_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7416)) (@Eref VarOrder.T (@Eid VarOrder.T 1810)) invalid flat_memories old current result old_value 32
 rfa_register_7322_position rfa_register_7322_split rfa_register_7322_straight rfa_register_7322_mid_safe rfa_register_7322_tail_safe Old Typed rfa_register_7322_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7416)) (@Eref VarOrder.T (@Eid VarOrder.T 1810))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7416 1810 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
