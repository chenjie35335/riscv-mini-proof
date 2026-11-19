Require Import JointRegisterCommits2 JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6 CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rfa_reset_commit_867 invalid old current result old_value word :
 VM.find 867 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1101 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 867 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 876 flat_statements joint_register_867_decl joint_register_867_mid joint_register_867_tail
 867 joint_register_867_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1101)) (@Eref VarOrder.T (@Eid VarOrder.T 1037)) invalid flat_memories old current result old_value 32
 joint_register_867_position joint_register_867_split joint_register_867_straight joint_register_867_mid_safe joint_register_867_tail_safe Old Typed joint_register_867_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1101)) (@Eref VarOrder.T (@Eid VarOrder.T 1037))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1101 1037 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7315_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7315)))).
Definition rfa_register_7315_decl := match straight_drop 7487 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7315_tail := match straight_drop 7906 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7315_mid := take_statements 418 rfa_register_7315_decl.
Lemma rfa_register_7315_position : straight_drop 7486 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7315 rfa_register_7315_reg) rfa_register_7315_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7315_split : rfa_register_7315_decl = statement_append rfa_register_7315_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7315) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7402)) (@Eref VarOrder.T (@Eid VarOrder.T 1803)))) rfa_register_7315_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7315_straight : straight_statements rfa_register_7315_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7315_mid_safe : formal_typed_suffix_safe flat_memories 7315 rfa_register_7315_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7315_tail_safe : formal_typed_suffix_safe flat_memories 7315 rfa_register_7315_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7315_identity : register_identity_b 7315 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7315 invalid old current result old_value word :
 VM.find 7315 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7402 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7315 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7486 flat_statements rfa_register_7315_decl rfa_register_7315_mid rfa_register_7315_tail
 7315 rfa_register_7315_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7402)) (@Eref VarOrder.T (@Eid VarOrder.T 1803)) invalid flat_memories old current result old_value 32
 rfa_register_7315_position rfa_register_7315_split rfa_register_7315_straight rfa_register_7315_mid_safe rfa_register_7315_tail_safe Old Typed rfa_register_7315_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7402)) (@Eref VarOrder.T (@Eid VarOrder.T 1803))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7402 1803 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_868 invalid old current result old_value word :
 VM.find 868 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1102 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 868 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 877 flat_statements joint_register_868_decl joint_register_868_mid joint_register_868_tail
 868 joint_register_868_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1102)) (@Eref VarOrder.T (@Eid VarOrder.T 1038)) invalid flat_memories old current result old_value 32
 joint_register_868_position joint_register_868_split joint_register_868_straight joint_register_868_mid_safe joint_register_868_tail_safe Old Typed joint_register_868_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1102)) (@Eref VarOrder.T (@Eid VarOrder.T 1038))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1102 1038 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7316_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7316)))).
Definition rfa_register_7316_decl := match straight_drop 7488 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7316_tail := match straight_drop 7907 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7316_mid := take_statements 418 rfa_register_7316_decl.
Lemma rfa_register_7316_position : straight_drop 7487 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7316 rfa_register_7316_reg) rfa_register_7316_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7316_split : rfa_register_7316_decl = statement_append rfa_register_7316_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7316) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7404)) (@Eref VarOrder.T (@Eid VarOrder.T 1804)))) rfa_register_7316_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7316_straight : straight_statements rfa_register_7316_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7316_mid_safe : formal_typed_suffix_safe flat_memories 7316 rfa_register_7316_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7316_tail_safe : formal_typed_suffix_safe flat_memories 7316 rfa_register_7316_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7316_identity : register_identity_b 7316 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7316 invalid old current result old_value word :
 VM.find 7316 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7404 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7316 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7487 flat_statements rfa_register_7316_decl rfa_register_7316_mid rfa_register_7316_tail
 7316 rfa_register_7316_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7404)) (@Eref VarOrder.T (@Eid VarOrder.T 1804)) invalid flat_memories old current result old_value 32
 rfa_register_7316_position rfa_register_7316_split rfa_register_7316_straight rfa_register_7316_mid_safe rfa_register_7316_tail_safe Old Typed rfa_register_7316_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7404)) (@Eref VarOrder.T (@Eid VarOrder.T 1804))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7404 1804 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_869 invalid old current result old_value word :
 VM.find 869 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1103 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 869 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 878 flat_statements joint_register_869_decl joint_register_869_mid joint_register_869_tail
 869 joint_register_869_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1103)) (@Eref VarOrder.T (@Eid VarOrder.T 1039)) invalid flat_memories old current result old_value 32
 joint_register_869_position joint_register_869_split joint_register_869_straight joint_register_869_mid_safe joint_register_869_tail_safe Old Typed joint_register_869_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1103)) (@Eref VarOrder.T (@Eid VarOrder.T 1039))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1103 1039 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7317_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7317)))).
Definition rfa_register_7317_decl := match straight_drop 7489 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7317_tail := match straight_drop 7908 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7317_mid := take_statements 418 rfa_register_7317_decl.
Lemma rfa_register_7317_position : straight_drop 7488 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7317 rfa_register_7317_reg) rfa_register_7317_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7317_split : rfa_register_7317_decl = statement_append rfa_register_7317_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7317) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7406)) (@Eref VarOrder.T (@Eid VarOrder.T 1805)))) rfa_register_7317_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7317_straight : straight_statements rfa_register_7317_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7317_mid_safe : formal_typed_suffix_safe flat_memories 7317 rfa_register_7317_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7317_tail_safe : formal_typed_suffix_safe flat_memories 7317 rfa_register_7317_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7317_identity : register_identity_b 7317 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7317 invalid old current result old_value word :
 VM.find 7317 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7406 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7317 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7488 flat_statements rfa_register_7317_decl rfa_register_7317_mid rfa_register_7317_tail
 7317 rfa_register_7317_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7406)) (@Eref VarOrder.T (@Eid VarOrder.T 1805)) invalid flat_memories old current result old_value 32
 rfa_register_7317_position rfa_register_7317_split rfa_register_7317_straight rfa_register_7317_mid_safe rfa_register_7317_tail_safe Old Typed rfa_register_7317_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7406)) (@Eref VarOrder.T (@Eid VarOrder.T 1805))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7406 1805 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_870 invalid old current result old_value word :
 VM.find 870 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1104 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 870 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 879 flat_statements joint_register_870_decl joint_register_870_mid joint_register_870_tail
 870 joint_register_870_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1104)) (@Eref VarOrder.T (@Eid VarOrder.T 1040)) invalid flat_memories old current result old_value 32
 joint_register_870_position joint_register_870_split joint_register_870_straight joint_register_870_mid_safe joint_register_870_tail_safe Old Typed joint_register_870_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1104)) (@Eref VarOrder.T (@Eid VarOrder.T 1040))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1104 1040 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7318_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7318)))).
Definition rfa_register_7318_decl := match straight_drop 7490 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7318_tail := match straight_drop 7909 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7318_mid := take_statements 418 rfa_register_7318_decl.
Lemma rfa_register_7318_position : straight_drop 7489 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7318 rfa_register_7318_reg) rfa_register_7318_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7318_split : rfa_register_7318_decl = statement_append rfa_register_7318_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7318) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7408)) (@Eref VarOrder.T (@Eid VarOrder.T 1806)))) rfa_register_7318_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7318_straight : straight_statements rfa_register_7318_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7318_mid_safe : formal_typed_suffix_safe flat_memories 7318 rfa_register_7318_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7318_tail_safe : formal_typed_suffix_safe flat_memories 7318 rfa_register_7318_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7318_identity : register_identity_b 7318 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7318 invalid old current result old_value word :
 VM.find 7318 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7408 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7318 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7489 flat_statements rfa_register_7318_decl rfa_register_7318_mid rfa_register_7318_tail
 7318 rfa_register_7318_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7408)) (@Eref VarOrder.T (@Eid VarOrder.T 1806)) invalid flat_memories old current result old_value 32
 rfa_register_7318_position rfa_register_7318_split rfa_register_7318_straight rfa_register_7318_mid_safe rfa_register_7318_tail_safe Old Typed rfa_register_7318_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7408)) (@Eref VarOrder.T (@Eid VarOrder.T 1806))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7408 1806 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
