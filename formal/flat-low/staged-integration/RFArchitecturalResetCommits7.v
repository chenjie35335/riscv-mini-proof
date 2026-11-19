Require Import JointRegisterCommits2 JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6 CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rfa_reset_commit_879 invalid old current result old_value word :
 VM.find 879 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1113 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 879 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 888 flat_statements joint_register_879_decl joint_register_879_mid joint_register_879_tail
 879 joint_register_879_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1113)) (@Eref VarOrder.T (@Eid VarOrder.T 1049)) invalid flat_memories old current result old_value 32
 joint_register_879_position joint_register_879_split joint_register_879_straight joint_register_879_mid_safe joint_register_879_tail_safe Old Typed joint_register_879_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1113)) (@Eref VarOrder.T (@Eid VarOrder.T 1049))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1113 1049 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7327_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7327)))).
Definition rfa_register_7327_decl := match straight_drop 7499 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7327_tail := match straight_drop 7918 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7327_mid := take_statements 418 rfa_register_7327_decl.
Lemma rfa_register_7327_position : straight_drop 7498 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7327 rfa_register_7327_reg) rfa_register_7327_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7327_split : rfa_register_7327_decl = statement_append rfa_register_7327_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7327) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7426)) (@Eref VarOrder.T (@Eid VarOrder.T 1815)))) rfa_register_7327_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7327_straight : straight_statements rfa_register_7327_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7327_mid_safe : formal_typed_suffix_safe flat_memories 7327 rfa_register_7327_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7327_tail_safe : formal_typed_suffix_safe flat_memories 7327 rfa_register_7327_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7327_identity : register_identity_b 7327 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7327 invalid old current result old_value word :
 VM.find 7327 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7426 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7327 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7498 flat_statements rfa_register_7327_decl rfa_register_7327_mid rfa_register_7327_tail
 7327 rfa_register_7327_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7426)) (@Eref VarOrder.T (@Eid VarOrder.T 1815)) invalid flat_memories old current result old_value 32
 rfa_register_7327_position rfa_register_7327_split rfa_register_7327_straight rfa_register_7327_mid_safe rfa_register_7327_tail_safe Old Typed rfa_register_7327_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7426)) (@Eref VarOrder.T (@Eid VarOrder.T 1815))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7426 1815 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_880 invalid old current result old_value word :
 VM.find 880 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1114 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 880 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 889 flat_statements joint_register_880_decl joint_register_880_mid joint_register_880_tail
 880 joint_register_880_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1114)) (@Eref VarOrder.T (@Eid VarOrder.T 1050)) invalid flat_memories old current result old_value 32
 joint_register_880_position joint_register_880_split joint_register_880_straight joint_register_880_mid_safe joint_register_880_tail_safe Old Typed joint_register_880_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1114)) (@Eref VarOrder.T (@Eid VarOrder.T 1050))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1114 1050 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7328_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7328)))).
Definition rfa_register_7328_decl := match straight_drop 7500 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7328_tail := match straight_drop 7919 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7328_mid := take_statements 418 rfa_register_7328_decl.
Lemma rfa_register_7328_position : straight_drop 7499 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7328 rfa_register_7328_reg) rfa_register_7328_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7328_split : rfa_register_7328_decl = statement_append rfa_register_7328_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7328) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7428)) (@Eref VarOrder.T (@Eid VarOrder.T 1816)))) rfa_register_7328_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7328_straight : straight_statements rfa_register_7328_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7328_mid_safe : formal_typed_suffix_safe flat_memories 7328 rfa_register_7328_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7328_tail_safe : formal_typed_suffix_safe flat_memories 7328 rfa_register_7328_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7328_identity : register_identity_b 7328 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7328 invalid old current result old_value word :
 VM.find 7328 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7428 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7328 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7499 flat_statements rfa_register_7328_decl rfa_register_7328_mid rfa_register_7328_tail
 7328 rfa_register_7328_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7428)) (@Eref VarOrder.T (@Eid VarOrder.T 1816)) invalid flat_memories old current result old_value 32
 rfa_register_7328_position rfa_register_7328_split rfa_register_7328_straight rfa_register_7328_mid_safe rfa_register_7328_tail_safe Old Typed rfa_register_7328_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7428)) (@Eref VarOrder.T (@Eid VarOrder.T 1816))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7428 1816 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_881 invalid old current result old_value word :
 VM.find 881 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1115 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 881 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 890 flat_statements joint_register_881_decl joint_register_881_mid joint_register_881_tail
 881 joint_register_881_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1115)) (@Eref VarOrder.T (@Eid VarOrder.T 1051)) invalid flat_memories old current result old_value 32
 joint_register_881_position joint_register_881_split joint_register_881_straight joint_register_881_mid_safe joint_register_881_tail_safe Old Typed joint_register_881_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1115)) (@Eref VarOrder.T (@Eid VarOrder.T 1051))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1115 1051 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7329_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7329)))).
Definition rfa_register_7329_decl := match straight_drop 7501 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7329_tail := match straight_drop 7920 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7329_mid := take_statements 418 rfa_register_7329_decl.
Lemma rfa_register_7329_position : straight_drop 7500 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7329 rfa_register_7329_reg) rfa_register_7329_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7329_split : rfa_register_7329_decl = statement_append rfa_register_7329_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7329) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7430)) (@Eref VarOrder.T (@Eid VarOrder.T 1817)))) rfa_register_7329_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7329_straight : straight_statements rfa_register_7329_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7329_mid_safe : formal_typed_suffix_safe flat_memories 7329 rfa_register_7329_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7329_tail_safe : formal_typed_suffix_safe flat_memories 7329 rfa_register_7329_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7329_identity : register_identity_b 7329 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7329 invalid old current result old_value word :
 VM.find 7329 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7430 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7329 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7500 flat_statements rfa_register_7329_decl rfa_register_7329_mid rfa_register_7329_tail
 7329 rfa_register_7329_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7430)) (@Eref VarOrder.T (@Eid VarOrder.T 1817)) invalid flat_memories old current result old_value 32
 rfa_register_7329_position rfa_register_7329_split rfa_register_7329_straight rfa_register_7329_mid_safe rfa_register_7329_tail_safe Old Typed rfa_register_7329_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7430)) (@Eref VarOrder.T (@Eid VarOrder.T 1817))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7430 1817 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_882 invalid old current result old_value word :
 VM.find 882 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1116 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 882 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 891 flat_statements joint_register_882_decl joint_register_882_mid joint_register_882_tail
 882 joint_register_882_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1116)) (@Eref VarOrder.T (@Eid VarOrder.T 1052)) invalid flat_memories old current result old_value 32
 joint_register_882_position joint_register_882_split joint_register_882_straight joint_register_882_mid_safe joint_register_882_tail_safe Old Typed joint_register_882_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1116)) (@Eref VarOrder.T (@Eid VarOrder.T 1052))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1116 1052 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7330_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7330)))).
Definition rfa_register_7330_decl := match straight_drop 7502 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7330_tail := match straight_drop 7921 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7330_mid := take_statements 418 rfa_register_7330_decl.
Lemma rfa_register_7330_position : straight_drop 7501 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7330 rfa_register_7330_reg) rfa_register_7330_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7330_split : rfa_register_7330_decl = statement_append rfa_register_7330_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7330) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7432)) (@Eref VarOrder.T (@Eid VarOrder.T 1818)))) rfa_register_7330_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7330_straight : straight_statements rfa_register_7330_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7330_mid_safe : formal_typed_suffix_safe flat_memories 7330 rfa_register_7330_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7330_tail_safe : formal_typed_suffix_safe flat_memories 7330 rfa_register_7330_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7330_identity : register_identity_b 7330 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7330 invalid old current result old_value word :
 VM.find 7330 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7432 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7330 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7501 flat_statements rfa_register_7330_decl rfa_register_7330_mid rfa_register_7330_tail
 7330 rfa_register_7330_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7432)) (@Eref VarOrder.T (@Eid VarOrder.T 1818)) invalid flat_memories old current result old_value 32
 rfa_register_7330_position rfa_register_7330_split rfa_register_7330_straight rfa_register_7330_mid_safe rfa_register_7330_tail_safe Old Typed rfa_register_7330_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7432)) (@Eref VarOrder.T (@Eid VarOrder.T 1818))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7432 1818 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
