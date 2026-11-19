Require Import RFSelectedLowMux RFReferenceNopExit RFReferenceWriteEffect RFReferenceNopHistory RFReferenceNopIngress RFEffectState FormalDeclaredWireCheck CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_bank_inactive_exit index invalid s0 s1 s2 s3 word :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->size word=32%nat ->
 VM.find 1707 s0=Some(Gval(Fuint 1)[::false]) ->
 VM.find(N.of_nat(2177-index)%nat)s0=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 VM.find(rf_exit_port index)s3=Some(Gval(Fuint 32)word).
Proof.
 intros Lower Upper Size Active Prior S1 S2 S3.
 assert(PLow:rf_reference_low_word word(Gval(Fuint 32)word)).
 { exists 32%nat,word. repeat split;try reflexivity;try exact Size. rewrite<-Size;apply take_size. }
 destruct(rf_selected_low_mux rf_exit_offsets rf_exit_nodes(rf_exit_node 3615 index)(@Eref VarOrder.T(@Eid VarOrder.T 1707))(rf_exit_node 3614 index)(N.of_nat(2177-index)%nat)invalid s0 s1 false _ word
 rf_exit_positions rf_exit_safety(proj1(rf_exit_members index Lower Upper))(fun site=>Active)Prior PLow S1)as[value[Out Low]].
 assert(Alias:VM.find(rf_exit_node 3616 index)s2=Some value).
 { eapply rf_exit_alias_step;[exact Lower|exact Upper|exact Out| |exact S2].
   destruct Low as[width[raw[Value Rest]]]. exists width,raw;exact Value. }
 eapply(declared_wire_checked_value flat_memories flat_statements(rf_exit_decl_position index)
 (Nat.sub(rf_exit_connect_position index)(S(rf_exit_decl_position index)))(rf_exit_port index)(rf_exit_node 3616 index)32);
 [exact(rf_exit_wire_certificates index Lower Upper)|exact Alias|exact(rf_reference_low_adapt32 _ _ Low)|exact S3].
Qed.
Theorem reference_bank_inactive_commit invalid history bank result :
 rf_reference_bank_at(history 0%nat)bank ->bank 0%nat=nseq 32 false ->
 (forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::false])) ->
 (forall t,(t<9259)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 1515(history 9259%nat)=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories(history 9259%nat)true(history 9259%nat)flat_statements=Some result ->
 rf_reference_bank_at result bank.
Proof.
 intros Bank Zero Active Steps Reset Commit.
 apply(rf_reference_no_write_commit invalid(history 9259%nat)(history 9259%nat)result bank
 (rf_reference_bank_history_hold invalid history 9259 bank Bank Steps 9259 ltac:(lia))Reset);[|exact Commit].
 intros index Bound. destruct index as[|index].
 - rewrite Zero. exact(rf_reference_x0_source_history invalid history 9259 200 bank false Bank Zero ltac:(lia)Active Steps 9259 ltac:(vm_compute;lia)ltac:(lia)).
 - pose proof(rf_reference_bank_history_hold invalid history 9259 bank Bank Steps 9254 ltac:(vm_compute;lia)(S index)Bound)as[Size Old].
   pose proof(rf_reference_old_word_ingress(S index)invalid(history 9254%nat)(history 9255%nat)(history 9256%nat)(bank(S index))Bound Size Old(Steps 9254 ltac:(vm_compute;lia))(Steps 9255 ltac:(vm_compute;lia)))as Prior.
   exact(reference_bank_inactive_exit(S index)invalid(history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)(bank(S index))ltac:(lia)Bound Size(Active 9256 ltac:(vm_compute;lia)ltac:(vm_compute;lia))Prior(Steps 9256 ltac:(vm_compute;lia))(Steps 9257 ltac:(vm_compute;lia))(Steps 9258 ltac:(vm_compute;lia))).
Qed.
