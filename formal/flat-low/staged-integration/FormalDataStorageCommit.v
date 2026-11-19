Require Import ConcreteMemoryWriteGate CoreSocModel ComparisonNodes ConcreteMemoryRead DataMemoryConcrete DataMemoryCommitSegments FormalStatementSegments FormalNonwriterStorageFrames FormalConnectionFrames FormalDataStorageHold FormalRegisterCommitIdentity.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma data_commit_writer_exact : is_memory_data_port true flat_memories 9178 0 4 = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_memories flat_statements data_commit_prefix data_commit_tail.
Theorem data_storage_commit_concrete invalid old current result values gate :
 VM.find 9179 current = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 memory_write_gate old 9178 0 (@mk_mem_port VarOrder.T 0 0 1 2 3) = Some gate ->
 (gate = MemoryOff \/ gate = MemoryOn) ->
 (forall site value,
 eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories data_commit_source old old = Some value ->
 gate = MemoryOn -> exists source_width bits address_width address_bits,
 value = Gval (Fuint source_width) bits /\
 read_memory_port_field old 9178 0 0 = Some (Gval (Fuint address_width) address_bits)) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists updated, VM.find 9179 result = Some (Aval (Gtyp (Fuint 32)) updated) /\ concrete_uint_array 32 updated.
Proof.
 intros Storage Concrete Gate Known Active Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 pose proof (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result 9179 data_storage_identity Step) as Finish.
 rewrite data_commit_split in Statements.
 destruct (successful_straight_segment data_commit_prefix _ invalid nil 0 flat_memories old true current proposed data_commit_prefix_straight Statements)
 as [before [Prefix Rest]].
 assert (Before : VM.find 9179 before = Some (Aval (Gtyp (Fuint 32)) values)).
 { eapply formal_nonwriter_suffix_preserves_value; [exact data_commit_prefix_safe|exact Storage|exact Prefix]. }
 cbn [formal_statements data_commit_source] in Rest.
 destruct (formal_connect invalid (validif_raw_address nil (0 + statement_count data_commit_prefix) 0 nil)
 flat_memories true data_commit_sink data_commit_source old before) as [after|] eqn:Connect.
 - unfold formal_connect, data_commit_sink in Connect. rewrite data_commit_writer_exact in Connect. fold data_commit_sink in Connect.
   destruct (formal_connect_bundle invalid (validif_raw_address nil (0 + statement_count data_commit_prefix) 0 nil)
    flat_memories data_commit_sink data_commit_source old before) as [middle|] eqn:Bundle; [|discriminate Connect].
   destruct (eval_hfexpr_validif_policy (isolated_validif_policy invalid)
    (validif_raw_address nil (0 + statement_count data_commit_prefix) 0 nil)
    flat_memories data_commit_source old old) as [value|] eqn:Eval; [|discriminate Connect].
   assert (Middle : VM.find 9179 middle = Some (Aval (Gtyp (Fuint 32)) values)).
   { rewrite (formal_bundle_preserves_other invalid _ flat_memories 9179 data_commit_sink data_commit_source old before middle (Logic.eq_refl _) Bundle). exact Before. }
   destruct (data_memory_write_concrete old middle after value values gate Middle Concrete Gate Known (Active _ _ Eval) Connect)
    as [updated [Updated ConcreteUpdated]].
   exists updated. split; [|exact ConcreteUpdated]. rewrite Finish.
   eapply formal_nonwriter_suffix_preserves_value; [exact data_commit_tail_safe|exact Updated|exact Rest].
 - discriminate Rest.
Qed.
Print Assumptions data_storage_commit_concrete.
Theorem data_storage_commit_from_concrete_ports invalid old current result values
 source_width source_bits enable_width enable_bits mask_width mask_bits address_width address_bits :
 VM.find 9179 current = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 VM.find 9234 old = Some (Gval (Fuint source_width) source_bits) ->
 read_memory_port_field old 9178 0 1 = Some (Gval (Fuint enable_width) enable_bits) ->
 read_memory_port_field old 9178 0 3 = Some (Gval (Fuint mask_width) mask_bits) ->
 read_memory_port_field old 9178 0 0 = Some (Gval (Fuint address_width) address_bits) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 exists updated, VM.find 9179 result = Some (Aval (Gtyp (Fuint 32)) updated) /\ concrete_uint_array 32 updated.
Proof.
 intros Storage Concrete Source Enable Mask Address Step.
 destruct (concrete_memory_gate_known old 9178 0 (@mk_mem_port VarOrder.T 0 0 1 2 3)
 enable_width enable_bits mask_width mask_bits Enable Mask) as [gate [Gate Known]].
 eapply (data_storage_commit_concrete invalid old current result values gate);
 [exact Storage|exact Concrete|exact Gate|exact Known| |exact Step].
 intros site value Eval On.
 unfold data_commit_source in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite Source in Eval. cbn [eval_unop] in Eval.
 destruct (31 < source_width)%nat; [|discriminate Eval].
 inversion Eval; subst value.
 eexists. eexists. exists address_width, address_bits. split; [reflexivity|exact Address].
Qed.
Print Assumptions data_storage_commit_from_concrete_ports.
