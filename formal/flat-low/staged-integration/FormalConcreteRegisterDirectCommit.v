Require Import ConcreteGroundUIntAdapt FormalDeclaredConnection FormalRegisterCommitIdentity RegisterCommitCertificate.
Require Import ConcreteGroundAdapt ConcreteGroundOperations ScalarSinkObservation ScalarSinkTypes.
Require Import RegisterInvariants ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalConnectionTail FormalNodeEquation StagedRegisterHold.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem concrete_register_direct_commit count stmts declared_tail middle tail
 (node source : VarOrder.T) reg width ground bits old_value invalid mm old current result :
 straight_drop count stmts = Some (Qcons (Sreg node reg) declared_tail) ->
 declared_tail = statement_append middle (Qcons (Sfcnct (Eid node) (Eref (Eid source))) tail) ->
 straight_statements middle ->
 formal_typed_suffix_safe mm node middle -> formal_typed_suffix_safe mm node tail ->
 register_identity_b node stmts ->
 VM.find node old = Some old_value -> type_of_val old_value = Gtyp (Fuint width) -> node != source ->
 VM.find source old = Some (Gval ground bits) ->
 formal_value_iter invalid mm old true current stmts = Some result ->
 exists word, size word = width /\ VM.find node result = Some (Gval (Fuint width) word).
Proof.
 intros Position Split Straight MiddleSafe TailSafe Identity Old Typed Different Source Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid [::] 0 mm old true current stmts) as [proposed|] eqn:Statements;
 [|discriminate Step].
 pose proof (formal_finish_identity_preserves stmts invalid nil 0 mm old proposed result node Identity Step) as Projection.
 destruct (formal_straight_prefix count stmts _ invalid nil 0 mm old true current proposed Position Statements)
   as [at_declaration Decl].
 cbn [formal_statements] in Decl. rewrite Old in Decl.
 rewrite Split in Decl.
 destruct (successful_straight_segment middle _ invalid nil (S (0 + count)) mm old true
  (VM.add node old_value at_declaration) proposed Straight Decl)
  as [at_connection [Middle Connection]].
 assert (Before : VM.find node at_connection = Some old_value).
 { eapply formal_typed_suffix_preserves_value;
   [exact MiddleSafe|exact Typed| |exact Middle].
   apply RegisterMapFacts.find_add_eq. exact (eqxx node). }
 cbn [formal_statements is_memory_writer_ref] in Connection.
 destruct (bidirectional_connect_with_memory mm (@Eid VarOrder.T node) (@Eid VarOrder.T source) old at_connection)
 as [next|] eqn:Connect; [|discriminate Connection].
 destruct (bidirectional_uint_sink_observation mm node (@Eid VarOrder.T source)
 old at_connection next old_value width Different Before Typed Connect)
 as [read [written [Read [Written Next]]]].
 cbn [eval_href_with_memory] in Read. rewrite Source in Read. inversion Read; subst read.
 destruct (concrete_ground_uint_adapt ground bits width written Written) as [word [Size Equal]].
 subst written.
 exists word. split; [exact Size|]. rewrite Projection.
 eapply formal_typed_suffix_preserves_value;
 [exact TailSafe|reflexivity|exact Next|exact Connection].
Qed.
Print Assumptions concrete_register_direct_commit.
