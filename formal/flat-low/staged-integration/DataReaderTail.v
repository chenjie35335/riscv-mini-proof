Require Import DataReaderSegments DataWriterReaderFrames DataWriterBidirectionalFrames DataReaderSourceFrame DataReaderEnableConnections FormalConnectionFrames ScalarNodeFrames MemoryWriteFrames ComparisonNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_tail_8 := @Qnil VarOrder.T.
Definition data_tail_7 := @Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 9222) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 4))) data_tail_8.
Definition data_tail_6 := @Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 9220) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 4))) data_tail_7.
Definition data_tail_5 := @Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 9180) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 9236)))) data_tail_6.
Definition data_tail_4 := @Qcons VarOrder.T (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 3) (@Eref VarOrder.T (@Eid VarOrder.T 9233))) data_tail_5.
Definition data_tail_3 := @Qcons VarOrder.T (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 4) (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 9234)))) data_tail_4.
Definition data_tail_2 := @Qcons VarOrder.T (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 2) (@Eref VarOrder.T (@Eid VarOrder.T 9231))) data_tail_3.
Definition data_tail_1 := @Qcons VarOrder.T (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 1) (@Eref VarOrder.T (@Eid VarOrder.T 9232))) data_tail_2.
Definition data_tail_0 := @Qcons VarOrder.T (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 0) (@Eref VarOrder.T (@Eid VarOrder.T 9230))) data_tail_1.
Lemma data_tail_exact : data_after_readers = data_tail_0.
Proof. vm_compute. reflexivity. Qed.
Lemma data_tail_register_storage_disjoint : memory_storage_disjoint flat_memories 9178 9180.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_memories.
Theorem data_tail_preserves_readers invalid scope position phase old current result p2 p3 p4 p5 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) p0) ->
 type_of_val data = Gtyp (Fuint 32) ->
 formal_statements invalid scope position flat_memories old phase current data_after_readers = Some result ->
 exists updated, VM.find 9178 result = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) updated).
Proof.
 intros Value Typed Step. rewrite data_tail_exact in Step.
 cbn [data_tail_0 formal_statements is_memory_writer_ref] in Step.
 assert (NoWriter0 : is_memory_data_port true flat_memories 9178 0 0 = false) by reflexivity.
 rewrite NoWriter0 in Step.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 0)
 (@Eid VarOrder.T 9230) old current) as [next0|] eqn:Connect0; [|discriminate Step].
 destruct (data_writer_bidirectional_preserves_readers flat_memories old current next0 0 9230
 p2 p3 p4 p5 (data_port_fields address enable clock mask data) p0 (Logic.eq_refl _) Value Connect0)
 as [writer0 Value0].
 cbn [data_tail_1 formal_statements is_memory_writer_ref] in Step.
 assert (NoWriter1 : is_memory_data_port true flat_memories 9178 0 1 = false) by reflexivity.
 rewrite NoWriter1 in Step.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 1)
 (@Eid VarOrder.T 9232) old next0) as [next1|] eqn:Connect1; [|discriminate Step].
 destruct (data_writer_bidirectional_preserves_readers flat_memories old next0 next1 1 9232
 p2 p3 p4 p5 (data_port_fields address enable clock mask data) writer0 (Logic.eq_refl _) Value0 Connect1)
 as [writer1 Value1].
 cbn [data_tail_2 formal_statements is_memory_writer_ref] in Step.
 assert (NoWriter2 : is_memory_data_port true flat_memories 9178 0 2 = false) by reflexivity.
 rewrite NoWriter2 in Step.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 2)
 (@Eid VarOrder.T 9231) old next1) as [next2|] eqn:Connect2; [|discriminate Step].
 destruct (data_writer_bidirectional_preserves_readers flat_memories old next1 next2 2 9231
 p2 p3 p4 p5 (data_port_fields address enable clock mask data) writer1 (Logic.eq_refl _) Value1 Connect2)
 as [writer2 Value2].
 cbn [data_tail_3 formal_statements is_memory_writer_ref] in Step.
 match type of Step with
 | context [formal_connect ?inv ?site ?mm ?ph ?lhs ?rhs ?o ?c] =>
 destruct (formal_connect inv site mm ph lhs rhs o c) as [next3|] eqn:Connect3
 end; [|discriminate Step].
 destruct (data_writer_connection_preserves_readers invalid _ phase old next2 next3 4 _
 p2 p3 p4 p5 (data_port_fields address enable clock mask data) writer2 Value2 Connect3)
 as [writer3 Value3].
 cbn [data_tail_4 formal_statements is_memory_writer_ref] in Step.
 assert (NoWriter4 : is_memory_data_port true flat_memories 9178 0 3 = false) by reflexivity.
 rewrite NoWriter4 in Step.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 3)
 (@Eid VarOrder.T 9233) old next3) as [next4|] eqn:Connect4; [|discriminate Step].
 destruct (data_writer_bidirectional_preserves_readers flat_memories old next3 next4 3 9233
 p2 p3 p4 p5 (data_port_fields address enable clock mask data) writer3 (Logic.eq_refl _) Value3 Connect4)
 as [writer4 Value4].
 cbn [data_tail_5 formal_statements] in Step.
 match type of Step with
 | context [formal_connect ?inv ?site ?mm ?ph ?lhs ?rhs ?o ?c] =>
 destruct (formal_connect inv site mm ph lhs rhs o c) as [next5|] eqn:Connect5
 end; [|discriminate Step].
 assert (Value5 : VM.find 9178 next5 = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) writer4)).
 { rewrite (formal_connection_preserves_other invalid _ flat_memories phase 9178 (@Eid VarOrder.T 9180) _ old next4 next5 (Logic.eq_refl _) data_tail_register_storage_disjoint Connect5).
   exact Value4. }
 cbn [data_tail_6 formal_statements is_memory_writer_ref] in Step.
 destruct (bidirectional_connect_with_memory flat_memories (@Eid VarOrder.T 9220)
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 4) old next5)
 as [next6|] eqn:Connect6; [|discriminate Step].
 assert (Value6 : VM.find 9178 next6 = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) writer4)).
 { rewrite (bidirectional_connect_with_memory_preserves_other flat_memories 9178 (@Eid VarOrder.T 9220) (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 4) old next5 next6 (Logic.eq_refl _) (Logic.eq_refl _) Connect6). exact Value5. }
 cbn [data_tail_7 formal_statements is_memory_writer_ref] in Step.
 destruct (bidirectional_connect_with_memory flat_memories (@Eid VarOrder.T 9222)
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 4) old next6)
 as [next7|] eqn:Connect7; [|discriminate Step].
 cbn [data_tail_8 formal_statements] in Step. inversion Step; subst result.
 exists writer4.
 exact (data_reader_source_preserved flat_memories (@Eid VarOrder.T 9222) old next6 next7
 p2 p3 p4 p5 writer4 address enable clock mask data (Logic.eq_refl _) Value6 Typed Connect7).
Qed.
Print Assumptions data_tail_preserves_readers.
