Require Import FormalInstructionPortConnection FormalNodeEquation FormalNodeSuffixFrames FormalRegisterCommitIdentity StagedRegisterHold RegisterCommitCertificate CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalStatementSegments MemoryWriteFrames FormalInstructionPortSegments InstructionPortConnection InstructionPortShape InstructionPortSource.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem instruction_port_iteration invalid old phase current result address enable clock mask data :
 VM.find 9176 old = Some (instruction_port_bundle address enable clock mask data) ->
 type_of_val address = Gtyp (Fuint 16) -> type_of_val enable = Gtyp (Fuint 1) ->
 type_of_val clock = Gtyp Fclock -> type_of_val data = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old phase current flat_statements = Some result ->
 exists new_address new_clock,
 type_of_val new_address = Gtyp (Fuint 16) /\ type_of_val new_clock = Gtyp Fclock /\
 VM.find 9176 result = Some (instruction_port_bundle new_address (Gval (Fuint 1) [::true]) new_clock mask data).
Proof.
 intros Old AddressType EnableType ClockType DataType Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old phase current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 assert (Projection : VM.find 9176 result = VM.find 9176 proposed).
 { destruct phase.
   - apply (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result 9176); [vm_compute; reflexivity|exact Step].
   - rewrite (staged_finish_false_equal flat_statements invalid nil 0 flat_memories old proposed (fun e => eval_hfexpr_with_memory flat_memories e old old)) in Step.
     exact (finish_registers_preserves_nonregister flat_statements _ old false proposed result 9176 instruction_port_nonregister Step). }
 destruct (formal_straight_prefix 10007 flat_statements _ invalid [::] 0 flat_memories old phase current proposed
 instruction_port_decl_position Statements) as [at_decl Decl].
 cbn [instruction_port_decl_stmt formal_statements] in Decl.
 rewrite Old instruction_port_before_address_split in Decl.
 destruct (successful_straight_segment instruction_port_before_address _ invalid [::] _ flat_memories old phase _ proposed
 instruction_port_before_address_straight Decl) as [at_address [Middle Address]].
 assert (AtAddress : VM.find 9176 at_address = Some (instruction_port_bundle address enable clock mask data)).
 { eapply formal_suffix_preserves_value; [exact instruction_port_before_address_safe| |exact Middle].
   apply RegisterMapFacts.find_add_eq. exact (eqxx 9176). }
 cbn [instruction_port_address_stmt formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Address.
 assert (NoAddressWriter : is_memory_data_port true flat_memories 9176 0 0 = false) by reflexivity.
 try rewrite NoAddressWriter in Address.
 assert (NoClockWriter : is_memory_data_port true flat_memories 9176 0 2 = false) by reflexivity.
 try rewrite NoClockWriter in Address.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 0)
 (@Eid VarOrder.T 9219) old at_address) as [after_address|] eqn:AddressConnect; [|discriminate Address].
 destruct (instruction_address_connection_typed flat_memories old at_address after_address address enable clock mask data AtAddress AddressType AddressConnect)
 as [new_address [NewAddressType AfterAddress]].
 rewrite instruction_port_address_next in Address.
 cbn [instruction_port_enable_stmt formal_statements] in Address.
 match type of Address with
 | context [formal_connect ?inv ?site ?mm ?ph ?lhs ?rhs ?old ?cur] =>
 destruct (formal_connect inv site mm ph lhs rhs old cur) as [after_enable|] eqn:EnableConnect
 end; [|discriminate Address].
 assert (AfterEnable : VM.find 9176 after_enable = Some (instruction_port_bundle new_address (Gval (Fuint 1) [::true]) clock mask data)).
 { eapply formal_instruction_enable_connection; [exact AfterAddress|exact EnableType|exact EnableConnect]. }
 rewrite instruction_port_enable_next in Address.
 cbn [instruction_port_clock_stmt formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Address.
 rewrite NoClockWriter in Address.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 2)
 (@Eid VarOrder.T 0) old after_enable) as [after_clock|] eqn:ClockConnect; [|discriminate Address].
 destruct (instruction_clock_connection_typed flat_memories old after_enable after_clock new_address (Gval (Fuint 1) [::true]) clock mask data AfterEnable ClockType ClockConnect)
 as [new_clock [NewClockType AfterClock]].
 rewrite instruction_port_before_read_split in Address.
 destruct (successful_straight_segment instruction_port_before_read _ invalid [::] _ flat_memories old phase after_clock proposed
 instruction_port_before_read_straight Address) as [at_read [ReadMiddle Read]].
 assert (AtRead : VM.find 9176 at_read = Some (instruction_port_bundle new_address (Gval (Fuint 1) [::true]) new_clock mask data)).
 { eapply formal_suffix_preserves_value; [exact instruction_port_before_read_safe|exact AfterClock|exact ReadMiddle]. }
 cbn [instruction_port_read_stmt formal_statements is_memory_writer_ref] in Read.
 destruct (bidirectional_connect_with_memory flat_memories (@Eid VarOrder.T 9220)
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 4)
 old at_read) as [after_read|] eqn:ReadConnect; [|discriminate Read].
 pose proof (instruction_data_source_preserved flat_memories (@Eid VarOrder.T 9220) old at_read after_read new_address (Gval (Fuint 1) [::true]) new_clock mask data (Logic.eq_refl _) AtRead DataType ReadConnect) as AfterRead.
 exists new_address, new_clock. split; [exact NewAddressType|]. split; [exact NewClockType|].
 rewrite Projection. eapply formal_suffix_preserves_value; [exact instruction_port_read_suffix_safe|exact AfterRead|exact Read].
Qed.
Print Assumptions instruction_port_iteration.
