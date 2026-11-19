Require Import RegisterInvariants ScalarNodeFrames ScalarSinkTypes ScalarSinkObservation
 FormalTypedNodeFrames.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem connection_tail_value invalid scope position mm old set_regs current result tail
 (node source : VarOrder.T) width previous source_value value :
 node != source ->
 formal_typed_suffix_safe mm node tail ->
 VM.find node current = Some previous -> type_of_val previous = Gtyp (Fuint width) ->
 VM.find source old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint width)) = Some value ->
 formal_statements invalid scope position mm old set_regs current
  (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T node)
    (@Eref VarOrder.T (@Eid VarOrder.T source))) tail) = Some result ->
 VM.find node result = Some value.
Proof.
 intros Different Safe Current Typed Source Adapt Step.
 cbn [formal_statements is_memory_writer_ref] in Step.
 destruct (bidirectional_connect_with_memory mm (@Eid VarOrder.T node) (@Eid VarOrder.T source) old current)
  as [next|] eqn:Connect; [|discriminate Step].
 destruct (bidirectional_uint_sink_observation mm node (@Eid VarOrder.T source)
  old current next previous width Different Current Typed Connect) as [read [written [Read [Written Next]]]].
 cbn [eval_href_with_memory] in Read. rewrite Source in Read. inversion Read; subst read.
 rewrite Adapt in Written. inversion Written; subst written.
 eapply formal_typed_suffix_preserves_value;
 [exact Safe|eapply adapted_uint_result_type; exact Adapt|exact Next|exact Step].
Qed.
Print Assumptions connection_tail_value.
