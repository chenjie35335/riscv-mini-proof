Require Import RegisterInvariants ScalarNodeFrames DataReaderEnableConnections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem data_reader_source_preserved mm lhs old current result p2 p3 p4 p5 p0 address enable clock mask data :
 9178 != HiF.base_ref lhs ->
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) p0) ->
 type_of_val data = Gtyp (Fuint 32) ->
 bidirectional_connect_with_memory mm lhs
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 4)
 old current = Some result ->
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) p0).
Proof.
 move/negP => Different. intros Current Typed Step.
 unfold bidirectional_connect_with_memory in Step.
 destruct (VM.find (HiF.base_ref lhs) current); [|discriminate Step].
 destruct (eval_type_of_ref lhs current); [|discriminate Step].
 destruct (eval_href_with_memory mm _ old old); [|discriminate Step].
 destruct (adapt_hvalue_as_type _ _); [|discriminate Step].
 destruct (repl_val_part lhs _ _ _ _) as [left_value|]; [|discriminate Step].
 cbn [option_map eval_type_of_ref HiF.base_ref] in Step.
 rewrite (RegisterMapFacts.find_add_neq Different) Current in Step.
 cbn [data_ports data_port_fields option_map type_of_val type_of_bundle_val] in Step.
 rewrite Typed in Step.
 destruct (eval_href_with_memory mm lhs old old) as [source|]; [|discriminate Step].
 cbn in Step.
 destruct (adapt_hvalue_as_type source (Gtyp (Fuint 32))) as [written|] eqn:Adapt; [|discriminate Step].
 pose proof (adapted_uint_is_passive source 32 written Adapt) as Passive.
 cbn [data_ports data_port_fields repl_val_part convert_to_bundle_value option_map] in Step.
 rewrite (passive_source_unchanged data written Passive) in Step.
 cbn in Step. inversion Step; subst result.
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9178)). reflexivity.
Qed.
Print Assumptions data_reader_source_preserved.
