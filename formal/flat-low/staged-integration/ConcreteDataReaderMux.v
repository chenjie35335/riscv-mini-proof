Require Import CoreSocModel ComparisonNodes DataMemoryReaders ConcreteMemoryRead ConcreteGroundOperations ConcretePolicyMux.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_reader_expression (port : VarOrder.T) : hfexpr VarOrder.T :=
 @Eref VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) port) 4).
Lemma data_reader_expression_eval invalid site port old :
 List.In port [::1;2;3;4;5] ->
 eval_hfexpr_validif_policy invalid site flat_memories (data_reader_expression port) old old =
 eval_memory_reader_data flat_memories 9178 port old old.
Proof.
 intro Member. cbn [List.In] in Member.
 repeat destruct Member as [Same|Member]; try (subst port; reflexivity).
 contradiction.
Qed.
Theorem data_reader_expression_concrete invalid site port old values address width value :
 List.In port [::1;2;3;4;5] ->
 VM.find 9179 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 read_memory_port_field old 9178 port 1 = Some (Gval (Fuint 1) [::true]) ->
 read_memory_port_field old 9178 port 0 = Some (Gval (Fuint width) address) ->
 eval_hfexpr_validif_policy invalid site flat_memories (data_reader_expression port) old old = Some value ->
 concrete_ground_value value.
Proof.
 intros Member Storage Concrete Enable Address Eval.
 rewrite (data_reader_expression_eval invalid site port old Member) in Eval.
 destruct (data_memory_any_reader_concrete port old old values [::true] address width value
 Member Storage Enable (Logic.eq_refl _) Address Concrete Eval) as [bits Value].
 exists (Fuint 32), bits. exact Value.
Qed.
Theorem data_reader_mux_concrete invalid site port condition source old values address width cg cb sg sb value :
 List.In port [::1;2;3;4;5] ->
 VM.find 9179 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 read_memory_port_field old 9178 port 1 = Some (Gval (Fuint 1) [::true]) ->
 read_memory_port_field old 9178 port 0 = Some (Gval (Fuint width) address) ->
 VM.find condition old = Some (Gval cg cb) ->
 VM.find source old = Some (Gval sg sb) ->
 eval_hfexpr_validif_policy invalid site flat_memories
 (Emux (Eref (Eid condition)) (Eref (Eid source)) (data_reader_expression port)) old old = Some value ->
 concrete_ground_value value.
Proof.
 intros Member Storage Concrete Enable Address Condition Source Eval.
 eapply concrete_policy_mux; [| | |exact Eval].
 - intros location result E. cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in E.
   rewrite Condition in E. inversion E; subst. do 2 eexists; reflexivity.
 - intros location result E. cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in E.
   rewrite Source in E. inversion E; subst. do 2 eexists; reflexivity.
 - intros location result E. eapply data_reader_expression_concrete; eassumption.
Qed.
Print Assumptions data_reader_mux_concrete.
