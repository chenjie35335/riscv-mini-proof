Require Import AddressAssertion1Reset RequestEnableNormalized FormalNodeEquation JointBoundaryRegisters CoreSocModel ComparisonNodes CycleView ReferenceNonloadDecode ReferenceZeroReadValid ReadValidHistory ObservedLegalNoTrap ExceptionSourceNoTrap ObservedJointRegisterConcrete ConcreteRegisterInitialization FormalResetPreparation ReferenceMemoryRequest MemoryRequestObservedSemantics LoadTypeCorrespondence LoadPipelineClassification ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory JointUpdateBoundaryHistory FormalAssertionDischarge MemoryRequestWidth.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem nonload_address_assertion1 memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 load_type_decode(to_N instruction)49=from_N 3 0 ->generated_assert_m0_1_local(top_environment observed).
Proof.
 intros Observe Legal Reset Instruction Zero.
 destruct(memory_reference_enable_known memory inputs k observed Observe Legal Reset)as[enabled Enabled].
 pose proof(reference_nonload_guards_observed memory inputs k observed instruction enabled Observe Legal Instruction Zero Enabled)as Decode.
 destruct(observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as[committed[initial[history[Run[Prepare[First[Last[Steps NoTrap]]]]]]]].
 destruct(top_reset_prepared(Some committed)_ initial _ Reset Prepare)as[env[Env InitialReset]].
 assert(Reset0:VM.find 1(history 0%nat)=Some(Gval(Fuint 1)[::false])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 pose proof(legal_local_reset_history _ history 9259 false Steps Reset0)as Resets.
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member.
   destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[word[Size Value]].
   exists word;split;[exact Size|].
   rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)).
   rewrite Last. exact Value. }
 assert(Enable:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::enabled])).
 { intros t Lower Upper. rewrite(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 false Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert(Guards:forall node,List.In node [::1970;1966;1962;1958;1886] ->forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::false])).
 { intros node Member t Lower Upper. cbn in Member. repeat destruct Member as[<-|Member];try contradiction.
 - rewrite(reference_control_stable_1970_history (generated_observation_input inputs k)nil history 9259 false Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact(Decode 4%nat ltac:(lia)).
 - rewrite(reference_control_stable_1966_history (generated_observation_input inputs k)nil history 9259 false Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact(Decode 3%nat ltac:(lia)).
 - rewrite(reference_control_stable_1962_history (generated_observation_input inputs k)nil history 9259 false Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact(Decode 2%nat ltac:(lia)).
 - rewrite(reference_control_stable_1958_history (generated_observation_input inputs k)nil history 9259 false Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact(Decode 1%nat ltac:(lia)).
 - rewrite(reference_control_stable_1886_history (generated_observation_input inputs k)nil history 9259 false Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact(Decode 0%nat ltac:(lia)).
 }
 assert(Ref:forall t,(210<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1519(history t)=Some(Gval(Fuint 1)(zeros 1))).
 { intros t Lower Upper. exact(reference_zero_read_valid_history _ history 9259 200 enabled Steps Enable Guards t Lower Upper). }
 pose proof(load_pipeline_observed memory inputs k observed Observe Legal instruction Instruction)as Mode. rewrite Zero in Mode.
 assert(Modes:forall t,(t<=9259)%coq_nat ->VM.find 7755(history t)=Some(Gval(Fuint 3)(from_N 3 0))).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7755 3 load_type_register_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite <-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Mode. }
 assert(Dut:forall t,(47<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1474(history t)=Some(Gval(Fuint 1)[::false])).
 { intros t Lower Upper. eapply(read_valid_history 0%nat _ history 9259 41 ltac:(lia)Steps).
 - intros u Lo Hi. exact(memory_width_decoder_history false 0%nat _ history 9259 ltac:(cbn;lia) Steps Modes u ltac:(lia) Hi).
 - exact(exception_source_false_after_settling (generated_observation_input inputs k)nil history Boundary Steps NoTrap).
 - exact Lower.
 - exact Upper. }
 assert(Valid:VM.find 7569(history 9259)=Some(Gval(Fuint 1)[::false])).
 { rewrite(formal_combinational_node_equation _ _ _ _ _ _ flat_memories (history 9258)(history 9258)(history 9259) read_valid_or_position read_valid_or_suffix read_valid_or_nonregister (Steps 9258 ltac:(vm_compute;lia))).
 unfold read_valid_or_expression. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Dut 9258 ltac:(vm_compute;lia)ltac:(vm_compute;lia))(Ref 9258 ltac:(vm_compute;lia)ltac:(vm_compute;lia)). reflexivity. }
 pose proof(address_assertion1_reset_guard_observed memory inputs k observed false Observe Reset)as Guard.
 rewrite Last in Valid. unfold generated_assert_m0_1_local,generated_expr_true.
 cbn[eval_hfexpr eval_href]. rewrite Valid Guard. vm_compute;intro Impossible;discriminate Impossible.
Qed.
