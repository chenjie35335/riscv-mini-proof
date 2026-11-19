Require Import RFUpperDUTCopyOutput RFALUData ALUInputStability ALUOperandTransfer LoadEffectiveAddress FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_upper_dut_copy_commit memory inputs k observed next immediate right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 size immediate=32%nat ->
 VM.find 87(top_environment observed)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 89(top_environment observed)=Some(Gval(Fuint 4)(from_N 4 11)) ->
 VM.find 1308(top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)immediate).
Proof.
 intros Observe Legal Next Reset Size Select Mode Imm Right.
 destruct(rf_alu_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 assert(Root:forall node value t,List.In node alu_stability_roots ->VM.find(N.of_nat node)(top_environment observed)=Some value ->(128<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find(N.of_nat node)(history t)=Some value).
 { intros node value t Member Value Lower Upper.
 rewrite(proj2(alu_stability_roots_history (generated_observation_input inputs k)nil history 9259 Boundary Steps node Member t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia)))Last;exact Value. }
 assert(B:forall t,(131<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1152(history t)=Some(Gval(Fuint 32)immediate)).
 { intros t Lower Upper. eapply(alu_operand_selected_history _ history 9259 128 false immediate Size Steps true).
 - intros u Lo Hi. exact(Root 87%nat _ u ltac:(right;left;reflexivity)Select Lo Hi).
 - intros u Lo Hi. exact(alu_stable_value_at (generated_observation_input inputs k)nil history 1308 _ u Boundary Steps ltac:(right;right;right;right;right;left;reflexivity)Lo Hi ltac:(rewrite Last;exact Imm)).
 - intros u Lo Hi. exists(Gval(Fuint 32)right). split;[exact(Root 7819%nat _ u ltac:(right;right;right;right;right;right;right;left;reflexivity)Right Lo Hi)|reflexivity].
 - exact Lower.
 - exact Upper. }
 assert(M:forall t,(131<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)(from_N 4 11))).
 { intros[|t]Lo Hi;[lia|]. exact(load_operand_wire_value 2%nat _ (history t)(history t)(history(S t))(from_N 4 11)ltac:(lia)(size_from_N _ _)
 (Root 89%nat _ t ltac:(right;right;right;left;reflexivity)Mode ltac:(lia)ltac:(lia))(Steps t ltac:(lia))). }
 apply(Transfer immediate Size).
 exact(rf_upper_dut_copy_output _ history 9259 131 immediate Size Steps M B 9257 ltac:(vm_compute;lia)ltac:(vm_compute;lia)).
Qed.
