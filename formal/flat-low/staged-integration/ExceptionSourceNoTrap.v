Require Import CoreSocModel ComparisonNodes ExceptionEventHistory ExceptionStabilityHistory JointBoundaryRegisters ConcreteRegisterInitialization NormalizedBit.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem exception_source_false_after_settling inputs path history :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 forall time, (41 <= time)%coq_nat -> (time <= 9259)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Boundary Steps NoTrap.
 destruct (exception_concrete_128_history inputs path history 9259 Boundary Steps 9249 ltac:(vm_compute; lia) ltac:(vm_compute; lia))
 as [width [bits Concrete]].
 destruct (exception_source128_normalized _ (history 9248%nat) (history 9248%nat) (history 9249%nat)
 (Steps 9248%nat ltac:(vm_compute; lia))) as [value [Value Normal]].
 assert (Bit : exists bit, VM.find 128 (history 9249%nat) = Some (Gval (Fuint 1) [::bit])).
 { destruct Normal as [bit| | |].
   - exists bit. exact Value.
   - rewrite Concrete in Value. discriminate Value.
   - rewrite Concrete in Value. discriminate Value.
   - rewrite Concrete in Value. discriminate Value. }
 destruct Bit as [bit Source].
 pose proof (exception_trap_after_five _ (history 9249%nat) (history 9250%nat) (history 9251%nat)
 (history 9252%nat) (history 9253%nat) (history 9254%nat) bit Source
 (Steps 9249%nat ltac:(vm_compute; lia)) (Steps 9250%nat ltac:(vm_compute; lia))
 (Steps 9251%nat ltac:(vm_compute; lia)) (Steps 9252%nat ltac:(vm_compute; lia))
 (Steps 9253%nat ltac:(vm_compute; lia))) as TrapValue.
 rewrite NoTrap in TrapValue. inversion TrapValue; subst bit.
 intros time Lower Upper.
 rewrite (exception_stable_128_history inputs path history 9259 Boundary Steps time 9249
 Lower ltac:(vm_compute;lia) Upper ltac:(vm_compute;lia)). exact Source.
Qed.
Print Assumptions exception_source_false_after_settling.
