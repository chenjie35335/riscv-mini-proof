Require Import CoreSocModel JointBoundaryInitialization JointBoundaryResetBase JointBoundaryInduction.
Theorem joint_boundary_reachable memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k ->
 joint_boundary_concrete states.
Proof.
 exact (joint_boundary_induction memory inputs (joint_boundary_run_zero memory inputs) k states).
Qed.
Print Assumptions joint_boundary_reachable.
