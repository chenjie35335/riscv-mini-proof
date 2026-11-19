Require Import CoreSocModel JointBoundaryInitialization JointBoundaryRunStep JointScalarResetBase DataStorageResetBase LoadSizedResetBase FetchSizedResetBase.
From Coq Require Import Arith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
Theorem joint_boundary_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states -> joint_boundary_concrete states.
Proof.
 intro Run. split; [|exact (data_storage_run_zero memory inputs states Run)].
 intros node width Member.
 destruct (Nat.eq_dec node 9220) as [Equal|NotFetch].
 - subst node. rewrite (joint_fetch_register_width width Member). exact (fetch_sized_run_zero memory inputs states Run).
 - destruct (Nat.eq_dec node 9222) as [Equal|NotLoad].
   + subst node. rewrite (joint_load_register_width width Member). exact (load_sized_run_zero memory inputs states Run).
   + exact (joint_scalar_run_zero memory inputs states Run node width Member NotFetch NotLoad).
Qed.
Print Assumptions joint_boundary_run_zero.
