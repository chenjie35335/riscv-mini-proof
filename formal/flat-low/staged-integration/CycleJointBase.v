Require Import CycleInitialState CycleJointReachability CycleDataNormalStep CycleView
 PCRelativePendingInvariant CycleRedirectDecision JALRPendingInvariant JALRTakenInvariant CoreSocModel FormalLocalHistory.
Local Opaque generated_modules generated_top.
Theorem cycle_joint_initial memory inputs observed :
 generated_observe memory inputs 0=Some observed ->generated_legal_trace memory inputs 0 ->
 exists v,cycle_view_at(top_environment observed)v /\cycle_pc_aligned v /\cycle_joint_pending(top_environment observed)v.
Proof.
 intros Observe Legal.
 destruct(cycle_initial_view memory inputs observed Observe Legal)as[v[View[Banks PC]]].
 exists v. split;[exact View|]. split;[exact PC|].
 split;[exact(cycle_data_base memory inputs observed v Observe Legal View)|].
 split;[exact(cycle_pc_relative_pending_base memory inputs observed v Observe View)|].
 split;[exact(cycle_redirect_decision_base memory inputs observed v Observe View)|].
 split;[exact(cycle_jalr_pending_base memory inputs observed v Observe View)|].
 exact(cycle_jalr_taken_base memory inputs observed v Observe View).
Qed.
