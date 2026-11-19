Require Import CycleRFOriginalAssertions CycleJointInvariant CycleJointReachability CycleDataReachability
 CycleISAReferenceAdvance RFArithmeticPendingClosure RFModeReachability RFArchitecturalWriteEffect
 CycleView ExternalReset CoreSocModel FormalLocalHistory.
From Coq Require Import Lia.
Local Opaque generated_modules generated_top.
Theorem cycle_rf_original_assertion_reachable memory inputs k observed index :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (index<32)%nat ->rf_original_assertion_all index observed.
Proof.
 intros Observe Legal Index.
 destruct(legal_observation_reset memory inputs k Legal)as[bit Reset].
 destruct bit.
 - exact(cycle_rf_original_assertion_reset memory inputs k observed index Observe Legal Reset Index).
 - destruct(cycle_joint_observed_invariant memory inputs k observed Observe Legal)as[v[View[PC[Data[Relative[Decision[Jalr Taken]]]]]]].
   destruct Data as[Banks[Arithmetic[Memory[Store Assertion]]]].
   destruct Arithmetic as[Add[Bitwise[Subtract[Compare[Immediate[Shift Upper]]]]]].
   assert(Pending:cycle_isa_pending v).
   { constructor;try assumption.
     - exact(cycle_writeback_mode_reachable memory inputs k observed v Observe Legal View).
     - exact(proj2 PC). }
   exact(cycle_rf_original_assertion_normal memory inputs k observed v index Observe Legal Reset View Banks Pending Index).
Qed.
