Require Import CoreSocModel.
From firrtl Require Import Semantics_with_memory Semantics_with_implicit_widths.
Definition flat_iteration_count := circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count.
Lemma flat_iteration_count_exact : flat_iteration_count = Some 9259.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions flat_iteration_count_exact.
