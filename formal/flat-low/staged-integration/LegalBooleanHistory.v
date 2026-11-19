Require Import CoreSocModel ComparisonNodes LegalBooleanCone FormalLocalHistory NormalizedBit.
From Coq Require Import ZArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem legal_bool_9028_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9028 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9028_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9030_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9030 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9030_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9032_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9032 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9032_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9034_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9034 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9034_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9036_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9036 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9036_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9038_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9038 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9038_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9040_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9040 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9040_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9042_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9042 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9042_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9044_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9044 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9044_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9046_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9046 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9046_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9048_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9048 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9048_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9050_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9050 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9050_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9051_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9051 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9051_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9030_history invalid history limit Steps time); lia.
 - apply (legal_bool_9032_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9052_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9052 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9052_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9051_history invalid history limit Steps time); lia.
 - apply (legal_bool_9034_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9053_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9053 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9053_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9052_history invalid history limit Steps time); lia.
 - apply (legal_bool_9036_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9054_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9054 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9054_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9053_history invalid history limit Steps time); lia.
 - apply (legal_bool_9038_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9055_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9055 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9055_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9054_history invalid history limit Steps time); lia.
 - apply (legal_bool_9040_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9056_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9056 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9056_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9055_history invalid history limit Steps time); lia.
 - apply (legal_bool_9042_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9057_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9057 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9057_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9056_history invalid history limit Steps time); lia.
 - apply (legal_bool_9044_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9058_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9058 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9058_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9057_history invalid history limit Steps time); lia.
 - apply (legal_bool_9046_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9059_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9059 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9059_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9058_history invalid history limit Steps time); lia.
 - apply (legal_bool_9048_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9060_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9060 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9060_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9059_history invalid history limit Steps time); lia.
 - apply (legal_bool_9050_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9062_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9062 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9062_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9064_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9064 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9064_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9066_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9066 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9066_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9068_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9068 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9068_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9070_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9070 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9070_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9072_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9072 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9072_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9074_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9074 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9074_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9076_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9076 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9076_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9078_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9078 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9078_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9080_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9080 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9080_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9081_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9081 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9081_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9062_history invalid history limit Steps time); lia.
 - apply (legal_bool_9064_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9082_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9082 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9082_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9081_history invalid history limit Steps time); lia.
 - apply (legal_bool_9066_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9083_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9083 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9083_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9082_history invalid history limit Steps time); lia.
 - apply (legal_bool_9068_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9084_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9084 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9084_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9083_history invalid history limit Steps time); lia.
 - apply (legal_bool_9070_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9085_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9085 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9085_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9084_history invalid history limit Steps time); lia.
 - apply (legal_bool_9072_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9086_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9086 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9086_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9085_history invalid history limit Steps time); lia.
 - apply (legal_bool_9074_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9087_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9087 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9087_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9086_history invalid history limit Steps time); lia.
 - apply (legal_bool_9076_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9088_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9088 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9088_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9087_history invalid history limit Steps time); lia.
 - apply (legal_bool_9078_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9089_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9089 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9089_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9088_history invalid history limit Steps time); lia.
 - apply (legal_bool_9080_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9090_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9090 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9090_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9060_history invalid history limit Steps time); lia.
 - apply (legal_bool_9089_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9092_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9092 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9092_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9094_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9094 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9094_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9096_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9096 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9096_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9098_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9098 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9098_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9100_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9100 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9100_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9102_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9102 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9102_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9104_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9104 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9104_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9106_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9106 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9106_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9107_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9107 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9107_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9092_history invalid history limit Steps time); lia.
 - apply (legal_bool_9094_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9108_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9108 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9108_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9107_history invalid history limit Steps time); lia.
 - apply (legal_bool_9096_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9109_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9109 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9109_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9108_history invalid history limit Steps time); lia.
 - apply (legal_bool_9098_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9110_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9110 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9110_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9109_history invalid history limit Steps time); lia.
 - apply (legal_bool_9100_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9111_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9111 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9111_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9110_history invalid history limit Steps time); lia.
 - apply (legal_bool_9102_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9112_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9112 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9112_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9111_history invalid history limit Steps time); lia.
 - apply (legal_bool_9104_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9113_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9113 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9113_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9112_history invalid history limit Steps time); lia.
 - apply (legal_bool_9106_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9114_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9114 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9114_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9090_history invalid history limit Steps time); lia.
 - apply (legal_bool_9113_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9116_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9116 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9116_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9118_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9118 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9118_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9120_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9120 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9120_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9122_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9122 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9122_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9124_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9124 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9124_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9126_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9126 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9126_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9128_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9128 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9128_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9130_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9130 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9130_normalized invalid (history time) (history time) (history (S time))).
 apply Steps. lia.
Qed.
Theorem legal_bool_9131_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9131 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9131_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9116_history invalid history limit Steps time); lia.
 - apply (legal_bool_9118_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9132_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9132 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9132_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9131_history invalid history limit Steps time); lia.
 - apply (legal_bool_9120_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9133_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9133 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9133_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9132_history invalid history limit Steps time); lia.
 - apply (legal_bool_9122_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9134_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9134 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9134_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9133_history invalid history limit Steps time); lia.
 - apply (legal_bool_9124_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9135_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9135 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9135_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9134_history invalid history limit Steps time); lia.
 - apply (legal_bool_9126_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9136_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9136 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9136_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9135_history invalid history limit Steps time); lia.
 - apply (legal_bool_9128_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9137_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9137 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9137_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9136_history invalid history limit Steps time); lia.
 - apply (legal_bool_9130_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9138_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9138 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9138_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9114_history invalid history limit Steps time); lia.
 - apply (legal_bool_9137_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem legal_bool_9139_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 9139 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_9139_normalized invalid (history time) (history time) (history (S time))).
 - apply (legal_bool_9028_history invalid history limit Steps time); lia.
 - apply (legal_bool_9138_history invalid history limit Steps time); lia.
 - apply Steps. lia.
Qed.
Print Assumptions legal_bool_9139_history.
