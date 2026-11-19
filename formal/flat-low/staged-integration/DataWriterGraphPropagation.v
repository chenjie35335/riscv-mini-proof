Require Import CoreSocModel ComparisonNodes DataWriterDependencyRanks DataAddressOutputCertificates DataAddressConnectionCertificates DataAddressUnaryConnection DataWriterOutputCertificates DataWriterConnectionCertificates DataWriterUIntOutputs DataMemoryMuxCertificates ConcreteMemoryRead CheckedDependencyHistory.
From Coq Require Import ZArith List Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition writer_uint_required (node : nat) := List.existsb (N.eqb (N.of_nat node))
 [::N.of_nat 851;N.of_nat 9214;N.of_nat 9224;N.of_nat 9225;N.of_nat 9227;N.of_nat 9228;N.of_nat 9229;N.of_nat 9230;N.of_nat 9232;N.of_nat 9233;N.of_nat 9234].
Definition writer_concrete_at (env : VM.t hvalue) (node : nat) : Prop :=
 if writer_uint_required node then exists width bits, VM.find (N.of_nat node) env = Some (Gval (Fuint width) bits)
 else exists ground bits, VM.find (N.of_nat node) env = Some (Gval ground bits).
Lemma writer_concrete_ground env node : writer_concrete_at env node ->
 exists ground bits, VM.find (N.of_nat node) env = Some (Gval ground bits).
Proof.
 unfold writer_concrete_at. destruct (writer_uint_required node); intro Value; [|exact Value].
 destruct Value as [width [bits Value]]. exists (Fuint width), bits. exact Value.
Qed.
Definition writer_memory_ready env := exists values,
 VM.find (N.of_nat 9179) env = Some (Aval (Gtyp (Fuint 32)) values) /\
 concrete_uint_array 32 values /\
 forall port, List.In port [::N.of_nat 2;N.of_nat 3;N.of_nat 4;N.of_nat 5] ->
 read_memory_port_field env (N.of_nat 9178) port (N.of_nat 1) = Some (Gval (Fuint 1) [::true]) /\
 exists width address, read_memory_port_field env (N.of_nat 9178) port (N.of_nat 0) = Some (Gval (Fuint width) address).
Definition writer_transfer old result entry := let '(node,(rank,dependencies)) := entry in
 (0 < rank)%coq_nat ->
 (forall source, List.In source dependencies -> writer_concrete_at old source) ->
 writer_concrete_at result node.
Definition data_writer_chunk_0 : list (nat * (nat * list nat)) := [::(1,(0,[::]));(851,(0,[::]));(852,(0,[::]));(853,(0,[::]));(854,(0,[::]));(855,(0,[::]));(856,(0,[::]));(857,(0,[::]));(858,(0,[::]));(859,(0,[::]));(860,(0,[::]));(861,(0,[::]));(862,(0,[::]));(863,(0,[::]));(864,(0,[::]));(865,(0,[::]));(866,(0,[::]));(867,(0,[::]));(868,(0,[::]));(869,(0,[::]));(870,(0,[::]));(871,(0,[::]));(872,(0,[::]));(873,(0,[::]))].
Lemma data_writer_chunk_0_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_0.
Proof.
 intros Memory Step. unfold data_writer_chunk_0.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
Qed.
Definition data_writer_chunk_1 : list (nat * (nat * list nat)) := [::(874,(0,[::]));(875,(0,[::]));(876,(0,[::]));(877,(0,[::]));(878,(0,[::]));(879,(0,[::]));(880,(0,[::]));(881,(0,[::]));(882,(0,[::]));(7748,(0,[::]));(7749,(0,[::]));(7750,(0,[::]));(7752,(0,[::]));(7754,(0,[::]));(7756,(0,[::]));(7757,(0,[::]));(83,(1,[::7748]));(1306,(1,[::7748]));(7803,(1,[::7748]));(7804,(1,[::7748]));(7805,(1,[::7750]));(7814,(1,[::7756]));(7817,(1,[::7756]));(9215,(1,[::1]))].
Lemma data_writer_chunk_1_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_1.
Proof.
 intros Memory Step. unfold data_writer_chunk_1.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   lia. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7748 ltac:(do 0 right; left; reflexivity)) as S7748.
   apply writer_concrete_ground in S7748.
   change (exists ground bits, VM.find (N.of_nat 83) result = Some (Gval ground bits)).
   destruct (data_address_connection_83_output (formal_invalid_policy inputs path) old current result S7748 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7748 ltac:(do 0 right; left; reflexivity)) as S7748.
   apply writer_concrete_ground in S7748.
   change (exists ground bits, VM.find (N.of_nat 1306) result = Some (Gval ground bits)).
   destruct (data_address_connection_1306_output (formal_invalid_policy inputs path) old current result S7748 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7748 ltac:(do 0 right; left; reflexivity)) as S7748.
   apply writer_concrete_ground in S7748.
   change (exists ground bits, VM.find (N.of_nat 7803) result = Some (Gval ground bits)).
   exact (data_address_node_output_7803 inputs path old current result S7748 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7748 ltac:(do 0 right; left; reflexivity)) as S7748.
   apply writer_concrete_ground in S7748.
   change (exists ground bits, VM.find (N.of_nat 7804) result = Some (Gval ground bits)).
   exact (data_address_node_output_7804 inputs path old current result S7748 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7750 ltac:(do 0 right; left; reflexivity)) as S7750.
   apply writer_concrete_ground in S7750.
   change (exists ground bits, VM.find (N.of_nat 7805) result = Some (Gval ground bits)).
   exact (data_address_node_output_7805 inputs path old current result S7750 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7756 ltac:(do 0 right; left; reflexivity)) as S7756.
   apply writer_concrete_ground in S7756.
   change (exists ground bits, VM.find (N.of_nat 7814) result = Some (Gval ground bits)).
   exact (data_address_node_output_7814 inputs path old current result S7756 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7756 ltac:(do 0 right; left; reflexivity)) as S7756.
   apply writer_concrete_ground in S7756.
   change (exists ground bits, VM.find (N.of_nat 7817) result = Some (Gval ground bits)).
   exact (data_address_node_output_7817 inputs path old current result S7756 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1 ltac:(do 0 right; left; reflexivity)) as S1.
   apply writer_concrete_ground in S1.
   change (exists ground bits, VM.find (N.of_nat 9215) result = Some (Gval ground bits)).
   exact (data_address_node_output_9215 inputs path old current result S1 Step). }
 constructor.
Qed.
Definition data_writer_chunk_2 : list (nat * (nat * list nat)) := [::(9217,(1,[::1]));(780,(2,[::7803]));(781,(2,[::7804]));(1309,(2,[::1306]));(1311,(2,[::1306]));(1312,(2,[::1306]));(1315,(2,[::1306]));(1316,(2,[::1306]));(1317,(2,[::1306]));(1318,(2,[::1306]));(1324,(2,[::1306]));(1327,(2,[::1306]));(1328,(2,[::1306]));(1329,(2,[::1306]));(1330,(2,[::1306]));(1331,(2,[::1306]));(1338,(2,[::1306]));(7806,(2,[::7803]));(7808,(2,[::7803;7805]));(7810,(2,[::7804]));(7812,(2,[::7804;7805]));(8249,(2,[::83]));(9216,(2,[::9215]));(9218,(2,[::9217]))].
Lemma data_writer_chunk_2_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_2.
Proof.
 intros Memory Step. unfold data_writer_chunk_2.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1 ltac:(do 0 right; left; reflexivity)) as S1.
   apply writer_concrete_ground in S1.
   change (exists ground bits, VM.find (N.of_nat 9217) result = Some (Gval ground bits)).
   exact (data_address_node_output_9217 inputs path old current result S1 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7803 ltac:(do 0 right; left; reflexivity)) as S7803.
   apply writer_concrete_ground in S7803.
   change (exists ground bits, VM.find (N.of_nat 780) result = Some (Gval ground bits)).
   destruct (data_address_connection_780_output (formal_invalid_policy inputs path) old current result S7803 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7804 ltac:(do 0 right; left; reflexivity)) as S7804.
   apply writer_concrete_ground in S7804.
   change (exists ground bits, VM.find (N.of_nat 781) result = Some (Gval ground bits)).
   destruct (data_address_connection_781_output (formal_invalid_policy inputs path) old current result S7804 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1309) result = Some (Gval ground bits)).
   exact (data_address_node_output_1309 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1311) result = Some (Gval ground bits)).
   exact (data_address_node_output_1311 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1312) result = Some (Gval ground bits)).
   exact (data_address_node_output_1312 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1315) result = Some (Gval ground bits)).
   exact (data_address_node_output_1315 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1316) result = Some (Gval ground bits)).
   exact (data_address_node_output_1316 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1317) result = Some (Gval ground bits)).
   exact (data_address_node_output_1317 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1318) result = Some (Gval ground bits)).
   exact (data_address_node_output_1318 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1324) result = Some (Gval ground bits)).
   exact (data_address_node_output_1324 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1327) result = Some (Gval ground bits)).
   exact (data_address_node_output_1327 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1328) result = Some (Gval ground bits)).
   exact (data_address_node_output_1328 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1329) result = Some (Gval ground bits)).
   exact (data_address_node_output_1329 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1330) result = Some (Gval ground bits)).
   exact (data_address_node_output_1330 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1331) result = Some (Gval ground bits)).
   exact (data_address_node_output_1331 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1306 ltac:(do 0 right; left; reflexivity)) as S1306.
   apply writer_concrete_ground in S1306.
   change (exists ground bits, VM.find (N.of_nat 1338) result = Some (Gval ground bits)).
   exact (data_address_node_output_1338 inputs path old current result S1306 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7803 ltac:(do 0 right; left; reflexivity)) as S7803.
   apply writer_concrete_ground in S7803.
   change (exists ground bits, VM.find (N.of_nat 7806) result = Some (Gval ground bits)).
   exact (data_address_node_output_7806 inputs path old current result S7803 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7803 ltac:(do 0 right; left; reflexivity)) as S7803.
   apply writer_concrete_ground in S7803.
   pose proof (Sources 7805 ltac:(do 1 right; left; reflexivity)) as S7805.
   apply writer_concrete_ground in S7805.
   change (exists ground bits, VM.find (N.of_nat 7808) result = Some (Gval ground bits)).
   exact (data_address_node_output_7808 inputs path old current result S7803 S7805 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7804 ltac:(do 0 right; left; reflexivity)) as S7804.
   apply writer_concrete_ground in S7804.
   change (exists ground bits, VM.find (N.of_nat 7810) result = Some (Gval ground bits)).
   exact (data_address_node_output_7810 inputs path old current result S7804 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7804 ltac:(do 0 right; left; reflexivity)) as S7804.
   apply writer_concrete_ground in S7804.
   pose proof (Sources 7805 ltac:(do 1 right; left; reflexivity)) as S7805.
   apply writer_concrete_ground in S7805.
   change (exists ground bits, VM.find (N.of_nat 7812) result = Some (Gval ground bits)).
   exact (data_address_node_output_7812 inputs path old current result S7804 S7805 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 83 ltac:(do 0 right; left; reflexivity)) as S83.
   apply writer_concrete_ground in S83.
   change (exists ground bits, VM.find (N.of_nat 8249) result = Some (Gval ground bits)).
   destruct (data_address_connection_8249_output (formal_invalid_policy inputs path) old current result S83 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9215 ltac:(do 0 right; left; reflexivity)) as S9215.
   apply writer_concrete_ground in S9215.
   change (exists ground bits, VM.find (N.of_nat 9216) result = Some (Gval ground bits)).
   exact (data_address_node_output_9216 inputs path old current result S9215 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9217 ltac:(do 0 right; left; reflexivity)) as S9217.
   apply writer_concrete_ground in S9217.
   change (exists ground bits, VM.find (N.of_nat 9218) result = Some (Gval ground bits)).
   exact (data_address_node_output_9218 inputs path old current result S9217 Step). }
 constructor.
Qed.
Definition data_writer_chunk_3 : list (nat * (nat * list nat)) := [::(33,(3,[::9216]));(40,(3,[::9218]));(883,(3,[::780]));(884,(3,[::780;851]));(918,(3,[::781]));(919,(3,[::781;851]));(1310,(3,[::1309]));(1313,(3,[::1311;1312]));(1319,(3,[::1318]));(1320,(3,[::1315;1316]));(1325,(3,[::1324]));(1332,(3,[::1330;1331]));(1334,(3,[::1327;1328]));(1339,(3,[::1338]));(7807,(3,[::7757;7806]));(7811,(3,[::7757;7810]));(8263,(3,[::8249]));(8265,(3,[::8249]));(8267,(3,[::8249]));(8269,(3,[::8249]));(8271,(3,[::8249]));(8273,(3,[::8249]));(8275,(3,[::8249]));(8277,(3,[::8249]))].
Lemma data_writer_chunk_3_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_3.
Proof.
 intros Memory Step. unfold data_writer_chunk_3.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9216 ltac:(do 0 right; left; reflexivity)) as S9216.
   apply writer_concrete_ground in S9216.
   change (exists ground bits, VM.find (N.of_nat 33) result = Some (Gval ground bits)).
   destruct (data_address_connection_33_output (formal_invalid_policy inputs path) old current result S9216 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9218 ltac:(do 0 right; left; reflexivity)) as S9218.
   apply writer_concrete_ground in S9218.
   change (exists ground bits, VM.find (N.of_nat 40) result = Some (Gval ground bits)).
   destruct (data_address_connection_40_output (formal_invalid_policy inputs path) old current result S9218 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   change (exists ground bits, VM.find (N.of_nat 883) result = Some (Gval ground bits)).
   exact (data_address_node_output_883 inputs path old current result S780 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 851 ltac:(do 1 right; left; reflexivity)) as S851.
   change (exists ground bits, VM.find (N.of_nat 884) result = Some (Gval ground bits)).
   exact (data_address_node_output_884 inputs path old current result S780 S851 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   change (exists ground bits, VM.find (N.of_nat 918) result = Some (Gval ground bits)).
   exact (data_address_node_output_918 inputs path old current result S781 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 851 ltac:(do 1 right; left; reflexivity)) as S851.
   change (exists ground bits, VM.find (N.of_nat 919) result = Some (Gval ground bits)).
   exact (data_address_node_output_919 inputs path old current result S781 S851 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1309 ltac:(do 0 right; left; reflexivity)) as S1309.
   apply writer_concrete_ground in S1309.
   change (exists ground bits, VM.find (N.of_nat 1310) result = Some (Gval ground bits)).
   exact (data_address_node_output_1310 inputs path old current result S1309 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1311 ltac:(do 0 right; left; reflexivity)) as S1311.
   apply writer_concrete_ground in S1311.
   pose proof (Sources 1312 ltac:(do 1 right; left; reflexivity)) as S1312.
   apply writer_concrete_ground in S1312.
   change (exists ground bits, VM.find (N.of_nat 1313) result = Some (Gval ground bits)).
   exact (data_address_node_output_1313 inputs path old current result S1311 S1312 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1318 ltac:(do 0 right; left; reflexivity)) as S1318.
   apply writer_concrete_ground in S1318.
   change (exists ground bits, VM.find (N.of_nat 1319) result = Some (Gval ground bits)).
   exact (data_address_node_output_1319 inputs path old current result S1318 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1315 ltac:(do 0 right; left; reflexivity)) as S1315.
   apply writer_concrete_ground in S1315.
   pose proof (Sources 1316 ltac:(do 1 right; left; reflexivity)) as S1316.
   apply writer_concrete_ground in S1316.
   change (exists ground bits, VM.find (N.of_nat 1320) result = Some (Gval ground bits)).
   exact (data_address_node_output_1320 inputs path old current result S1315 S1316 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1324 ltac:(do 0 right; left; reflexivity)) as S1324.
   apply writer_concrete_ground in S1324.
   change (exists ground bits, VM.find (N.of_nat 1325) result = Some (Gval ground bits)).
   exact (data_address_node_output_1325 inputs path old current result S1324 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1330 ltac:(do 0 right; left; reflexivity)) as S1330.
   apply writer_concrete_ground in S1330.
   pose proof (Sources 1331 ltac:(do 1 right; left; reflexivity)) as S1331.
   apply writer_concrete_ground in S1331.
   change (exists ground bits, VM.find (N.of_nat 1332) result = Some (Gval ground bits)).
   exact (data_address_node_output_1332 inputs path old current result S1330 S1331 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1327 ltac:(do 0 right; left; reflexivity)) as S1327.
   apply writer_concrete_ground in S1327.
   pose proof (Sources 1328 ltac:(do 1 right; left; reflexivity)) as S1328.
   apply writer_concrete_ground in S1328.
   change (exists ground bits, VM.find (N.of_nat 1334) result = Some (Gval ground bits)).
   exact (data_address_node_output_1334 inputs path old current result S1327 S1328 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1338 ltac:(do 0 right; left; reflexivity)) as S1338.
   apply writer_concrete_ground in S1338.
   change (exists ground bits, VM.find (N.of_nat 1339) result = Some (Gval ground bits)).
   exact (data_address_node_output_1339 inputs path old current result S1338 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7757 ltac:(do 0 right; left; reflexivity)) as S7757.
   apply writer_concrete_ground in S7757.
   pose proof (Sources 7806 ltac:(do 1 right; left; reflexivity)) as S7806.
   apply writer_concrete_ground in S7806.
   change (exists ground bits, VM.find (N.of_nat 7807) result = Some (Gval ground bits)).
   exact (data_address_node_output_7807 inputs path old current result S7757 S7806 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7757 ltac:(do 0 right; left; reflexivity)) as S7757.
   apply writer_concrete_ground in S7757.
   pose proof (Sources 7810 ltac:(do 1 right; left; reflexivity)) as S7810.
   apply writer_concrete_ground in S7810.
   change (exists ground bits, VM.find (N.of_nat 7811) result = Some (Gval ground bits)).
   exact (data_address_node_output_7811 inputs path old current result S7757 S7810 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8263) result = Some (Gval ground bits)).
   exact (data_address_node_output_8263 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8265) result = Some (Gval ground bits)).
   exact (data_address_node_output_8265 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8267) result = Some (Gval ground bits)).
   exact (data_address_node_output_8267 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8269) result = Some (Gval ground bits)).
   exact (data_address_node_output_8269 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8271) result = Some (Gval ground bits)).
   exact (data_address_node_output_8271 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8273) result = Some (Gval ground bits)).
   exact (data_address_node_output_8273 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8275) result = Some (Gval ground bits)).
   exact (data_address_node_output_8275 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8277) result = Some (Gval ground bits)).
   exact (data_address_node_output_8277 inputs path old current result S8249 Step). }
 constructor.
Qed.
Definition data_writer_chunk_4 : list (nat * (nat * list nat)) := [::(8279,(3,[::8249]));(8281,(3,[::8249]));(8283,(3,[::8249]));(8285,(3,[::8249]));(8287,(3,[::8249]));(8289,(3,[::8249]));(8291,(3,[::8249]));(8293,(3,[::8249]));(8295,(3,[::8249]));(8297,(3,[::8249]));(8299,(3,[::8249]));(8301,(3,[::8249]));(8303,(3,[::8249]));(8305,(3,[::8249]));(8307,(3,[::8249]));(8309,(3,[::8249]));(8311,(3,[::8249]));(8313,(3,[::8249]));(8315,(3,[::8249]));(8317,(3,[::8249]));(8319,(3,[::8249]));(8321,(3,[::8249]));(8323,(3,[::8249]));(8325,(3,[::8249]))].
Lemma data_writer_chunk_4_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_4.
Proof.
 intros Memory Step. unfold data_writer_chunk_4.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8279) result = Some (Gval ground bits)).
   exact (data_address_node_output_8279 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8281) result = Some (Gval ground bits)).
   exact (data_address_node_output_8281 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8283) result = Some (Gval ground bits)).
   exact (data_address_node_output_8283 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8285) result = Some (Gval ground bits)).
   exact (data_address_node_output_8285 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8287) result = Some (Gval ground bits)).
   exact (data_address_node_output_8287 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8289) result = Some (Gval ground bits)).
   exact (data_address_node_output_8289 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8291) result = Some (Gval ground bits)).
   exact (data_address_node_output_8291 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8293) result = Some (Gval ground bits)).
   exact (data_address_node_output_8293 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8295) result = Some (Gval ground bits)).
   exact (data_address_node_output_8295 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8297) result = Some (Gval ground bits)).
   exact (data_address_node_output_8297 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8299) result = Some (Gval ground bits)).
   exact (data_address_node_output_8299 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8301) result = Some (Gval ground bits)).
   exact (data_address_node_output_8301 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8303) result = Some (Gval ground bits)).
   exact (data_address_node_output_8303 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8305) result = Some (Gval ground bits)).
   exact (data_address_node_output_8305 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8307) result = Some (Gval ground bits)).
   exact (data_address_node_output_8307 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8309) result = Some (Gval ground bits)).
   exact (data_address_node_output_8309 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8311) result = Some (Gval ground bits)).
   exact (data_address_node_output_8311 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8313) result = Some (Gval ground bits)).
   exact (data_address_node_output_8313 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8315) result = Some (Gval ground bits)).
   exact (data_address_node_output_8315 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8317) result = Some (Gval ground bits)).
   exact (data_address_node_output_8317 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8319) result = Some (Gval ground bits)).
   exact (data_address_node_output_8319 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8321) result = Some (Gval ground bits)).
   exact (data_address_node_output_8321 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8323) result = Some (Gval ground bits)).
   exact (data_address_node_output_8323 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8325) result = Some (Gval ground bits)).
   exact (data_address_node_output_8325 inputs path old current result S8249 Step). }
 constructor.
Qed.
Definition data_writer_chunk_5 : list (nat * (nat * list nat)) := [::(8327,(3,[::8249]));(8329,(3,[::8249]));(8331,(3,[::8249]));(8333,(3,[::8249]));(8335,(3,[::8249]));(8337,(3,[::8249]));(8339,(3,[::8249]));(8341,(3,[::8249]));(8343,(3,[::8249]));(8345,(3,[::8249]));(8347,(3,[::8249]));(8349,(3,[::8249]));(8351,(3,[::8249]));(8353,(3,[::8249]));(8355,(3,[::8249]));(8357,(3,[::8249]));(8359,(3,[::8249]));(74,(4,[::33]));(81,(4,[::40]));(885,(4,[::780;852;884]));(920,(4,[::781;852;919]));(1314,(4,[::1313]));(1321,(4,[::1317;1320]));(1326,(4,[::1325]))].
Lemma data_writer_chunk_5_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_5.
Proof.
 intros Memory Step. unfold data_writer_chunk_5.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8327) result = Some (Gval ground bits)).
   exact (data_address_node_output_8327 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8329) result = Some (Gval ground bits)).
   exact (data_address_node_output_8329 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8331) result = Some (Gval ground bits)).
   exact (data_address_node_output_8331 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8333) result = Some (Gval ground bits)).
   exact (data_address_node_output_8333 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8335) result = Some (Gval ground bits)).
   exact (data_address_node_output_8335 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8337) result = Some (Gval ground bits)).
   exact (data_address_node_output_8337 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8339) result = Some (Gval ground bits)).
   exact (data_address_node_output_8339 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8341) result = Some (Gval ground bits)).
   exact (data_address_node_output_8341 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8343) result = Some (Gval ground bits)).
   exact (data_address_node_output_8343 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8345) result = Some (Gval ground bits)).
   exact (data_address_node_output_8345 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8347) result = Some (Gval ground bits)).
   exact (data_address_node_output_8347 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8349) result = Some (Gval ground bits)).
   exact (data_address_node_output_8349 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8351) result = Some (Gval ground bits)).
   exact (data_address_node_output_8351 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8353) result = Some (Gval ground bits)).
   exact (data_address_node_output_8353 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8355) result = Some (Gval ground bits)).
   exact (data_address_node_output_8355 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8357) result = Some (Gval ground bits)).
   exact (data_address_node_output_8357 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8249 ltac:(do 0 right; left; reflexivity)) as S8249.
   apply writer_concrete_ground in S8249.
   change (exists ground bits, VM.find (N.of_nat 8359) result = Some (Gval ground bits)).
   exact (data_address_node_output_8359 inputs path old current result S8249 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 33 ltac:(do 0 right; left; reflexivity)) as S33.
   apply writer_concrete_ground in S33.
   change (exists ground bits, VM.find (N.of_nat 74) result = Some (Gval ground bits)).
   destruct (data_address_connection_74_output (formal_invalid_policy inputs path) old current result S33 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 40 ltac:(do 0 right; left; reflexivity)) as S40.
   apply writer_concrete_ground in S40.
   change (exists ground bits, VM.find (N.of_nat 81) result = Some (Gval ground bits)).
   destruct (data_address_connection_81_output (formal_invalid_policy inputs path) old current result S40 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 852 ltac:(do 1 right; left; reflexivity)) as S852.
   apply writer_concrete_ground in S852.
   pose proof (Sources 884 ltac:(do 2 right; left; reflexivity)) as S884.
   apply writer_concrete_ground in S884.
   change (exists ground bits, VM.find (N.of_nat 885) result = Some (Gval ground bits)).
   exact (data_address_node_output_885 inputs path old current result S780 S852 S884 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 852 ltac:(do 1 right; left; reflexivity)) as S852.
   apply writer_concrete_ground in S852.
   pose proof (Sources 919 ltac:(do 2 right; left; reflexivity)) as S919.
   apply writer_concrete_ground in S919.
   change (exists ground bits, VM.find (N.of_nat 920) result = Some (Gval ground bits)).
   exact (data_address_node_output_920 inputs path old current result S781 S852 S919 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1313 ltac:(do 0 right; left; reflexivity)) as S1313.
   apply writer_concrete_ground in S1313.
   change (exists ground bits, VM.find (N.of_nat 1314) result = Some (Gval ground bits)).
   exact (data_address_node_output_1314 inputs path old current result S1313 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1317 ltac:(do 0 right; left; reflexivity)) as S1317.
   apply writer_concrete_ground in S1317.
   pose proof (Sources 1320 ltac:(do 1 right; left; reflexivity)) as S1320.
   apply writer_concrete_ground in S1320.
   change (exists ground bits, VM.find (N.of_nat 1321) result = Some (Gval ground bits)).
   exact (data_address_node_output_1321 inputs path old current result S1317 S1320 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1325 ltac:(do 0 right; left; reflexivity)) as S1325.
   apply writer_concrete_ground in S1325.
   change (exists ground bits, VM.find (N.of_nat 1326) result = Some (Gval ground bits)).
   exact (data_address_node_output_1326 inputs path old current result S1325 Step). }
 constructor.
Qed.
Definition data_writer_chunk_6 : list (nat * (nat * list nat)) := [::(1333,(4,[::1332]));(1335,(4,[::1329;1334]));(1340,(4,[::1310]));(7809,(4,[::7807;7808]));(7813,(4,[::7811;7812]));(8264,(4,[::8263]));(8266,(4,[::8265]));(8268,(4,[::8267]));(8270,(4,[::8269]));(8272,(4,[::8271]));(8274,(4,[::8273]));(8276,(4,[::8275]));(8278,(4,[::8277]));(8280,(4,[::8279]));(8282,(4,[::8281]));(8284,(4,[::8283]));(8286,(4,[::8285]));(8288,(4,[::8287]));(8290,(4,[::8289]));(8292,(4,[::8291]));(8294,(4,[::8293]));(8296,(4,[::8295]));(8298,(4,[::8297]));(8300,(4,[::8299]))].
Lemma data_writer_chunk_6_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_6.
Proof.
 intros Memory Step. unfold data_writer_chunk_6.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1332 ltac:(do 0 right; left; reflexivity)) as S1332.
   apply writer_concrete_ground in S1332.
   change (exists ground bits, VM.find (N.of_nat 1333) result = Some (Gval ground bits)).
   exact (data_address_node_output_1333 inputs path old current result S1332 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1329 ltac:(do 0 right; left; reflexivity)) as S1329.
   apply writer_concrete_ground in S1329.
   pose proof (Sources 1334 ltac:(do 1 right; left; reflexivity)) as S1334.
   apply writer_concrete_ground in S1334.
   change (exists ground bits, VM.find (N.of_nat 1335) result = Some (Gval ground bits)).
   exact (data_address_node_output_1335 inputs path old current result S1329 S1334 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1310 ltac:(do 0 right; left; reflexivity)) as S1310.
   apply writer_concrete_ground in S1310.
   change (exists ground bits, VM.find (N.of_nat 1340) result = Some (Gval ground bits)).
   exact (data_address_node_output_1340 inputs path old current result S1310 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7807 ltac:(do 0 right; left; reflexivity)) as S7807.
   apply writer_concrete_ground in S7807.
   pose proof (Sources 7808 ltac:(do 1 right; left; reflexivity)) as S7808.
   apply writer_concrete_ground in S7808.
   change (exists ground bits, VM.find (N.of_nat 7809) result = Some (Gval ground bits)).
   exact (data_address_node_output_7809 inputs path old current result S7807 S7808 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7811 ltac:(do 0 right; left; reflexivity)) as S7811.
   apply writer_concrete_ground in S7811.
   pose proof (Sources 7812 ltac:(do 1 right; left; reflexivity)) as S7812.
   apply writer_concrete_ground in S7812.
   change (exists ground bits, VM.find (N.of_nat 7813) result = Some (Gval ground bits)).
   exact (data_address_node_output_7813 inputs path old current result S7811 S7812 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8263 ltac:(do 0 right; left; reflexivity)) as S8263.
   apply writer_concrete_ground in S8263.
   change (exists ground bits, VM.find (N.of_nat 8264) result = Some (Gval ground bits)).
   exact (data_address_node_output_8264 inputs path old current result S8263 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8265 ltac:(do 0 right; left; reflexivity)) as S8265.
   apply writer_concrete_ground in S8265.
   change (exists ground bits, VM.find (N.of_nat 8266) result = Some (Gval ground bits)).
   exact (data_address_node_output_8266 inputs path old current result S8265 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8267 ltac:(do 0 right; left; reflexivity)) as S8267.
   apply writer_concrete_ground in S8267.
   change (exists ground bits, VM.find (N.of_nat 8268) result = Some (Gval ground bits)).
   exact (data_address_node_output_8268 inputs path old current result S8267 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8269 ltac:(do 0 right; left; reflexivity)) as S8269.
   apply writer_concrete_ground in S8269.
   change (exists ground bits, VM.find (N.of_nat 8270) result = Some (Gval ground bits)).
   exact (data_address_node_output_8270 inputs path old current result S8269 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8271 ltac:(do 0 right; left; reflexivity)) as S8271.
   apply writer_concrete_ground in S8271.
   change (exists ground bits, VM.find (N.of_nat 8272) result = Some (Gval ground bits)).
   exact (data_address_node_output_8272 inputs path old current result S8271 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8273 ltac:(do 0 right; left; reflexivity)) as S8273.
   apply writer_concrete_ground in S8273.
   change (exists ground bits, VM.find (N.of_nat 8274) result = Some (Gval ground bits)).
   exact (data_address_node_output_8274 inputs path old current result S8273 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8275 ltac:(do 0 right; left; reflexivity)) as S8275.
   apply writer_concrete_ground in S8275.
   change (exists ground bits, VM.find (N.of_nat 8276) result = Some (Gval ground bits)).
   exact (data_address_node_output_8276 inputs path old current result S8275 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8277 ltac:(do 0 right; left; reflexivity)) as S8277.
   apply writer_concrete_ground in S8277.
   change (exists ground bits, VM.find (N.of_nat 8278) result = Some (Gval ground bits)).
   exact (data_address_node_output_8278 inputs path old current result S8277 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8279 ltac:(do 0 right; left; reflexivity)) as S8279.
   apply writer_concrete_ground in S8279.
   change (exists ground bits, VM.find (N.of_nat 8280) result = Some (Gval ground bits)).
   exact (data_address_node_output_8280 inputs path old current result S8279 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8281 ltac:(do 0 right; left; reflexivity)) as S8281.
   apply writer_concrete_ground in S8281.
   change (exists ground bits, VM.find (N.of_nat 8282) result = Some (Gval ground bits)).
   exact (data_address_node_output_8282 inputs path old current result S8281 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8283 ltac:(do 0 right; left; reflexivity)) as S8283.
   apply writer_concrete_ground in S8283.
   change (exists ground bits, VM.find (N.of_nat 8284) result = Some (Gval ground bits)).
   exact (data_address_node_output_8284 inputs path old current result S8283 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8285 ltac:(do 0 right; left; reflexivity)) as S8285.
   apply writer_concrete_ground in S8285.
   change (exists ground bits, VM.find (N.of_nat 8286) result = Some (Gval ground bits)).
   exact (data_address_node_output_8286 inputs path old current result S8285 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8287 ltac:(do 0 right; left; reflexivity)) as S8287.
   apply writer_concrete_ground in S8287.
   change (exists ground bits, VM.find (N.of_nat 8288) result = Some (Gval ground bits)).
   exact (data_address_node_output_8288 inputs path old current result S8287 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8289 ltac:(do 0 right; left; reflexivity)) as S8289.
   apply writer_concrete_ground in S8289.
   change (exists ground bits, VM.find (N.of_nat 8290) result = Some (Gval ground bits)).
   exact (data_address_node_output_8290 inputs path old current result S8289 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8291 ltac:(do 0 right; left; reflexivity)) as S8291.
   apply writer_concrete_ground in S8291.
   change (exists ground bits, VM.find (N.of_nat 8292) result = Some (Gval ground bits)).
   exact (data_address_node_output_8292 inputs path old current result S8291 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8293 ltac:(do 0 right; left; reflexivity)) as S8293.
   apply writer_concrete_ground in S8293.
   change (exists ground bits, VM.find (N.of_nat 8294) result = Some (Gval ground bits)).
   exact (data_address_node_output_8294 inputs path old current result S8293 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8295 ltac:(do 0 right; left; reflexivity)) as S8295.
   apply writer_concrete_ground in S8295.
   change (exists ground bits, VM.find (N.of_nat 8296) result = Some (Gval ground bits)).
   exact (data_address_node_output_8296 inputs path old current result S8295 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8297 ltac:(do 0 right; left; reflexivity)) as S8297.
   apply writer_concrete_ground in S8297.
   change (exists ground bits, VM.find (N.of_nat 8298) result = Some (Gval ground bits)).
   exact (data_address_node_output_8298 inputs path old current result S8297 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8299 ltac:(do 0 right; left; reflexivity)) as S8299.
   apply writer_concrete_ground in S8299.
   change (exists ground bits, VM.find (N.of_nat 8300) result = Some (Gval ground bits)).
   exact (data_address_node_output_8300 inputs path old current result S8299 Step). }
 constructor.
Qed.
Definition data_writer_chunk_7 : list (nat * (nat * list nat)) := [::(8302,(4,[::8301]));(8304,(4,[::8303]));(8306,(4,[::8305]));(8308,(4,[::8307]));(8310,(4,[::8309]));(8312,(4,[::8311]));(8314,(4,[::8313]));(8316,(4,[::8315]));(8318,(4,[::8317]));(8320,(4,[::8319]));(8322,(4,[::8321]));(8324,(4,[::8323]));(8326,(4,[::8325]));(8328,(4,[::8327]));(8330,(4,[::8329]));(8332,(4,[::8331]));(8334,(4,[::8333]));(8336,(4,[::8335]));(8338,(4,[::8337]));(8340,(4,[::8339]));(8342,(4,[::8341]));(8344,(4,[::8343]));(8346,(4,[::8345]));(8348,(4,[::8347]))].
Lemma data_writer_chunk_7_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_7.
Proof.
 intros Memory Step. unfold data_writer_chunk_7.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8301 ltac:(do 0 right; left; reflexivity)) as S8301.
   apply writer_concrete_ground in S8301.
   change (exists ground bits, VM.find (N.of_nat 8302) result = Some (Gval ground bits)).
   exact (data_address_node_output_8302 inputs path old current result S8301 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8303 ltac:(do 0 right; left; reflexivity)) as S8303.
   apply writer_concrete_ground in S8303.
   change (exists ground bits, VM.find (N.of_nat 8304) result = Some (Gval ground bits)).
   exact (data_address_node_output_8304 inputs path old current result S8303 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8305 ltac:(do 0 right; left; reflexivity)) as S8305.
   apply writer_concrete_ground in S8305.
   change (exists ground bits, VM.find (N.of_nat 8306) result = Some (Gval ground bits)).
   exact (data_address_node_output_8306 inputs path old current result S8305 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8307 ltac:(do 0 right; left; reflexivity)) as S8307.
   apply writer_concrete_ground in S8307.
   change (exists ground bits, VM.find (N.of_nat 8308) result = Some (Gval ground bits)).
   exact (data_address_node_output_8308 inputs path old current result S8307 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8309 ltac:(do 0 right; left; reflexivity)) as S8309.
   apply writer_concrete_ground in S8309.
   change (exists ground bits, VM.find (N.of_nat 8310) result = Some (Gval ground bits)).
   exact (data_address_node_output_8310 inputs path old current result S8309 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8311 ltac:(do 0 right; left; reflexivity)) as S8311.
   apply writer_concrete_ground in S8311.
   change (exists ground bits, VM.find (N.of_nat 8312) result = Some (Gval ground bits)).
   exact (data_address_node_output_8312 inputs path old current result S8311 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8313 ltac:(do 0 right; left; reflexivity)) as S8313.
   apply writer_concrete_ground in S8313.
   change (exists ground bits, VM.find (N.of_nat 8314) result = Some (Gval ground bits)).
   exact (data_address_node_output_8314 inputs path old current result S8313 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8315 ltac:(do 0 right; left; reflexivity)) as S8315.
   apply writer_concrete_ground in S8315.
   change (exists ground bits, VM.find (N.of_nat 8316) result = Some (Gval ground bits)).
   exact (data_address_node_output_8316 inputs path old current result S8315 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8317 ltac:(do 0 right; left; reflexivity)) as S8317.
   apply writer_concrete_ground in S8317.
   change (exists ground bits, VM.find (N.of_nat 8318) result = Some (Gval ground bits)).
   exact (data_address_node_output_8318 inputs path old current result S8317 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8319 ltac:(do 0 right; left; reflexivity)) as S8319.
   apply writer_concrete_ground in S8319.
   change (exists ground bits, VM.find (N.of_nat 8320) result = Some (Gval ground bits)).
   exact (data_address_node_output_8320 inputs path old current result S8319 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8321 ltac:(do 0 right; left; reflexivity)) as S8321.
   apply writer_concrete_ground in S8321.
   change (exists ground bits, VM.find (N.of_nat 8322) result = Some (Gval ground bits)).
   exact (data_address_node_output_8322 inputs path old current result S8321 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8323 ltac:(do 0 right; left; reflexivity)) as S8323.
   apply writer_concrete_ground in S8323.
   change (exists ground bits, VM.find (N.of_nat 8324) result = Some (Gval ground bits)).
   exact (data_address_node_output_8324 inputs path old current result S8323 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8325 ltac:(do 0 right; left; reflexivity)) as S8325.
   apply writer_concrete_ground in S8325.
   change (exists ground bits, VM.find (N.of_nat 8326) result = Some (Gval ground bits)).
   exact (data_address_node_output_8326 inputs path old current result S8325 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8327 ltac:(do 0 right; left; reflexivity)) as S8327.
   apply writer_concrete_ground in S8327.
   change (exists ground bits, VM.find (N.of_nat 8328) result = Some (Gval ground bits)).
   exact (data_address_node_output_8328 inputs path old current result S8327 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8329 ltac:(do 0 right; left; reflexivity)) as S8329.
   apply writer_concrete_ground in S8329.
   change (exists ground bits, VM.find (N.of_nat 8330) result = Some (Gval ground bits)).
   exact (data_address_node_output_8330 inputs path old current result S8329 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8331 ltac:(do 0 right; left; reflexivity)) as S8331.
   apply writer_concrete_ground in S8331.
   change (exists ground bits, VM.find (N.of_nat 8332) result = Some (Gval ground bits)).
   exact (data_address_node_output_8332 inputs path old current result S8331 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8333 ltac:(do 0 right; left; reflexivity)) as S8333.
   apply writer_concrete_ground in S8333.
   change (exists ground bits, VM.find (N.of_nat 8334) result = Some (Gval ground bits)).
   exact (data_address_node_output_8334 inputs path old current result S8333 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8335 ltac:(do 0 right; left; reflexivity)) as S8335.
   apply writer_concrete_ground in S8335.
   change (exists ground bits, VM.find (N.of_nat 8336) result = Some (Gval ground bits)).
   exact (data_address_node_output_8336 inputs path old current result S8335 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8337 ltac:(do 0 right; left; reflexivity)) as S8337.
   apply writer_concrete_ground in S8337.
   change (exists ground bits, VM.find (N.of_nat 8338) result = Some (Gval ground bits)).
   exact (data_address_node_output_8338 inputs path old current result S8337 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8339 ltac:(do 0 right; left; reflexivity)) as S8339.
   apply writer_concrete_ground in S8339.
   change (exists ground bits, VM.find (N.of_nat 8340) result = Some (Gval ground bits)).
   exact (data_address_node_output_8340 inputs path old current result S8339 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8341 ltac:(do 0 right; left; reflexivity)) as S8341.
   apply writer_concrete_ground in S8341.
   change (exists ground bits, VM.find (N.of_nat 8342) result = Some (Gval ground bits)).
   exact (data_address_node_output_8342 inputs path old current result S8341 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8343 ltac:(do 0 right; left; reflexivity)) as S8343.
   apply writer_concrete_ground in S8343.
   change (exists ground bits, VM.find (N.of_nat 8344) result = Some (Gval ground bits)).
   exact (data_address_node_output_8344 inputs path old current result S8343 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8345 ltac:(do 0 right; left; reflexivity)) as S8345.
   apply writer_concrete_ground in S8345.
   change (exists ground bits, VM.find (N.of_nat 8346) result = Some (Gval ground bits)).
   exact (data_address_node_output_8346 inputs path old current result S8345 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8347 ltac:(do 0 right; left; reflexivity)) as S8347.
   apply writer_concrete_ground in S8347.
   change (exists ground bits, VM.find (N.of_nat 8348) result = Some (Gval ground bits)).
   exact (data_address_node_output_8348 inputs path old current result S8347 Step). }
 constructor.
Qed.
Definition data_writer_chunk_8 : list (nat * (nat * list nat)) := [::(8350,(4,[::8349]));(8352,(4,[::8351]));(8354,(4,[::8353]));(8356,(4,[::8355]));(8358,(4,[::8357]));(8360,(4,[::8359]));(886,(5,[::780;853;885]));(921,(5,[::781;853;920]));(1322,(5,[::1319;1321]));(1336,(5,[::1333;1335]));(1341,(5,[::1340]));(7763,(5,[::74]));(7764,(5,[::81]));(7815,(5,[::7809;7814]));(7818,(5,[::7813;7817]));(8410,(5,[::8360]));(8459,(5,[::8360]));(8508,(5,[::8360]));(8557,(5,[::8360]));(8704,(5,[::8360]));(8753,(5,[::8360]));(887,(6,[::780;854;886]));(922,(6,[::781;854;921]));(1323,(6,[::1322]))].
Lemma data_writer_chunk_8_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_8.
Proof.
 intros Memory Step. unfold data_writer_chunk_8.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8349 ltac:(do 0 right; left; reflexivity)) as S8349.
   apply writer_concrete_ground in S8349.
   change (exists ground bits, VM.find (N.of_nat 8350) result = Some (Gval ground bits)).
   exact (data_address_node_output_8350 inputs path old current result S8349 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8351 ltac:(do 0 right; left; reflexivity)) as S8351.
   apply writer_concrete_ground in S8351.
   change (exists ground bits, VM.find (N.of_nat 8352) result = Some (Gval ground bits)).
   exact (data_address_node_output_8352 inputs path old current result S8351 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8353 ltac:(do 0 right; left; reflexivity)) as S8353.
   apply writer_concrete_ground in S8353.
   change (exists ground bits, VM.find (N.of_nat 8354) result = Some (Gval ground bits)).
   exact (data_address_node_output_8354 inputs path old current result S8353 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8355 ltac:(do 0 right; left; reflexivity)) as S8355.
   apply writer_concrete_ground in S8355.
   change (exists ground bits, VM.find (N.of_nat 8356) result = Some (Gval ground bits)).
   exact (data_address_node_output_8356 inputs path old current result S8355 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8357 ltac:(do 0 right; left; reflexivity)) as S8357.
   apply writer_concrete_ground in S8357.
   change (exists ground bits, VM.find (N.of_nat 8358) result = Some (Gval ground bits)).
   exact (data_address_node_output_8358 inputs path old current result S8357 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8359 ltac:(do 0 right; left; reflexivity)) as S8359.
   apply writer_concrete_ground in S8359.
   change (exists ground bits, VM.find (N.of_nat 8360) result = Some (Gval ground bits)).
   exact (data_address_node_output_8360 inputs path old current result S8359 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 853 ltac:(do 1 right; left; reflexivity)) as S853.
   apply writer_concrete_ground in S853.
   pose proof (Sources 885 ltac:(do 2 right; left; reflexivity)) as S885.
   apply writer_concrete_ground in S885.
   change (exists ground bits, VM.find (N.of_nat 886) result = Some (Gval ground bits)).
   exact (data_address_node_output_886 inputs path old current result S780 S853 S885 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 853 ltac:(do 1 right; left; reflexivity)) as S853.
   apply writer_concrete_ground in S853.
   pose proof (Sources 920 ltac:(do 2 right; left; reflexivity)) as S920.
   apply writer_concrete_ground in S920.
   change (exists ground bits, VM.find (N.of_nat 921) result = Some (Gval ground bits)).
   exact (data_address_node_output_921 inputs path old current result S781 S853 S920 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1319 ltac:(do 0 right; left; reflexivity)) as S1319.
   apply writer_concrete_ground in S1319.
   pose proof (Sources 1321 ltac:(do 1 right; left; reflexivity)) as S1321.
   apply writer_concrete_ground in S1321.
   change (exists ground bits, VM.find (N.of_nat 1322) result = Some (Gval ground bits)).
   exact (data_address_node_output_1322 inputs path old current result S1319 S1321 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1333 ltac:(do 0 right; left; reflexivity)) as S1333.
   apply writer_concrete_ground in S1333.
   pose proof (Sources 1335 ltac:(do 1 right; left; reflexivity)) as S1335.
   apply writer_concrete_ground in S1335.
   change (exists ground bits, VM.find (N.of_nat 1336) result = Some (Gval ground bits)).
   exact (data_address_node_output_1336 inputs path old current result S1333 S1335 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1340 ltac:(do 0 right; left; reflexivity)) as S1340.
   apply writer_concrete_ground in S1340.
   change (exists ground bits, VM.find (N.of_nat 1341) result = Some (Gval ground bits)).
   exact (data_address_node_output_1341 inputs path old current result S1340 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 74 ltac:(do 0 right; left; reflexivity)) as S74.
   apply writer_concrete_ground in S74.
   change (exists ground bits, VM.find (N.of_nat 7763) result = Some (Gval ground bits)).
   exact (data_address_node_output_7763 inputs path old current result S74 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 81 ltac:(do 0 right; left; reflexivity)) as S81.
   apply writer_concrete_ground in S81.
   change (exists ground bits, VM.find (N.of_nat 7764) result = Some (Gval ground bits)).
   exact (data_address_node_output_7764 inputs path old current result S81 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7809 ltac:(do 0 right; left; reflexivity)) as S7809.
   apply writer_concrete_ground in S7809.
   pose proof (Sources 7814 ltac:(do 1 right; left; reflexivity)) as S7814.
   apply writer_concrete_ground in S7814.
   change (exists ground bits, VM.find (N.of_nat 7815) result = Some (Gval ground bits)).
   exact (data_address_node_output_7815 inputs path old current result S7809 S7814 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7813 ltac:(do 0 right; left; reflexivity)) as S7813.
   apply writer_concrete_ground in S7813.
   pose proof (Sources 7817 ltac:(do 1 right; left; reflexivity)) as S7817.
   apply writer_concrete_ground in S7817.
   change (exists ground bits, VM.find (N.of_nat 7818) result = Some (Gval ground bits)).
   exact (data_address_node_output_7818 inputs path old current result S7813 S7817 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8360 ltac:(do 0 right; left; reflexivity)) as S8360.
   apply writer_concrete_ground in S8360.
   change (exists ground bits, VM.find (N.of_nat 8410) result = Some (Gval ground bits)).
   exact (data_address_node_output_8410 inputs path old current result S8360 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8360 ltac:(do 0 right; left; reflexivity)) as S8360.
   apply writer_concrete_ground in S8360.
   change (exists ground bits, VM.find (N.of_nat 8459) result = Some (Gval ground bits)).
   exact (data_address_node_output_8459 inputs path old current result S8360 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8360 ltac:(do 0 right; left; reflexivity)) as S8360.
   apply writer_concrete_ground in S8360.
   change (exists ground bits, VM.find (N.of_nat 8508) result = Some (Gval ground bits)).
   exact (data_address_node_output_8508 inputs path old current result S8360 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8360 ltac:(do 0 right; left; reflexivity)) as S8360.
   apply writer_concrete_ground in S8360.
   change (exists ground bits, VM.find (N.of_nat 8557) result = Some (Gval ground bits)).
   exact (data_address_node_output_8557 inputs path old current result S8360 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8360 ltac:(do 0 right; left; reflexivity)) as S8360.
   apply writer_concrete_ground in S8360.
   change (exists ground bits, VM.find (N.of_nat 8704) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8704 inputs path old current result S8360 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8360 ltac:(do 0 right; left; reflexivity)) as S8360.
   apply writer_concrete_ground in S8360.
   change (exists ground bits, VM.find (N.of_nat 8753) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8753 inputs path old current result S8360 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 854 ltac:(do 1 right; left; reflexivity)) as S854.
   apply writer_concrete_ground in S854.
   pose proof (Sources 886 ltac:(do 2 right; left; reflexivity)) as S886.
   apply writer_concrete_ground in S886.
   change (exists ground bits, VM.find (N.of_nat 887) result = Some (Gval ground bits)).
   exact (data_address_node_output_887 inputs path old current result S780 S854 S886 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 854 ltac:(do 1 right; left; reflexivity)) as S854.
   apply writer_concrete_ground in S854.
   pose proof (Sources 921 ltac:(do 2 right; left; reflexivity)) as S921.
   apply writer_concrete_ground in S921.
   change (exists ground bits, VM.find (N.of_nat 922) result = Some (Gval ground bits)).
   exact (data_address_node_output_922 inputs path old current result S781 S854 S921 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1322 ltac:(do 0 right; left; reflexivity)) as S1322.
   apply writer_concrete_ground in S1322.
   change (exists ground bits, VM.find (N.of_nat 1323) result = Some (Gval ground bits)).
   exact (data_address_node_output_1323 inputs path old current result S1322 Step). }
 constructor.
Qed.
Definition data_writer_chunk_9 : list (nat * (nat * list nat)) := [::(1337,(6,[::1336]));(7765,(6,[::7763;7764]));(8411,(6,[::8358;8410]));(8460,(6,[::8358;8459]));(8509,(6,[::8358;8508]));(8558,(6,[::8358;8557]));(8705,(6,[::8358;8704]));(8754,(6,[::8358;8753]));(888,(7,[::780;855;887]));(923,(7,[::781;855;922]));(7832,(7,[::7765]));(8412,(7,[::8356;8411]));(8461,(7,[::8356;8460]));(8510,(7,[::8356;8509]));(8559,(7,[::8356;8558]));(8706,(7,[::8356;8705]));(8755,(7,[::8356;8754]));(889,(8,[::780;856;888]));(924,(8,[::781;856;923]));(8413,(8,[::8354;8412]));(8462,(8,[::8354;8461]));(8511,(8,[::8354;8510]));(8560,(8,[::8354;8559]));(8707,(8,[::8354;8706]))].
Lemma data_writer_chunk_9_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_9.
Proof.
 intros Memory Step. unfold data_writer_chunk_9.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1336 ltac:(do 0 right; left; reflexivity)) as S1336.
   apply writer_concrete_ground in S1336.
   change (exists ground bits, VM.find (N.of_nat 1337) result = Some (Gval ground bits)).
   exact (data_address_node_output_1337 inputs path old current result S1336 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7763 ltac:(do 0 right; left; reflexivity)) as S7763.
   apply writer_concrete_ground in S7763.
   pose proof (Sources 7764 ltac:(do 1 right; left; reflexivity)) as S7764.
   apply writer_concrete_ground in S7764.
   change (exists ground bits, VM.find (N.of_nat 7765) result = Some (Gval ground bits)).
   exact (data_address_node_output_7765 inputs path old current result S7763 S7764 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8358 ltac:(do 0 right; left; reflexivity)) as S8358.
   apply writer_concrete_ground in S8358.
   pose proof (Sources 8410 ltac:(do 1 right; left; reflexivity)) as S8410.
   apply writer_concrete_ground in S8410.
   change (exists ground bits, VM.find (N.of_nat 8411) result = Some (Gval ground bits)).
   exact (data_address_node_output_8411 inputs path old current result S8358 S8410 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8358 ltac:(do 0 right; left; reflexivity)) as S8358.
   apply writer_concrete_ground in S8358.
   pose proof (Sources 8459 ltac:(do 1 right; left; reflexivity)) as S8459.
   apply writer_concrete_ground in S8459.
   change (exists ground bits, VM.find (N.of_nat 8460) result = Some (Gval ground bits)).
   exact (data_address_node_output_8460 inputs path old current result S8358 S8459 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8358 ltac:(do 0 right; left; reflexivity)) as S8358.
   apply writer_concrete_ground in S8358.
   pose proof (Sources 8508 ltac:(do 1 right; left; reflexivity)) as S8508.
   apply writer_concrete_ground in S8508.
   change (exists ground bits, VM.find (N.of_nat 8509) result = Some (Gval ground bits)).
   exact (data_address_node_output_8509 inputs path old current result S8358 S8508 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8358 ltac:(do 0 right; left; reflexivity)) as S8358.
   apply writer_concrete_ground in S8358.
   pose proof (Sources 8557 ltac:(do 1 right; left; reflexivity)) as S8557.
   apply writer_concrete_ground in S8557.
   change (exists ground bits, VM.find (N.of_nat 8558) result = Some (Gval ground bits)).
   exact (data_address_node_output_8558 inputs path old current result S8358 S8557 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8358 ltac:(do 0 right; left; reflexivity)) as S8358.
   apply writer_concrete_ground in S8358.
   pose proof (Sources 8704 ltac:(do 1 right; left; reflexivity)) as S8704.
   apply writer_concrete_ground in S8704.
   change (exists ground bits, VM.find (N.of_nat 8705) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8705 inputs path old current result S8358 S8704 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8358 ltac:(do 0 right; left; reflexivity)) as S8358.
   apply writer_concrete_ground in S8358.
   pose proof (Sources 8753 ltac:(do 1 right; left; reflexivity)) as S8753.
   apply writer_concrete_ground in S8753.
   change (exists ground bits, VM.find (N.of_nat 8754) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8754 inputs path old current result S8358 S8753 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 855 ltac:(do 1 right; left; reflexivity)) as S855.
   apply writer_concrete_ground in S855.
   pose proof (Sources 887 ltac:(do 2 right; left; reflexivity)) as S887.
   apply writer_concrete_ground in S887.
   change (exists ground bits, VM.find (N.of_nat 888) result = Some (Gval ground bits)).
   exact (data_address_node_output_888 inputs path old current result S780 S855 S887 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 855 ltac:(do 1 right; left; reflexivity)) as S855.
   apply writer_concrete_ground in S855.
   pose proof (Sources 922 ltac:(do 2 right; left; reflexivity)) as S922.
   apply writer_concrete_ground in S922.
   change (exists ground bits, VM.find (N.of_nat 923) result = Some (Gval ground bits)).
   exact (data_address_node_output_923 inputs path old current result S781 S855 S922 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7765 ltac:(do 0 right; left; reflexivity)) as S7765.
   apply writer_concrete_ground in S7765.
   change (exists ground bits, VM.find (N.of_nat 7832) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7832 inputs path old current result S7765 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8356 ltac:(do 0 right; left; reflexivity)) as S8356.
   apply writer_concrete_ground in S8356.
   pose proof (Sources 8411 ltac:(do 1 right; left; reflexivity)) as S8411.
   apply writer_concrete_ground in S8411.
   change (exists ground bits, VM.find (N.of_nat 8412) result = Some (Gval ground bits)).
   exact (data_address_node_output_8412 inputs path old current result S8356 S8411 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8356 ltac:(do 0 right; left; reflexivity)) as S8356.
   apply writer_concrete_ground in S8356.
   pose proof (Sources 8460 ltac:(do 1 right; left; reflexivity)) as S8460.
   apply writer_concrete_ground in S8460.
   change (exists ground bits, VM.find (N.of_nat 8461) result = Some (Gval ground bits)).
   exact (data_address_node_output_8461 inputs path old current result S8356 S8460 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8356 ltac:(do 0 right; left; reflexivity)) as S8356.
   apply writer_concrete_ground in S8356.
   pose proof (Sources 8509 ltac:(do 1 right; left; reflexivity)) as S8509.
   apply writer_concrete_ground in S8509.
   change (exists ground bits, VM.find (N.of_nat 8510) result = Some (Gval ground bits)).
   exact (data_address_node_output_8510 inputs path old current result S8356 S8509 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8356 ltac:(do 0 right; left; reflexivity)) as S8356.
   apply writer_concrete_ground in S8356.
   pose proof (Sources 8558 ltac:(do 1 right; left; reflexivity)) as S8558.
   apply writer_concrete_ground in S8558.
   change (exists ground bits, VM.find (N.of_nat 8559) result = Some (Gval ground bits)).
   exact (data_address_node_output_8559 inputs path old current result S8356 S8558 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8356 ltac:(do 0 right; left; reflexivity)) as S8356.
   apply writer_concrete_ground in S8356.
   pose proof (Sources 8705 ltac:(do 1 right; left; reflexivity)) as S8705.
   apply writer_concrete_ground in S8705.
   change (exists ground bits, VM.find (N.of_nat 8706) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8706 inputs path old current result S8356 S8705 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8356 ltac:(do 0 right; left; reflexivity)) as S8356.
   apply writer_concrete_ground in S8356.
   pose proof (Sources 8754 ltac:(do 1 right; left; reflexivity)) as S8754.
   apply writer_concrete_ground in S8754.
   change (exists ground bits, VM.find (N.of_nat 8755) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8755 inputs path old current result S8356 S8754 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 856 ltac:(do 1 right; left; reflexivity)) as S856.
   apply writer_concrete_ground in S856.
   pose proof (Sources 888 ltac:(do 2 right; left; reflexivity)) as S888.
   apply writer_concrete_ground in S888.
   change (exists ground bits, VM.find (N.of_nat 889) result = Some (Gval ground bits)).
   exact (data_address_node_output_889 inputs path old current result S780 S856 S888 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 856 ltac:(do 1 right; left; reflexivity)) as S856.
   apply writer_concrete_ground in S856.
   pose proof (Sources 923 ltac:(do 2 right; left; reflexivity)) as S923.
   apply writer_concrete_ground in S923.
   change (exists ground bits, VM.find (N.of_nat 924) result = Some (Gval ground bits)).
   exact (data_address_node_output_924 inputs path old current result S781 S856 S923 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8354 ltac:(do 0 right; left; reflexivity)) as S8354.
   apply writer_concrete_ground in S8354.
   pose proof (Sources 8412 ltac:(do 1 right; left; reflexivity)) as S8412.
   apply writer_concrete_ground in S8412.
   change (exists ground bits, VM.find (N.of_nat 8413) result = Some (Gval ground bits)).
   exact (data_address_node_output_8413 inputs path old current result S8354 S8412 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8354 ltac:(do 0 right; left; reflexivity)) as S8354.
   apply writer_concrete_ground in S8354.
   pose proof (Sources 8461 ltac:(do 1 right; left; reflexivity)) as S8461.
   apply writer_concrete_ground in S8461.
   change (exists ground bits, VM.find (N.of_nat 8462) result = Some (Gval ground bits)).
   exact (data_address_node_output_8462 inputs path old current result S8354 S8461 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8354 ltac:(do 0 right; left; reflexivity)) as S8354.
   apply writer_concrete_ground in S8354.
   pose proof (Sources 8510 ltac:(do 1 right; left; reflexivity)) as S8510.
   apply writer_concrete_ground in S8510.
   change (exists ground bits, VM.find (N.of_nat 8511) result = Some (Gval ground bits)).
   exact (data_address_node_output_8511 inputs path old current result S8354 S8510 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8354 ltac:(do 0 right; left; reflexivity)) as S8354.
   apply writer_concrete_ground in S8354.
   pose proof (Sources 8559 ltac:(do 1 right; left; reflexivity)) as S8559.
   apply writer_concrete_ground in S8559.
   change (exists ground bits, VM.find (N.of_nat 8560) result = Some (Gval ground bits)).
   exact (data_address_node_output_8560 inputs path old current result S8354 S8559 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8354 ltac:(do 0 right; left; reflexivity)) as S8354.
   apply writer_concrete_ground in S8354.
   pose proof (Sources 8706 ltac:(do 1 right; left; reflexivity)) as S8706.
   apply writer_concrete_ground in S8706.
   change (exists ground bits, VM.find (N.of_nat 8707) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8707 inputs path old current result S8354 S8706 Step). }
 constructor.
Qed.
Definition data_writer_chunk_10 : list (nat * (nat * list nat)) := [::(8756,(8,[::8354;8755]));(890,(9,[::780;857;889]));(925,(9,[::781;857;924]));(8414,(9,[::8352;8413]));(8463,(9,[::8352;8462]));(8512,(9,[::8352;8511]));(8561,(9,[::8352;8560]));(8708,(9,[::8352;8707]));(8757,(9,[::8352;8756]));(891,(10,[::780;858;890]));(926,(10,[::781;858;925]));(8415,(10,[::8350;8414]));(8464,(10,[::8350;8463]));(8513,(10,[::8350;8512]));(8562,(10,[::8350;8561]));(8709,(10,[::8350;8708]));(8758,(10,[::8350;8757]));(892,(11,[::780;859;891]));(927,(11,[::781;859;926]));(8416,(11,[::8348;8415]));(8465,(11,[::8348;8464]));(8514,(11,[::8348;8513]));(8563,(11,[::8348;8562]));(8710,(11,[::8348;8709]))].
Lemma data_writer_chunk_10_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_10.
Proof.
 intros Memory Step. unfold data_writer_chunk_10.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8354 ltac:(do 0 right; left; reflexivity)) as S8354.
   apply writer_concrete_ground in S8354.
   pose proof (Sources 8755 ltac:(do 1 right; left; reflexivity)) as S8755.
   apply writer_concrete_ground in S8755.
   change (exists ground bits, VM.find (N.of_nat 8756) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8756 inputs path old current result S8354 S8755 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 857 ltac:(do 1 right; left; reflexivity)) as S857.
   apply writer_concrete_ground in S857.
   pose proof (Sources 889 ltac:(do 2 right; left; reflexivity)) as S889.
   apply writer_concrete_ground in S889.
   change (exists ground bits, VM.find (N.of_nat 890) result = Some (Gval ground bits)).
   exact (data_address_node_output_890 inputs path old current result S780 S857 S889 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 857 ltac:(do 1 right; left; reflexivity)) as S857.
   apply writer_concrete_ground in S857.
   pose proof (Sources 924 ltac:(do 2 right; left; reflexivity)) as S924.
   apply writer_concrete_ground in S924.
   change (exists ground bits, VM.find (N.of_nat 925) result = Some (Gval ground bits)).
   exact (data_address_node_output_925 inputs path old current result S781 S857 S924 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8352 ltac:(do 0 right; left; reflexivity)) as S8352.
   apply writer_concrete_ground in S8352.
   pose proof (Sources 8413 ltac:(do 1 right; left; reflexivity)) as S8413.
   apply writer_concrete_ground in S8413.
   change (exists ground bits, VM.find (N.of_nat 8414) result = Some (Gval ground bits)).
   exact (data_address_node_output_8414 inputs path old current result S8352 S8413 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8352 ltac:(do 0 right; left; reflexivity)) as S8352.
   apply writer_concrete_ground in S8352.
   pose proof (Sources 8462 ltac:(do 1 right; left; reflexivity)) as S8462.
   apply writer_concrete_ground in S8462.
   change (exists ground bits, VM.find (N.of_nat 8463) result = Some (Gval ground bits)).
   exact (data_address_node_output_8463 inputs path old current result S8352 S8462 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8352 ltac:(do 0 right; left; reflexivity)) as S8352.
   apply writer_concrete_ground in S8352.
   pose proof (Sources 8511 ltac:(do 1 right; left; reflexivity)) as S8511.
   apply writer_concrete_ground in S8511.
   change (exists ground bits, VM.find (N.of_nat 8512) result = Some (Gval ground bits)).
   exact (data_address_node_output_8512 inputs path old current result S8352 S8511 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8352 ltac:(do 0 right; left; reflexivity)) as S8352.
   apply writer_concrete_ground in S8352.
   pose proof (Sources 8560 ltac:(do 1 right; left; reflexivity)) as S8560.
   apply writer_concrete_ground in S8560.
   change (exists ground bits, VM.find (N.of_nat 8561) result = Some (Gval ground bits)).
   exact (data_address_node_output_8561 inputs path old current result S8352 S8560 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8352 ltac:(do 0 right; left; reflexivity)) as S8352.
   apply writer_concrete_ground in S8352.
   pose proof (Sources 8707 ltac:(do 1 right; left; reflexivity)) as S8707.
   apply writer_concrete_ground in S8707.
   change (exists ground bits, VM.find (N.of_nat 8708) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8708 inputs path old current result S8352 S8707 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8352 ltac:(do 0 right; left; reflexivity)) as S8352.
   apply writer_concrete_ground in S8352.
   pose proof (Sources 8756 ltac:(do 1 right; left; reflexivity)) as S8756.
   apply writer_concrete_ground in S8756.
   change (exists ground bits, VM.find (N.of_nat 8757) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8757 inputs path old current result S8352 S8756 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 858 ltac:(do 1 right; left; reflexivity)) as S858.
   apply writer_concrete_ground in S858.
   pose proof (Sources 890 ltac:(do 2 right; left; reflexivity)) as S890.
   apply writer_concrete_ground in S890.
   change (exists ground bits, VM.find (N.of_nat 891) result = Some (Gval ground bits)).
   exact (data_address_node_output_891 inputs path old current result S780 S858 S890 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 858 ltac:(do 1 right; left; reflexivity)) as S858.
   apply writer_concrete_ground in S858.
   pose proof (Sources 925 ltac:(do 2 right; left; reflexivity)) as S925.
   apply writer_concrete_ground in S925.
   change (exists ground bits, VM.find (N.of_nat 926) result = Some (Gval ground bits)).
   exact (data_address_node_output_926 inputs path old current result S781 S858 S925 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8350 ltac:(do 0 right; left; reflexivity)) as S8350.
   apply writer_concrete_ground in S8350.
   pose proof (Sources 8414 ltac:(do 1 right; left; reflexivity)) as S8414.
   apply writer_concrete_ground in S8414.
   change (exists ground bits, VM.find (N.of_nat 8415) result = Some (Gval ground bits)).
   exact (data_address_node_output_8415 inputs path old current result S8350 S8414 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8350 ltac:(do 0 right; left; reflexivity)) as S8350.
   apply writer_concrete_ground in S8350.
   pose proof (Sources 8463 ltac:(do 1 right; left; reflexivity)) as S8463.
   apply writer_concrete_ground in S8463.
   change (exists ground bits, VM.find (N.of_nat 8464) result = Some (Gval ground bits)).
   exact (data_address_node_output_8464 inputs path old current result S8350 S8463 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8350 ltac:(do 0 right; left; reflexivity)) as S8350.
   apply writer_concrete_ground in S8350.
   pose proof (Sources 8512 ltac:(do 1 right; left; reflexivity)) as S8512.
   apply writer_concrete_ground in S8512.
   change (exists ground bits, VM.find (N.of_nat 8513) result = Some (Gval ground bits)).
   exact (data_address_node_output_8513 inputs path old current result S8350 S8512 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8350 ltac:(do 0 right; left; reflexivity)) as S8350.
   apply writer_concrete_ground in S8350.
   pose proof (Sources 8561 ltac:(do 1 right; left; reflexivity)) as S8561.
   apply writer_concrete_ground in S8561.
   change (exists ground bits, VM.find (N.of_nat 8562) result = Some (Gval ground bits)).
   exact (data_address_node_output_8562 inputs path old current result S8350 S8561 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8350 ltac:(do 0 right; left; reflexivity)) as S8350.
   apply writer_concrete_ground in S8350.
   pose proof (Sources 8708 ltac:(do 1 right; left; reflexivity)) as S8708.
   apply writer_concrete_ground in S8708.
   change (exists ground bits, VM.find (N.of_nat 8709) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8709 inputs path old current result S8350 S8708 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8350 ltac:(do 0 right; left; reflexivity)) as S8350.
   apply writer_concrete_ground in S8350.
   pose proof (Sources 8757 ltac:(do 1 right; left; reflexivity)) as S8757.
   apply writer_concrete_ground in S8757.
   change (exists ground bits, VM.find (N.of_nat 8758) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8758 inputs path old current result S8350 S8757 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 859 ltac:(do 1 right; left; reflexivity)) as S859.
   apply writer_concrete_ground in S859.
   pose proof (Sources 891 ltac:(do 2 right; left; reflexivity)) as S891.
   apply writer_concrete_ground in S891.
   change (exists ground bits, VM.find (N.of_nat 892) result = Some (Gval ground bits)).
   exact (data_address_node_output_892 inputs path old current result S780 S859 S891 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 859 ltac:(do 1 right; left; reflexivity)) as S859.
   apply writer_concrete_ground in S859.
   pose proof (Sources 926 ltac:(do 2 right; left; reflexivity)) as S926.
   apply writer_concrete_ground in S926.
   change (exists ground bits, VM.find (N.of_nat 927) result = Some (Gval ground bits)).
   exact (data_address_node_output_927 inputs path old current result S781 S859 S926 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8348 ltac:(do 0 right; left; reflexivity)) as S8348.
   apply writer_concrete_ground in S8348.
   pose proof (Sources 8415 ltac:(do 1 right; left; reflexivity)) as S8415.
   apply writer_concrete_ground in S8415.
   change (exists ground bits, VM.find (N.of_nat 8416) result = Some (Gval ground bits)).
   exact (data_address_node_output_8416 inputs path old current result S8348 S8415 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8348 ltac:(do 0 right; left; reflexivity)) as S8348.
   apply writer_concrete_ground in S8348.
   pose proof (Sources 8464 ltac:(do 1 right; left; reflexivity)) as S8464.
   apply writer_concrete_ground in S8464.
   change (exists ground bits, VM.find (N.of_nat 8465) result = Some (Gval ground bits)).
   exact (data_address_node_output_8465 inputs path old current result S8348 S8464 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8348 ltac:(do 0 right; left; reflexivity)) as S8348.
   apply writer_concrete_ground in S8348.
   pose proof (Sources 8513 ltac:(do 1 right; left; reflexivity)) as S8513.
   apply writer_concrete_ground in S8513.
   change (exists ground bits, VM.find (N.of_nat 8514) result = Some (Gval ground bits)).
   exact (data_address_node_output_8514 inputs path old current result S8348 S8513 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8348 ltac:(do 0 right; left; reflexivity)) as S8348.
   apply writer_concrete_ground in S8348.
   pose proof (Sources 8562 ltac:(do 1 right; left; reflexivity)) as S8562.
   apply writer_concrete_ground in S8562.
   change (exists ground bits, VM.find (N.of_nat 8563) result = Some (Gval ground bits)).
   exact (data_address_node_output_8563 inputs path old current result S8348 S8562 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8348 ltac:(do 0 right; left; reflexivity)) as S8348.
   apply writer_concrete_ground in S8348.
   pose proof (Sources 8709 ltac:(do 1 right; left; reflexivity)) as S8709.
   apply writer_concrete_ground in S8709.
   change (exists ground bits, VM.find (N.of_nat 8710) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8710 inputs path old current result S8348 S8709 Step). }
 constructor.
Qed.
Definition data_writer_chunk_11 : list (nat * (nat * list nat)) := [::(8759,(11,[::8348;8758]));(893,(12,[::780;860;892]));(928,(12,[::781;860;927]));(8417,(12,[::8346;8416]));(8466,(12,[::8346;8465]));(8515,(12,[::8346;8514]));(8564,(12,[::8346;8563]));(8711,(12,[::8346;8710]));(8760,(12,[::8346;8759]));(894,(13,[::780;861;893]));(929,(13,[::781;861;928]));(8418,(13,[::8344;8417]));(8467,(13,[::8344;8466]));(8516,(13,[::8344;8515]));(8565,(13,[::8344;8564]));(8712,(13,[::8344;8711]));(8761,(13,[::8344;8760]));(895,(14,[::780;862;894]));(930,(14,[::781;862;929]));(8419,(14,[::8342;8418]));(8468,(14,[::8342;8467]));(8517,(14,[::8342;8516]));(8566,(14,[::8342;8565]));(8713,(14,[::8342;8712]))].
Lemma data_writer_chunk_11_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_11.
Proof.
 intros Memory Step. unfold data_writer_chunk_11.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8348 ltac:(do 0 right; left; reflexivity)) as S8348.
   apply writer_concrete_ground in S8348.
   pose proof (Sources 8758 ltac:(do 1 right; left; reflexivity)) as S8758.
   apply writer_concrete_ground in S8758.
   change (exists ground bits, VM.find (N.of_nat 8759) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8759 inputs path old current result S8348 S8758 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 860 ltac:(do 1 right; left; reflexivity)) as S860.
   apply writer_concrete_ground in S860.
   pose proof (Sources 892 ltac:(do 2 right; left; reflexivity)) as S892.
   apply writer_concrete_ground in S892.
   change (exists ground bits, VM.find (N.of_nat 893) result = Some (Gval ground bits)).
   exact (data_address_node_output_893 inputs path old current result S780 S860 S892 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 860 ltac:(do 1 right; left; reflexivity)) as S860.
   apply writer_concrete_ground in S860.
   pose proof (Sources 927 ltac:(do 2 right; left; reflexivity)) as S927.
   apply writer_concrete_ground in S927.
   change (exists ground bits, VM.find (N.of_nat 928) result = Some (Gval ground bits)).
   exact (data_address_node_output_928 inputs path old current result S781 S860 S927 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8346 ltac:(do 0 right; left; reflexivity)) as S8346.
   apply writer_concrete_ground in S8346.
   pose proof (Sources 8416 ltac:(do 1 right; left; reflexivity)) as S8416.
   apply writer_concrete_ground in S8416.
   change (exists ground bits, VM.find (N.of_nat 8417) result = Some (Gval ground bits)).
   exact (data_address_node_output_8417 inputs path old current result S8346 S8416 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8346 ltac:(do 0 right; left; reflexivity)) as S8346.
   apply writer_concrete_ground in S8346.
   pose proof (Sources 8465 ltac:(do 1 right; left; reflexivity)) as S8465.
   apply writer_concrete_ground in S8465.
   change (exists ground bits, VM.find (N.of_nat 8466) result = Some (Gval ground bits)).
   exact (data_address_node_output_8466 inputs path old current result S8346 S8465 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8346 ltac:(do 0 right; left; reflexivity)) as S8346.
   apply writer_concrete_ground in S8346.
   pose proof (Sources 8514 ltac:(do 1 right; left; reflexivity)) as S8514.
   apply writer_concrete_ground in S8514.
   change (exists ground bits, VM.find (N.of_nat 8515) result = Some (Gval ground bits)).
   exact (data_address_node_output_8515 inputs path old current result S8346 S8514 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8346 ltac:(do 0 right; left; reflexivity)) as S8346.
   apply writer_concrete_ground in S8346.
   pose proof (Sources 8563 ltac:(do 1 right; left; reflexivity)) as S8563.
   apply writer_concrete_ground in S8563.
   change (exists ground bits, VM.find (N.of_nat 8564) result = Some (Gval ground bits)).
   exact (data_address_node_output_8564 inputs path old current result S8346 S8563 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8346 ltac:(do 0 right; left; reflexivity)) as S8346.
   apply writer_concrete_ground in S8346.
   pose proof (Sources 8710 ltac:(do 1 right; left; reflexivity)) as S8710.
   apply writer_concrete_ground in S8710.
   change (exists ground bits, VM.find (N.of_nat 8711) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8711 inputs path old current result S8346 S8710 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8346 ltac:(do 0 right; left; reflexivity)) as S8346.
   apply writer_concrete_ground in S8346.
   pose proof (Sources 8759 ltac:(do 1 right; left; reflexivity)) as S8759.
   apply writer_concrete_ground in S8759.
   change (exists ground bits, VM.find (N.of_nat 8760) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8760 inputs path old current result S8346 S8759 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 861 ltac:(do 1 right; left; reflexivity)) as S861.
   apply writer_concrete_ground in S861.
   pose proof (Sources 893 ltac:(do 2 right; left; reflexivity)) as S893.
   apply writer_concrete_ground in S893.
   change (exists ground bits, VM.find (N.of_nat 894) result = Some (Gval ground bits)).
   exact (data_address_node_output_894 inputs path old current result S780 S861 S893 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 861 ltac:(do 1 right; left; reflexivity)) as S861.
   apply writer_concrete_ground in S861.
   pose proof (Sources 928 ltac:(do 2 right; left; reflexivity)) as S928.
   apply writer_concrete_ground in S928.
   change (exists ground bits, VM.find (N.of_nat 929) result = Some (Gval ground bits)).
   exact (data_address_node_output_929 inputs path old current result S781 S861 S928 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8344 ltac:(do 0 right; left; reflexivity)) as S8344.
   apply writer_concrete_ground in S8344.
   pose proof (Sources 8417 ltac:(do 1 right; left; reflexivity)) as S8417.
   apply writer_concrete_ground in S8417.
   change (exists ground bits, VM.find (N.of_nat 8418) result = Some (Gval ground bits)).
   exact (data_address_node_output_8418 inputs path old current result S8344 S8417 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8344 ltac:(do 0 right; left; reflexivity)) as S8344.
   apply writer_concrete_ground in S8344.
   pose proof (Sources 8466 ltac:(do 1 right; left; reflexivity)) as S8466.
   apply writer_concrete_ground in S8466.
   change (exists ground bits, VM.find (N.of_nat 8467) result = Some (Gval ground bits)).
   exact (data_address_node_output_8467 inputs path old current result S8344 S8466 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8344 ltac:(do 0 right; left; reflexivity)) as S8344.
   apply writer_concrete_ground in S8344.
   pose proof (Sources 8515 ltac:(do 1 right; left; reflexivity)) as S8515.
   apply writer_concrete_ground in S8515.
   change (exists ground bits, VM.find (N.of_nat 8516) result = Some (Gval ground bits)).
   exact (data_address_node_output_8516 inputs path old current result S8344 S8515 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8344 ltac:(do 0 right; left; reflexivity)) as S8344.
   apply writer_concrete_ground in S8344.
   pose proof (Sources 8564 ltac:(do 1 right; left; reflexivity)) as S8564.
   apply writer_concrete_ground in S8564.
   change (exists ground bits, VM.find (N.of_nat 8565) result = Some (Gval ground bits)).
   exact (data_address_node_output_8565 inputs path old current result S8344 S8564 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8344 ltac:(do 0 right; left; reflexivity)) as S8344.
   apply writer_concrete_ground in S8344.
   pose proof (Sources 8711 ltac:(do 1 right; left; reflexivity)) as S8711.
   apply writer_concrete_ground in S8711.
   change (exists ground bits, VM.find (N.of_nat 8712) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8712 inputs path old current result S8344 S8711 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8344 ltac:(do 0 right; left; reflexivity)) as S8344.
   apply writer_concrete_ground in S8344.
   pose proof (Sources 8760 ltac:(do 1 right; left; reflexivity)) as S8760.
   apply writer_concrete_ground in S8760.
   change (exists ground bits, VM.find (N.of_nat 8761) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8761 inputs path old current result S8344 S8760 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 862 ltac:(do 1 right; left; reflexivity)) as S862.
   apply writer_concrete_ground in S862.
   pose proof (Sources 894 ltac:(do 2 right; left; reflexivity)) as S894.
   apply writer_concrete_ground in S894.
   change (exists ground bits, VM.find (N.of_nat 895) result = Some (Gval ground bits)).
   exact (data_address_node_output_895 inputs path old current result S780 S862 S894 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 862 ltac:(do 1 right; left; reflexivity)) as S862.
   apply writer_concrete_ground in S862.
   pose proof (Sources 929 ltac:(do 2 right; left; reflexivity)) as S929.
   apply writer_concrete_ground in S929.
   change (exists ground bits, VM.find (N.of_nat 930) result = Some (Gval ground bits)).
   exact (data_address_node_output_930 inputs path old current result S781 S862 S929 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8342 ltac:(do 0 right; left; reflexivity)) as S8342.
   apply writer_concrete_ground in S8342.
   pose proof (Sources 8418 ltac:(do 1 right; left; reflexivity)) as S8418.
   apply writer_concrete_ground in S8418.
   change (exists ground bits, VM.find (N.of_nat 8419) result = Some (Gval ground bits)).
   exact (data_address_node_output_8419 inputs path old current result S8342 S8418 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8342 ltac:(do 0 right; left; reflexivity)) as S8342.
   apply writer_concrete_ground in S8342.
   pose proof (Sources 8467 ltac:(do 1 right; left; reflexivity)) as S8467.
   apply writer_concrete_ground in S8467.
   change (exists ground bits, VM.find (N.of_nat 8468) result = Some (Gval ground bits)).
   exact (data_address_node_output_8468 inputs path old current result S8342 S8467 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8342 ltac:(do 0 right; left; reflexivity)) as S8342.
   apply writer_concrete_ground in S8342.
   pose proof (Sources 8516 ltac:(do 1 right; left; reflexivity)) as S8516.
   apply writer_concrete_ground in S8516.
   change (exists ground bits, VM.find (N.of_nat 8517) result = Some (Gval ground bits)).
   exact (data_address_node_output_8517 inputs path old current result S8342 S8516 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8342 ltac:(do 0 right; left; reflexivity)) as S8342.
   apply writer_concrete_ground in S8342.
   pose proof (Sources 8565 ltac:(do 1 right; left; reflexivity)) as S8565.
   apply writer_concrete_ground in S8565.
   change (exists ground bits, VM.find (N.of_nat 8566) result = Some (Gval ground bits)).
   exact (data_address_node_output_8566 inputs path old current result S8342 S8565 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8342 ltac:(do 0 right; left; reflexivity)) as S8342.
   apply writer_concrete_ground in S8342.
   pose proof (Sources 8712 ltac:(do 1 right; left; reflexivity)) as S8712.
   apply writer_concrete_ground in S8712.
   change (exists ground bits, VM.find (N.of_nat 8713) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8713 inputs path old current result S8342 S8712 Step). }
 constructor.
Qed.
Definition data_writer_chunk_12 : list (nat * (nat * list nat)) := [::(8762,(14,[::8342;8761]));(896,(15,[::780;863;895]));(931,(15,[::781;863;930]));(8420,(15,[::8340;8419]));(8469,(15,[::8340;8468]));(8518,(15,[::8340;8517]));(8567,(15,[::8340;8566]));(8714,(15,[::8340;8713]));(8763,(15,[::8340;8762]));(897,(16,[::780;864;896]));(932,(16,[::781;864;931]));(8421,(16,[::8338;8420]));(8470,(16,[::8338;8469]));(8519,(16,[::8338;8518]));(8568,(16,[::8338;8567]));(8715,(16,[::8338;8714]));(8764,(16,[::8338;8763]));(898,(17,[::780;865;897]));(933,(17,[::781;865;932]));(8422,(17,[::8336;8421]));(8471,(17,[::8336;8470]));(8520,(17,[::8336;8519]));(8569,(17,[::8336;8568]));(8716,(17,[::8336;8715]))].
Lemma data_writer_chunk_12_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_12.
Proof.
 intros Memory Step. unfold data_writer_chunk_12.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8342 ltac:(do 0 right; left; reflexivity)) as S8342.
   apply writer_concrete_ground in S8342.
   pose proof (Sources 8761 ltac:(do 1 right; left; reflexivity)) as S8761.
   apply writer_concrete_ground in S8761.
   change (exists ground bits, VM.find (N.of_nat 8762) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8762 inputs path old current result S8342 S8761 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 863 ltac:(do 1 right; left; reflexivity)) as S863.
   apply writer_concrete_ground in S863.
   pose proof (Sources 895 ltac:(do 2 right; left; reflexivity)) as S895.
   apply writer_concrete_ground in S895.
   change (exists ground bits, VM.find (N.of_nat 896) result = Some (Gval ground bits)).
   exact (data_address_node_output_896 inputs path old current result S780 S863 S895 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 863 ltac:(do 1 right; left; reflexivity)) as S863.
   apply writer_concrete_ground in S863.
   pose proof (Sources 930 ltac:(do 2 right; left; reflexivity)) as S930.
   apply writer_concrete_ground in S930.
   change (exists ground bits, VM.find (N.of_nat 931) result = Some (Gval ground bits)).
   exact (data_address_node_output_931 inputs path old current result S781 S863 S930 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8340 ltac:(do 0 right; left; reflexivity)) as S8340.
   apply writer_concrete_ground in S8340.
   pose proof (Sources 8419 ltac:(do 1 right; left; reflexivity)) as S8419.
   apply writer_concrete_ground in S8419.
   change (exists ground bits, VM.find (N.of_nat 8420) result = Some (Gval ground bits)).
   exact (data_address_node_output_8420 inputs path old current result S8340 S8419 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8340 ltac:(do 0 right; left; reflexivity)) as S8340.
   apply writer_concrete_ground in S8340.
   pose proof (Sources 8468 ltac:(do 1 right; left; reflexivity)) as S8468.
   apply writer_concrete_ground in S8468.
   change (exists ground bits, VM.find (N.of_nat 8469) result = Some (Gval ground bits)).
   exact (data_address_node_output_8469 inputs path old current result S8340 S8468 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8340 ltac:(do 0 right; left; reflexivity)) as S8340.
   apply writer_concrete_ground in S8340.
   pose proof (Sources 8517 ltac:(do 1 right; left; reflexivity)) as S8517.
   apply writer_concrete_ground in S8517.
   change (exists ground bits, VM.find (N.of_nat 8518) result = Some (Gval ground bits)).
   exact (data_address_node_output_8518 inputs path old current result S8340 S8517 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8340 ltac:(do 0 right; left; reflexivity)) as S8340.
   apply writer_concrete_ground in S8340.
   pose proof (Sources 8566 ltac:(do 1 right; left; reflexivity)) as S8566.
   apply writer_concrete_ground in S8566.
   change (exists ground bits, VM.find (N.of_nat 8567) result = Some (Gval ground bits)).
   exact (data_address_node_output_8567 inputs path old current result S8340 S8566 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8340 ltac:(do 0 right; left; reflexivity)) as S8340.
   apply writer_concrete_ground in S8340.
   pose proof (Sources 8713 ltac:(do 1 right; left; reflexivity)) as S8713.
   apply writer_concrete_ground in S8713.
   change (exists ground bits, VM.find (N.of_nat 8714) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8714 inputs path old current result S8340 S8713 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8340 ltac:(do 0 right; left; reflexivity)) as S8340.
   apply writer_concrete_ground in S8340.
   pose proof (Sources 8762 ltac:(do 1 right; left; reflexivity)) as S8762.
   apply writer_concrete_ground in S8762.
   change (exists ground bits, VM.find (N.of_nat 8763) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8763 inputs path old current result S8340 S8762 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 864 ltac:(do 1 right; left; reflexivity)) as S864.
   apply writer_concrete_ground in S864.
   pose proof (Sources 896 ltac:(do 2 right; left; reflexivity)) as S896.
   apply writer_concrete_ground in S896.
   change (exists ground bits, VM.find (N.of_nat 897) result = Some (Gval ground bits)).
   exact (data_address_node_output_897 inputs path old current result S780 S864 S896 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 864 ltac:(do 1 right; left; reflexivity)) as S864.
   apply writer_concrete_ground in S864.
   pose proof (Sources 931 ltac:(do 2 right; left; reflexivity)) as S931.
   apply writer_concrete_ground in S931.
   change (exists ground bits, VM.find (N.of_nat 932) result = Some (Gval ground bits)).
   exact (data_address_node_output_932 inputs path old current result S781 S864 S931 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8338 ltac:(do 0 right; left; reflexivity)) as S8338.
   apply writer_concrete_ground in S8338.
   pose proof (Sources 8420 ltac:(do 1 right; left; reflexivity)) as S8420.
   apply writer_concrete_ground in S8420.
   change (exists ground bits, VM.find (N.of_nat 8421) result = Some (Gval ground bits)).
   exact (data_address_node_output_8421 inputs path old current result S8338 S8420 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8338 ltac:(do 0 right; left; reflexivity)) as S8338.
   apply writer_concrete_ground in S8338.
   pose proof (Sources 8469 ltac:(do 1 right; left; reflexivity)) as S8469.
   apply writer_concrete_ground in S8469.
   change (exists ground bits, VM.find (N.of_nat 8470) result = Some (Gval ground bits)).
   exact (data_address_node_output_8470 inputs path old current result S8338 S8469 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8338 ltac:(do 0 right; left; reflexivity)) as S8338.
   apply writer_concrete_ground in S8338.
   pose proof (Sources 8518 ltac:(do 1 right; left; reflexivity)) as S8518.
   apply writer_concrete_ground in S8518.
   change (exists ground bits, VM.find (N.of_nat 8519) result = Some (Gval ground bits)).
   exact (data_address_node_output_8519 inputs path old current result S8338 S8518 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8338 ltac:(do 0 right; left; reflexivity)) as S8338.
   apply writer_concrete_ground in S8338.
   pose proof (Sources 8567 ltac:(do 1 right; left; reflexivity)) as S8567.
   apply writer_concrete_ground in S8567.
   change (exists ground bits, VM.find (N.of_nat 8568) result = Some (Gval ground bits)).
   exact (data_address_node_output_8568 inputs path old current result S8338 S8567 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8338 ltac:(do 0 right; left; reflexivity)) as S8338.
   apply writer_concrete_ground in S8338.
   pose proof (Sources 8714 ltac:(do 1 right; left; reflexivity)) as S8714.
   apply writer_concrete_ground in S8714.
   change (exists ground bits, VM.find (N.of_nat 8715) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8715 inputs path old current result S8338 S8714 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8338 ltac:(do 0 right; left; reflexivity)) as S8338.
   apply writer_concrete_ground in S8338.
   pose proof (Sources 8763 ltac:(do 1 right; left; reflexivity)) as S8763.
   apply writer_concrete_ground in S8763.
   change (exists ground bits, VM.find (N.of_nat 8764) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8764 inputs path old current result S8338 S8763 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 865 ltac:(do 1 right; left; reflexivity)) as S865.
   apply writer_concrete_ground in S865.
   pose proof (Sources 897 ltac:(do 2 right; left; reflexivity)) as S897.
   apply writer_concrete_ground in S897.
   change (exists ground bits, VM.find (N.of_nat 898) result = Some (Gval ground bits)).
   exact (data_address_node_output_898 inputs path old current result S780 S865 S897 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 865 ltac:(do 1 right; left; reflexivity)) as S865.
   apply writer_concrete_ground in S865.
   pose proof (Sources 932 ltac:(do 2 right; left; reflexivity)) as S932.
   apply writer_concrete_ground in S932.
   change (exists ground bits, VM.find (N.of_nat 933) result = Some (Gval ground bits)).
   exact (data_address_node_output_933 inputs path old current result S781 S865 S932 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8336 ltac:(do 0 right; left; reflexivity)) as S8336.
   apply writer_concrete_ground in S8336.
   pose proof (Sources 8421 ltac:(do 1 right; left; reflexivity)) as S8421.
   apply writer_concrete_ground in S8421.
   change (exists ground bits, VM.find (N.of_nat 8422) result = Some (Gval ground bits)).
   exact (data_address_node_output_8422 inputs path old current result S8336 S8421 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8336 ltac:(do 0 right; left; reflexivity)) as S8336.
   apply writer_concrete_ground in S8336.
   pose proof (Sources 8470 ltac:(do 1 right; left; reflexivity)) as S8470.
   apply writer_concrete_ground in S8470.
   change (exists ground bits, VM.find (N.of_nat 8471) result = Some (Gval ground bits)).
   exact (data_address_node_output_8471 inputs path old current result S8336 S8470 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8336 ltac:(do 0 right; left; reflexivity)) as S8336.
   apply writer_concrete_ground in S8336.
   pose proof (Sources 8519 ltac:(do 1 right; left; reflexivity)) as S8519.
   apply writer_concrete_ground in S8519.
   change (exists ground bits, VM.find (N.of_nat 8520) result = Some (Gval ground bits)).
   exact (data_address_node_output_8520 inputs path old current result S8336 S8519 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8336 ltac:(do 0 right; left; reflexivity)) as S8336.
   apply writer_concrete_ground in S8336.
   pose proof (Sources 8568 ltac:(do 1 right; left; reflexivity)) as S8568.
   apply writer_concrete_ground in S8568.
   change (exists ground bits, VM.find (N.of_nat 8569) result = Some (Gval ground bits)).
   exact (data_address_node_output_8569 inputs path old current result S8336 S8568 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8336 ltac:(do 0 right; left; reflexivity)) as S8336.
   apply writer_concrete_ground in S8336.
   pose proof (Sources 8715 ltac:(do 1 right; left; reflexivity)) as S8715.
   apply writer_concrete_ground in S8715.
   change (exists ground bits, VM.find (N.of_nat 8716) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8716 inputs path old current result S8336 S8715 Step). }
 constructor.
Qed.
Definition data_writer_chunk_13 : list (nat * (nat * list nat)) := [::(8765,(17,[::8336;8764]));(899,(18,[::780;866;898]));(934,(18,[::781;866;933]));(8423,(18,[::8334;8422]));(8472,(18,[::8334;8471]));(8521,(18,[::8334;8520]));(8570,(18,[::8334;8569]));(8717,(18,[::8334;8716]));(8766,(18,[::8334;8765]));(900,(19,[::780;867;899]));(935,(19,[::781;867;934]));(8424,(19,[::8332;8423]));(8473,(19,[::8332;8472]));(8522,(19,[::8332;8521]));(8571,(19,[::8332;8570]));(8718,(19,[::8332;8717]));(8767,(19,[::8332;8766]));(901,(20,[::780;868;900]));(936,(20,[::781;868;935]));(8425,(20,[::8330;8424]));(8474,(20,[::8330;8473]));(8523,(20,[::8330;8522]));(8572,(20,[::8330;8571]));(8719,(20,[::8330;8718]))].
Lemma data_writer_chunk_13_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_13.
Proof.
 intros Memory Step. unfold data_writer_chunk_13.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8336 ltac:(do 0 right; left; reflexivity)) as S8336.
   apply writer_concrete_ground in S8336.
   pose proof (Sources 8764 ltac:(do 1 right; left; reflexivity)) as S8764.
   apply writer_concrete_ground in S8764.
   change (exists ground bits, VM.find (N.of_nat 8765) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8765 inputs path old current result S8336 S8764 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 866 ltac:(do 1 right; left; reflexivity)) as S866.
   apply writer_concrete_ground in S866.
   pose proof (Sources 898 ltac:(do 2 right; left; reflexivity)) as S898.
   apply writer_concrete_ground in S898.
   change (exists ground bits, VM.find (N.of_nat 899) result = Some (Gval ground bits)).
   exact (data_address_node_output_899 inputs path old current result S780 S866 S898 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 866 ltac:(do 1 right; left; reflexivity)) as S866.
   apply writer_concrete_ground in S866.
   pose proof (Sources 933 ltac:(do 2 right; left; reflexivity)) as S933.
   apply writer_concrete_ground in S933.
   change (exists ground bits, VM.find (N.of_nat 934) result = Some (Gval ground bits)).
   exact (data_address_node_output_934 inputs path old current result S781 S866 S933 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8334 ltac:(do 0 right; left; reflexivity)) as S8334.
   apply writer_concrete_ground in S8334.
   pose proof (Sources 8422 ltac:(do 1 right; left; reflexivity)) as S8422.
   apply writer_concrete_ground in S8422.
   change (exists ground bits, VM.find (N.of_nat 8423) result = Some (Gval ground bits)).
   exact (data_address_node_output_8423 inputs path old current result S8334 S8422 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8334 ltac:(do 0 right; left; reflexivity)) as S8334.
   apply writer_concrete_ground in S8334.
   pose proof (Sources 8471 ltac:(do 1 right; left; reflexivity)) as S8471.
   apply writer_concrete_ground in S8471.
   change (exists ground bits, VM.find (N.of_nat 8472) result = Some (Gval ground bits)).
   exact (data_address_node_output_8472 inputs path old current result S8334 S8471 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8334 ltac:(do 0 right; left; reflexivity)) as S8334.
   apply writer_concrete_ground in S8334.
   pose proof (Sources 8520 ltac:(do 1 right; left; reflexivity)) as S8520.
   apply writer_concrete_ground in S8520.
   change (exists ground bits, VM.find (N.of_nat 8521) result = Some (Gval ground bits)).
   exact (data_address_node_output_8521 inputs path old current result S8334 S8520 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8334 ltac:(do 0 right; left; reflexivity)) as S8334.
   apply writer_concrete_ground in S8334.
   pose proof (Sources 8569 ltac:(do 1 right; left; reflexivity)) as S8569.
   apply writer_concrete_ground in S8569.
   change (exists ground bits, VM.find (N.of_nat 8570) result = Some (Gval ground bits)).
   exact (data_address_node_output_8570 inputs path old current result S8334 S8569 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8334 ltac:(do 0 right; left; reflexivity)) as S8334.
   apply writer_concrete_ground in S8334.
   pose proof (Sources 8716 ltac:(do 1 right; left; reflexivity)) as S8716.
   apply writer_concrete_ground in S8716.
   change (exists ground bits, VM.find (N.of_nat 8717) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8717 inputs path old current result S8334 S8716 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8334 ltac:(do 0 right; left; reflexivity)) as S8334.
   apply writer_concrete_ground in S8334.
   pose proof (Sources 8765 ltac:(do 1 right; left; reflexivity)) as S8765.
   apply writer_concrete_ground in S8765.
   change (exists ground bits, VM.find (N.of_nat 8766) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8766 inputs path old current result S8334 S8765 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 867 ltac:(do 1 right; left; reflexivity)) as S867.
   apply writer_concrete_ground in S867.
   pose proof (Sources 899 ltac:(do 2 right; left; reflexivity)) as S899.
   apply writer_concrete_ground in S899.
   change (exists ground bits, VM.find (N.of_nat 900) result = Some (Gval ground bits)).
   exact (data_address_node_output_900 inputs path old current result S780 S867 S899 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 867 ltac:(do 1 right; left; reflexivity)) as S867.
   apply writer_concrete_ground in S867.
   pose proof (Sources 934 ltac:(do 2 right; left; reflexivity)) as S934.
   apply writer_concrete_ground in S934.
   change (exists ground bits, VM.find (N.of_nat 935) result = Some (Gval ground bits)).
   exact (data_address_node_output_935 inputs path old current result S781 S867 S934 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8332 ltac:(do 0 right; left; reflexivity)) as S8332.
   apply writer_concrete_ground in S8332.
   pose proof (Sources 8423 ltac:(do 1 right; left; reflexivity)) as S8423.
   apply writer_concrete_ground in S8423.
   change (exists ground bits, VM.find (N.of_nat 8424) result = Some (Gval ground bits)).
   exact (data_address_node_output_8424 inputs path old current result S8332 S8423 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8332 ltac:(do 0 right; left; reflexivity)) as S8332.
   apply writer_concrete_ground in S8332.
   pose proof (Sources 8472 ltac:(do 1 right; left; reflexivity)) as S8472.
   apply writer_concrete_ground in S8472.
   change (exists ground bits, VM.find (N.of_nat 8473) result = Some (Gval ground bits)).
   exact (data_address_node_output_8473 inputs path old current result S8332 S8472 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8332 ltac:(do 0 right; left; reflexivity)) as S8332.
   apply writer_concrete_ground in S8332.
   pose proof (Sources 8521 ltac:(do 1 right; left; reflexivity)) as S8521.
   apply writer_concrete_ground in S8521.
   change (exists ground bits, VM.find (N.of_nat 8522) result = Some (Gval ground bits)).
   exact (data_address_node_output_8522 inputs path old current result S8332 S8521 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8332 ltac:(do 0 right; left; reflexivity)) as S8332.
   apply writer_concrete_ground in S8332.
   pose proof (Sources 8570 ltac:(do 1 right; left; reflexivity)) as S8570.
   apply writer_concrete_ground in S8570.
   change (exists ground bits, VM.find (N.of_nat 8571) result = Some (Gval ground bits)).
   exact (data_address_node_output_8571 inputs path old current result S8332 S8570 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8332 ltac:(do 0 right; left; reflexivity)) as S8332.
   apply writer_concrete_ground in S8332.
   pose proof (Sources 8717 ltac:(do 1 right; left; reflexivity)) as S8717.
   apply writer_concrete_ground in S8717.
   change (exists ground bits, VM.find (N.of_nat 8718) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8718 inputs path old current result S8332 S8717 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8332 ltac:(do 0 right; left; reflexivity)) as S8332.
   apply writer_concrete_ground in S8332.
   pose proof (Sources 8766 ltac:(do 1 right; left; reflexivity)) as S8766.
   apply writer_concrete_ground in S8766.
   change (exists ground bits, VM.find (N.of_nat 8767) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8767 inputs path old current result S8332 S8766 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 868 ltac:(do 1 right; left; reflexivity)) as S868.
   apply writer_concrete_ground in S868.
   pose proof (Sources 900 ltac:(do 2 right; left; reflexivity)) as S900.
   apply writer_concrete_ground in S900.
   change (exists ground bits, VM.find (N.of_nat 901) result = Some (Gval ground bits)).
   exact (data_address_node_output_901 inputs path old current result S780 S868 S900 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 868 ltac:(do 1 right; left; reflexivity)) as S868.
   apply writer_concrete_ground in S868.
   pose proof (Sources 935 ltac:(do 2 right; left; reflexivity)) as S935.
   apply writer_concrete_ground in S935.
   change (exists ground bits, VM.find (N.of_nat 936) result = Some (Gval ground bits)).
   exact (data_address_node_output_936 inputs path old current result S781 S868 S935 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8330 ltac:(do 0 right; left; reflexivity)) as S8330.
   apply writer_concrete_ground in S8330.
   pose proof (Sources 8424 ltac:(do 1 right; left; reflexivity)) as S8424.
   apply writer_concrete_ground in S8424.
   change (exists ground bits, VM.find (N.of_nat 8425) result = Some (Gval ground bits)).
   exact (data_address_node_output_8425 inputs path old current result S8330 S8424 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8330 ltac:(do 0 right; left; reflexivity)) as S8330.
   apply writer_concrete_ground in S8330.
   pose proof (Sources 8473 ltac:(do 1 right; left; reflexivity)) as S8473.
   apply writer_concrete_ground in S8473.
   change (exists ground bits, VM.find (N.of_nat 8474) result = Some (Gval ground bits)).
   exact (data_address_node_output_8474 inputs path old current result S8330 S8473 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8330 ltac:(do 0 right; left; reflexivity)) as S8330.
   apply writer_concrete_ground in S8330.
   pose proof (Sources 8522 ltac:(do 1 right; left; reflexivity)) as S8522.
   apply writer_concrete_ground in S8522.
   change (exists ground bits, VM.find (N.of_nat 8523) result = Some (Gval ground bits)).
   exact (data_address_node_output_8523 inputs path old current result S8330 S8522 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8330 ltac:(do 0 right; left; reflexivity)) as S8330.
   apply writer_concrete_ground in S8330.
   pose proof (Sources 8571 ltac:(do 1 right; left; reflexivity)) as S8571.
   apply writer_concrete_ground in S8571.
   change (exists ground bits, VM.find (N.of_nat 8572) result = Some (Gval ground bits)).
   exact (data_address_node_output_8572 inputs path old current result S8330 S8571 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8330 ltac:(do 0 right; left; reflexivity)) as S8330.
   apply writer_concrete_ground in S8330.
   pose proof (Sources 8718 ltac:(do 1 right; left; reflexivity)) as S8718.
   apply writer_concrete_ground in S8718.
   change (exists ground bits, VM.find (N.of_nat 8719) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8719 inputs path old current result S8330 S8718 Step). }
 constructor.
Qed.
Definition data_writer_chunk_14 : list (nat * (nat * list nat)) := [::(8768,(20,[::8330;8767]));(902,(21,[::780;869;901]));(937,(21,[::781;869;936]));(8426,(21,[::8328;8425]));(8475,(21,[::8328;8474]));(8524,(21,[::8328;8523]));(8573,(21,[::8328;8572]));(8720,(21,[::8328;8719]));(8769,(21,[::8328;8768]));(903,(22,[::780;870;902]));(938,(22,[::781;870;937]));(8427,(22,[::8326;8426]));(8476,(22,[::8326;8475]));(8525,(22,[::8326;8524]));(8574,(22,[::8326;8573]));(8721,(22,[::8326;8720]));(8770,(22,[::8326;8769]));(904,(23,[::780;871;903]));(939,(23,[::781;871;938]));(8428,(23,[::8324;8427]));(8477,(23,[::8324;8476]));(8526,(23,[::8324;8525]));(8575,(23,[::8324;8574]));(8722,(23,[::8324;8721]))].
Lemma data_writer_chunk_14_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_14.
Proof.
 intros Memory Step. unfold data_writer_chunk_14.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8330 ltac:(do 0 right; left; reflexivity)) as S8330.
   apply writer_concrete_ground in S8330.
   pose proof (Sources 8767 ltac:(do 1 right; left; reflexivity)) as S8767.
   apply writer_concrete_ground in S8767.
   change (exists ground bits, VM.find (N.of_nat 8768) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8768 inputs path old current result S8330 S8767 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 869 ltac:(do 1 right; left; reflexivity)) as S869.
   apply writer_concrete_ground in S869.
   pose proof (Sources 901 ltac:(do 2 right; left; reflexivity)) as S901.
   apply writer_concrete_ground in S901.
   change (exists ground bits, VM.find (N.of_nat 902) result = Some (Gval ground bits)).
   exact (data_address_node_output_902 inputs path old current result S780 S869 S901 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 869 ltac:(do 1 right; left; reflexivity)) as S869.
   apply writer_concrete_ground in S869.
   pose proof (Sources 936 ltac:(do 2 right; left; reflexivity)) as S936.
   apply writer_concrete_ground in S936.
   change (exists ground bits, VM.find (N.of_nat 937) result = Some (Gval ground bits)).
   exact (data_address_node_output_937 inputs path old current result S781 S869 S936 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8328 ltac:(do 0 right; left; reflexivity)) as S8328.
   apply writer_concrete_ground in S8328.
   pose proof (Sources 8425 ltac:(do 1 right; left; reflexivity)) as S8425.
   apply writer_concrete_ground in S8425.
   change (exists ground bits, VM.find (N.of_nat 8426) result = Some (Gval ground bits)).
   exact (data_address_node_output_8426 inputs path old current result S8328 S8425 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8328 ltac:(do 0 right; left; reflexivity)) as S8328.
   apply writer_concrete_ground in S8328.
   pose proof (Sources 8474 ltac:(do 1 right; left; reflexivity)) as S8474.
   apply writer_concrete_ground in S8474.
   change (exists ground bits, VM.find (N.of_nat 8475) result = Some (Gval ground bits)).
   exact (data_address_node_output_8475 inputs path old current result S8328 S8474 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8328 ltac:(do 0 right; left; reflexivity)) as S8328.
   apply writer_concrete_ground in S8328.
   pose proof (Sources 8523 ltac:(do 1 right; left; reflexivity)) as S8523.
   apply writer_concrete_ground in S8523.
   change (exists ground bits, VM.find (N.of_nat 8524) result = Some (Gval ground bits)).
   exact (data_address_node_output_8524 inputs path old current result S8328 S8523 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8328 ltac:(do 0 right; left; reflexivity)) as S8328.
   apply writer_concrete_ground in S8328.
   pose proof (Sources 8572 ltac:(do 1 right; left; reflexivity)) as S8572.
   apply writer_concrete_ground in S8572.
   change (exists ground bits, VM.find (N.of_nat 8573) result = Some (Gval ground bits)).
   exact (data_address_node_output_8573 inputs path old current result S8328 S8572 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8328 ltac:(do 0 right; left; reflexivity)) as S8328.
   apply writer_concrete_ground in S8328.
   pose proof (Sources 8719 ltac:(do 1 right; left; reflexivity)) as S8719.
   apply writer_concrete_ground in S8719.
   change (exists ground bits, VM.find (N.of_nat 8720) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8720 inputs path old current result S8328 S8719 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8328 ltac:(do 0 right; left; reflexivity)) as S8328.
   apply writer_concrete_ground in S8328.
   pose proof (Sources 8768 ltac:(do 1 right; left; reflexivity)) as S8768.
   apply writer_concrete_ground in S8768.
   change (exists ground bits, VM.find (N.of_nat 8769) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8769 inputs path old current result S8328 S8768 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 870 ltac:(do 1 right; left; reflexivity)) as S870.
   apply writer_concrete_ground in S870.
   pose proof (Sources 902 ltac:(do 2 right; left; reflexivity)) as S902.
   apply writer_concrete_ground in S902.
   change (exists ground bits, VM.find (N.of_nat 903) result = Some (Gval ground bits)).
   exact (data_address_node_output_903 inputs path old current result S780 S870 S902 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 870 ltac:(do 1 right; left; reflexivity)) as S870.
   apply writer_concrete_ground in S870.
   pose proof (Sources 937 ltac:(do 2 right; left; reflexivity)) as S937.
   apply writer_concrete_ground in S937.
   change (exists ground bits, VM.find (N.of_nat 938) result = Some (Gval ground bits)).
   exact (data_address_node_output_938 inputs path old current result S781 S870 S937 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8326 ltac:(do 0 right; left; reflexivity)) as S8326.
   apply writer_concrete_ground in S8326.
   pose proof (Sources 8426 ltac:(do 1 right; left; reflexivity)) as S8426.
   apply writer_concrete_ground in S8426.
   change (exists ground bits, VM.find (N.of_nat 8427) result = Some (Gval ground bits)).
   exact (data_address_node_output_8427 inputs path old current result S8326 S8426 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8326 ltac:(do 0 right; left; reflexivity)) as S8326.
   apply writer_concrete_ground in S8326.
   pose proof (Sources 8475 ltac:(do 1 right; left; reflexivity)) as S8475.
   apply writer_concrete_ground in S8475.
   change (exists ground bits, VM.find (N.of_nat 8476) result = Some (Gval ground bits)).
   exact (data_address_node_output_8476 inputs path old current result S8326 S8475 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8326 ltac:(do 0 right; left; reflexivity)) as S8326.
   apply writer_concrete_ground in S8326.
   pose proof (Sources 8524 ltac:(do 1 right; left; reflexivity)) as S8524.
   apply writer_concrete_ground in S8524.
   change (exists ground bits, VM.find (N.of_nat 8525) result = Some (Gval ground bits)).
   exact (data_address_node_output_8525 inputs path old current result S8326 S8524 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8326 ltac:(do 0 right; left; reflexivity)) as S8326.
   apply writer_concrete_ground in S8326.
   pose proof (Sources 8573 ltac:(do 1 right; left; reflexivity)) as S8573.
   apply writer_concrete_ground in S8573.
   change (exists ground bits, VM.find (N.of_nat 8574) result = Some (Gval ground bits)).
   exact (data_address_node_output_8574 inputs path old current result S8326 S8573 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8326 ltac:(do 0 right; left; reflexivity)) as S8326.
   apply writer_concrete_ground in S8326.
   pose proof (Sources 8720 ltac:(do 1 right; left; reflexivity)) as S8720.
   apply writer_concrete_ground in S8720.
   change (exists ground bits, VM.find (N.of_nat 8721) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8721 inputs path old current result S8326 S8720 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8326 ltac:(do 0 right; left; reflexivity)) as S8326.
   apply writer_concrete_ground in S8326.
   pose proof (Sources 8769 ltac:(do 1 right; left; reflexivity)) as S8769.
   apply writer_concrete_ground in S8769.
   change (exists ground bits, VM.find (N.of_nat 8770) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8770 inputs path old current result S8326 S8769 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 871 ltac:(do 1 right; left; reflexivity)) as S871.
   apply writer_concrete_ground in S871.
   pose proof (Sources 903 ltac:(do 2 right; left; reflexivity)) as S903.
   apply writer_concrete_ground in S903.
   change (exists ground bits, VM.find (N.of_nat 904) result = Some (Gval ground bits)).
   exact (data_address_node_output_904 inputs path old current result S780 S871 S903 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 871 ltac:(do 1 right; left; reflexivity)) as S871.
   apply writer_concrete_ground in S871.
   pose proof (Sources 938 ltac:(do 2 right; left; reflexivity)) as S938.
   apply writer_concrete_ground in S938.
   change (exists ground bits, VM.find (N.of_nat 939) result = Some (Gval ground bits)).
   exact (data_address_node_output_939 inputs path old current result S781 S871 S938 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8324 ltac:(do 0 right; left; reflexivity)) as S8324.
   apply writer_concrete_ground in S8324.
   pose proof (Sources 8427 ltac:(do 1 right; left; reflexivity)) as S8427.
   apply writer_concrete_ground in S8427.
   change (exists ground bits, VM.find (N.of_nat 8428) result = Some (Gval ground bits)).
   exact (data_address_node_output_8428 inputs path old current result S8324 S8427 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8324 ltac:(do 0 right; left; reflexivity)) as S8324.
   apply writer_concrete_ground in S8324.
   pose proof (Sources 8476 ltac:(do 1 right; left; reflexivity)) as S8476.
   apply writer_concrete_ground in S8476.
   change (exists ground bits, VM.find (N.of_nat 8477) result = Some (Gval ground bits)).
   exact (data_address_node_output_8477 inputs path old current result S8324 S8476 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8324 ltac:(do 0 right; left; reflexivity)) as S8324.
   apply writer_concrete_ground in S8324.
   pose proof (Sources 8525 ltac:(do 1 right; left; reflexivity)) as S8525.
   apply writer_concrete_ground in S8525.
   change (exists ground bits, VM.find (N.of_nat 8526) result = Some (Gval ground bits)).
   exact (data_address_node_output_8526 inputs path old current result S8324 S8525 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8324 ltac:(do 0 right; left; reflexivity)) as S8324.
   apply writer_concrete_ground in S8324.
   pose proof (Sources 8574 ltac:(do 1 right; left; reflexivity)) as S8574.
   apply writer_concrete_ground in S8574.
   change (exists ground bits, VM.find (N.of_nat 8575) result = Some (Gval ground bits)).
   exact (data_address_node_output_8575 inputs path old current result S8324 S8574 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8324 ltac:(do 0 right; left; reflexivity)) as S8324.
   apply writer_concrete_ground in S8324.
   pose proof (Sources 8721 ltac:(do 1 right; left; reflexivity)) as S8721.
   apply writer_concrete_ground in S8721.
   change (exists ground bits, VM.find (N.of_nat 8722) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8722 inputs path old current result S8324 S8721 Step). }
 constructor.
Qed.
Definition data_writer_chunk_15 : list (nat * (nat * list nat)) := [::(8771,(23,[::8324;8770]));(905,(24,[::780;872;904]));(940,(24,[::781;872;939]));(8429,(24,[::8322;8428]));(8478,(24,[::8322;8477]));(8527,(24,[::8322;8526]));(8576,(24,[::8322;8575]));(8723,(24,[::8322;8722]));(8772,(24,[::8322;8771]));(906,(25,[::780;873;905]));(941,(25,[::781;873;940]));(8430,(25,[::8320;8429]));(8479,(25,[::8320;8478]));(8528,(25,[::8320;8527]));(8577,(25,[::8320;8576]));(8724,(25,[::8320;8723]));(8773,(25,[::8320;8772]));(907,(26,[::780;874;906]));(942,(26,[::781;874;941]));(8431,(26,[::8318;8430]));(8480,(26,[::8318;8479]));(8529,(26,[::8318;8528]));(8578,(26,[::8318;8577]));(8725,(26,[::8318;8724]))].
Lemma data_writer_chunk_15_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_15.
Proof.
 intros Memory Step. unfold data_writer_chunk_15.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8324 ltac:(do 0 right; left; reflexivity)) as S8324.
   apply writer_concrete_ground in S8324.
   pose proof (Sources 8770 ltac:(do 1 right; left; reflexivity)) as S8770.
   apply writer_concrete_ground in S8770.
   change (exists ground bits, VM.find (N.of_nat 8771) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8771 inputs path old current result S8324 S8770 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 872 ltac:(do 1 right; left; reflexivity)) as S872.
   apply writer_concrete_ground in S872.
   pose proof (Sources 904 ltac:(do 2 right; left; reflexivity)) as S904.
   apply writer_concrete_ground in S904.
   change (exists ground bits, VM.find (N.of_nat 905) result = Some (Gval ground bits)).
   exact (data_address_node_output_905 inputs path old current result S780 S872 S904 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 872 ltac:(do 1 right; left; reflexivity)) as S872.
   apply writer_concrete_ground in S872.
   pose proof (Sources 939 ltac:(do 2 right; left; reflexivity)) as S939.
   apply writer_concrete_ground in S939.
   change (exists ground bits, VM.find (N.of_nat 940) result = Some (Gval ground bits)).
   exact (data_address_node_output_940 inputs path old current result S781 S872 S939 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8322 ltac:(do 0 right; left; reflexivity)) as S8322.
   apply writer_concrete_ground in S8322.
   pose proof (Sources 8428 ltac:(do 1 right; left; reflexivity)) as S8428.
   apply writer_concrete_ground in S8428.
   change (exists ground bits, VM.find (N.of_nat 8429) result = Some (Gval ground bits)).
   exact (data_address_node_output_8429 inputs path old current result S8322 S8428 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8322 ltac:(do 0 right; left; reflexivity)) as S8322.
   apply writer_concrete_ground in S8322.
   pose proof (Sources 8477 ltac:(do 1 right; left; reflexivity)) as S8477.
   apply writer_concrete_ground in S8477.
   change (exists ground bits, VM.find (N.of_nat 8478) result = Some (Gval ground bits)).
   exact (data_address_node_output_8478 inputs path old current result S8322 S8477 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8322 ltac:(do 0 right; left; reflexivity)) as S8322.
   apply writer_concrete_ground in S8322.
   pose proof (Sources 8526 ltac:(do 1 right; left; reflexivity)) as S8526.
   apply writer_concrete_ground in S8526.
   change (exists ground bits, VM.find (N.of_nat 8527) result = Some (Gval ground bits)).
   exact (data_address_node_output_8527 inputs path old current result S8322 S8526 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8322 ltac:(do 0 right; left; reflexivity)) as S8322.
   apply writer_concrete_ground in S8322.
   pose proof (Sources 8575 ltac:(do 1 right; left; reflexivity)) as S8575.
   apply writer_concrete_ground in S8575.
   change (exists ground bits, VM.find (N.of_nat 8576) result = Some (Gval ground bits)).
   exact (data_address_node_output_8576 inputs path old current result S8322 S8575 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8322 ltac:(do 0 right; left; reflexivity)) as S8322.
   apply writer_concrete_ground in S8322.
   pose proof (Sources 8722 ltac:(do 1 right; left; reflexivity)) as S8722.
   apply writer_concrete_ground in S8722.
   change (exists ground bits, VM.find (N.of_nat 8723) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8723 inputs path old current result S8322 S8722 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8322 ltac:(do 0 right; left; reflexivity)) as S8322.
   apply writer_concrete_ground in S8322.
   pose proof (Sources 8771 ltac:(do 1 right; left; reflexivity)) as S8771.
   apply writer_concrete_ground in S8771.
   change (exists ground bits, VM.find (N.of_nat 8772) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8772 inputs path old current result S8322 S8771 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 873 ltac:(do 1 right; left; reflexivity)) as S873.
   apply writer_concrete_ground in S873.
   pose proof (Sources 905 ltac:(do 2 right; left; reflexivity)) as S905.
   apply writer_concrete_ground in S905.
   change (exists ground bits, VM.find (N.of_nat 906) result = Some (Gval ground bits)).
   exact (data_address_node_output_906 inputs path old current result S780 S873 S905 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 873 ltac:(do 1 right; left; reflexivity)) as S873.
   apply writer_concrete_ground in S873.
   pose proof (Sources 940 ltac:(do 2 right; left; reflexivity)) as S940.
   apply writer_concrete_ground in S940.
   change (exists ground bits, VM.find (N.of_nat 941) result = Some (Gval ground bits)).
   exact (data_address_node_output_941 inputs path old current result S781 S873 S940 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8320 ltac:(do 0 right; left; reflexivity)) as S8320.
   apply writer_concrete_ground in S8320.
   pose proof (Sources 8429 ltac:(do 1 right; left; reflexivity)) as S8429.
   apply writer_concrete_ground in S8429.
   change (exists ground bits, VM.find (N.of_nat 8430) result = Some (Gval ground bits)).
   exact (data_address_node_output_8430 inputs path old current result S8320 S8429 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8320 ltac:(do 0 right; left; reflexivity)) as S8320.
   apply writer_concrete_ground in S8320.
   pose proof (Sources 8478 ltac:(do 1 right; left; reflexivity)) as S8478.
   apply writer_concrete_ground in S8478.
   change (exists ground bits, VM.find (N.of_nat 8479) result = Some (Gval ground bits)).
   exact (data_address_node_output_8479 inputs path old current result S8320 S8478 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8320 ltac:(do 0 right; left; reflexivity)) as S8320.
   apply writer_concrete_ground in S8320.
   pose proof (Sources 8527 ltac:(do 1 right; left; reflexivity)) as S8527.
   apply writer_concrete_ground in S8527.
   change (exists ground bits, VM.find (N.of_nat 8528) result = Some (Gval ground bits)).
   exact (data_address_node_output_8528 inputs path old current result S8320 S8527 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8320 ltac:(do 0 right; left; reflexivity)) as S8320.
   apply writer_concrete_ground in S8320.
   pose proof (Sources 8576 ltac:(do 1 right; left; reflexivity)) as S8576.
   apply writer_concrete_ground in S8576.
   change (exists ground bits, VM.find (N.of_nat 8577) result = Some (Gval ground bits)).
   exact (data_address_node_output_8577 inputs path old current result S8320 S8576 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8320 ltac:(do 0 right; left; reflexivity)) as S8320.
   apply writer_concrete_ground in S8320.
   pose proof (Sources 8723 ltac:(do 1 right; left; reflexivity)) as S8723.
   apply writer_concrete_ground in S8723.
   change (exists ground bits, VM.find (N.of_nat 8724) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8724 inputs path old current result S8320 S8723 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8320 ltac:(do 0 right; left; reflexivity)) as S8320.
   apply writer_concrete_ground in S8320.
   pose proof (Sources 8772 ltac:(do 1 right; left; reflexivity)) as S8772.
   apply writer_concrete_ground in S8772.
   change (exists ground bits, VM.find (N.of_nat 8773) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8773 inputs path old current result S8320 S8772 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 874 ltac:(do 1 right; left; reflexivity)) as S874.
   apply writer_concrete_ground in S874.
   pose proof (Sources 906 ltac:(do 2 right; left; reflexivity)) as S906.
   apply writer_concrete_ground in S906.
   change (exists ground bits, VM.find (N.of_nat 907) result = Some (Gval ground bits)).
   exact (data_address_node_output_907 inputs path old current result S780 S874 S906 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 874 ltac:(do 1 right; left; reflexivity)) as S874.
   apply writer_concrete_ground in S874.
   pose proof (Sources 941 ltac:(do 2 right; left; reflexivity)) as S941.
   apply writer_concrete_ground in S941.
   change (exists ground bits, VM.find (N.of_nat 942) result = Some (Gval ground bits)).
   exact (data_address_node_output_942 inputs path old current result S781 S874 S941 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8318 ltac:(do 0 right; left; reflexivity)) as S8318.
   apply writer_concrete_ground in S8318.
   pose proof (Sources 8430 ltac:(do 1 right; left; reflexivity)) as S8430.
   apply writer_concrete_ground in S8430.
   change (exists ground bits, VM.find (N.of_nat 8431) result = Some (Gval ground bits)).
   exact (data_address_node_output_8431 inputs path old current result S8318 S8430 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8318 ltac:(do 0 right; left; reflexivity)) as S8318.
   apply writer_concrete_ground in S8318.
   pose proof (Sources 8479 ltac:(do 1 right; left; reflexivity)) as S8479.
   apply writer_concrete_ground in S8479.
   change (exists ground bits, VM.find (N.of_nat 8480) result = Some (Gval ground bits)).
   exact (data_address_node_output_8480 inputs path old current result S8318 S8479 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8318 ltac:(do 0 right; left; reflexivity)) as S8318.
   apply writer_concrete_ground in S8318.
   pose proof (Sources 8528 ltac:(do 1 right; left; reflexivity)) as S8528.
   apply writer_concrete_ground in S8528.
   change (exists ground bits, VM.find (N.of_nat 8529) result = Some (Gval ground bits)).
   exact (data_address_node_output_8529 inputs path old current result S8318 S8528 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8318 ltac:(do 0 right; left; reflexivity)) as S8318.
   apply writer_concrete_ground in S8318.
   pose proof (Sources 8577 ltac:(do 1 right; left; reflexivity)) as S8577.
   apply writer_concrete_ground in S8577.
   change (exists ground bits, VM.find (N.of_nat 8578) result = Some (Gval ground bits)).
   exact (data_address_node_output_8578 inputs path old current result S8318 S8577 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8318 ltac:(do 0 right; left; reflexivity)) as S8318.
   apply writer_concrete_ground in S8318.
   pose proof (Sources 8724 ltac:(do 1 right; left; reflexivity)) as S8724.
   apply writer_concrete_ground in S8724.
   change (exists ground bits, VM.find (N.of_nat 8725) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8725 inputs path old current result S8318 S8724 Step). }
 constructor.
Qed.
Definition data_writer_chunk_16 : list (nat * (nat * list nat)) := [::(8774,(26,[::8318;8773]));(908,(27,[::780;875;907]));(943,(27,[::781;875;942]));(8432,(27,[::8316;8431]));(8481,(27,[::8316;8480]));(8530,(27,[::8316;8529]));(8579,(27,[::8316;8578]));(8726,(27,[::8316;8725]));(8775,(27,[::8316;8774]));(909,(28,[::780;876;908]));(944,(28,[::781;876;943]));(8433,(28,[::8314;8432]));(8482,(28,[::8314;8481]));(8531,(28,[::8314;8530]));(8580,(28,[::8314;8579]));(8727,(28,[::8314;8726]));(8776,(28,[::8314;8775]));(910,(29,[::780;877;909]));(945,(29,[::781;877;944]));(8434,(29,[::8312;8433]));(8483,(29,[::8312;8482]));(8532,(29,[::8312;8531]));(8581,(29,[::8312;8580]));(8728,(29,[::8312;8727]))].
Lemma data_writer_chunk_16_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_16.
Proof.
 intros Memory Step. unfold data_writer_chunk_16.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8318 ltac:(do 0 right; left; reflexivity)) as S8318.
   apply writer_concrete_ground in S8318.
   pose proof (Sources 8773 ltac:(do 1 right; left; reflexivity)) as S8773.
   apply writer_concrete_ground in S8773.
   change (exists ground bits, VM.find (N.of_nat 8774) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8774 inputs path old current result S8318 S8773 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 875 ltac:(do 1 right; left; reflexivity)) as S875.
   apply writer_concrete_ground in S875.
   pose proof (Sources 907 ltac:(do 2 right; left; reflexivity)) as S907.
   apply writer_concrete_ground in S907.
   change (exists ground bits, VM.find (N.of_nat 908) result = Some (Gval ground bits)).
   exact (data_address_node_output_908 inputs path old current result S780 S875 S907 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 875 ltac:(do 1 right; left; reflexivity)) as S875.
   apply writer_concrete_ground in S875.
   pose proof (Sources 942 ltac:(do 2 right; left; reflexivity)) as S942.
   apply writer_concrete_ground in S942.
   change (exists ground bits, VM.find (N.of_nat 943) result = Some (Gval ground bits)).
   exact (data_address_node_output_943 inputs path old current result S781 S875 S942 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8316 ltac:(do 0 right; left; reflexivity)) as S8316.
   apply writer_concrete_ground in S8316.
   pose proof (Sources 8431 ltac:(do 1 right; left; reflexivity)) as S8431.
   apply writer_concrete_ground in S8431.
   change (exists ground bits, VM.find (N.of_nat 8432) result = Some (Gval ground bits)).
   exact (data_address_node_output_8432 inputs path old current result S8316 S8431 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8316 ltac:(do 0 right; left; reflexivity)) as S8316.
   apply writer_concrete_ground in S8316.
   pose proof (Sources 8480 ltac:(do 1 right; left; reflexivity)) as S8480.
   apply writer_concrete_ground in S8480.
   change (exists ground bits, VM.find (N.of_nat 8481) result = Some (Gval ground bits)).
   exact (data_address_node_output_8481 inputs path old current result S8316 S8480 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8316 ltac:(do 0 right; left; reflexivity)) as S8316.
   apply writer_concrete_ground in S8316.
   pose proof (Sources 8529 ltac:(do 1 right; left; reflexivity)) as S8529.
   apply writer_concrete_ground in S8529.
   change (exists ground bits, VM.find (N.of_nat 8530) result = Some (Gval ground bits)).
   exact (data_address_node_output_8530 inputs path old current result S8316 S8529 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8316 ltac:(do 0 right; left; reflexivity)) as S8316.
   apply writer_concrete_ground in S8316.
   pose proof (Sources 8578 ltac:(do 1 right; left; reflexivity)) as S8578.
   apply writer_concrete_ground in S8578.
   change (exists ground bits, VM.find (N.of_nat 8579) result = Some (Gval ground bits)).
   exact (data_address_node_output_8579 inputs path old current result S8316 S8578 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8316 ltac:(do 0 right; left; reflexivity)) as S8316.
   apply writer_concrete_ground in S8316.
   pose proof (Sources 8725 ltac:(do 1 right; left; reflexivity)) as S8725.
   apply writer_concrete_ground in S8725.
   change (exists ground bits, VM.find (N.of_nat 8726) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8726 inputs path old current result S8316 S8725 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8316 ltac:(do 0 right; left; reflexivity)) as S8316.
   apply writer_concrete_ground in S8316.
   pose proof (Sources 8774 ltac:(do 1 right; left; reflexivity)) as S8774.
   apply writer_concrete_ground in S8774.
   change (exists ground bits, VM.find (N.of_nat 8775) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8775 inputs path old current result S8316 S8774 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 876 ltac:(do 1 right; left; reflexivity)) as S876.
   apply writer_concrete_ground in S876.
   pose proof (Sources 908 ltac:(do 2 right; left; reflexivity)) as S908.
   apply writer_concrete_ground in S908.
   change (exists ground bits, VM.find (N.of_nat 909) result = Some (Gval ground bits)).
   exact (data_address_node_output_909 inputs path old current result S780 S876 S908 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 876 ltac:(do 1 right; left; reflexivity)) as S876.
   apply writer_concrete_ground in S876.
   pose proof (Sources 943 ltac:(do 2 right; left; reflexivity)) as S943.
   apply writer_concrete_ground in S943.
   change (exists ground bits, VM.find (N.of_nat 944) result = Some (Gval ground bits)).
   exact (data_address_node_output_944 inputs path old current result S781 S876 S943 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8314 ltac:(do 0 right; left; reflexivity)) as S8314.
   apply writer_concrete_ground in S8314.
   pose proof (Sources 8432 ltac:(do 1 right; left; reflexivity)) as S8432.
   apply writer_concrete_ground in S8432.
   change (exists ground bits, VM.find (N.of_nat 8433) result = Some (Gval ground bits)).
   exact (data_address_node_output_8433 inputs path old current result S8314 S8432 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8314 ltac:(do 0 right; left; reflexivity)) as S8314.
   apply writer_concrete_ground in S8314.
   pose proof (Sources 8481 ltac:(do 1 right; left; reflexivity)) as S8481.
   apply writer_concrete_ground in S8481.
   change (exists ground bits, VM.find (N.of_nat 8482) result = Some (Gval ground bits)).
   exact (data_address_node_output_8482 inputs path old current result S8314 S8481 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8314 ltac:(do 0 right; left; reflexivity)) as S8314.
   apply writer_concrete_ground in S8314.
   pose proof (Sources 8530 ltac:(do 1 right; left; reflexivity)) as S8530.
   apply writer_concrete_ground in S8530.
   change (exists ground bits, VM.find (N.of_nat 8531) result = Some (Gval ground bits)).
   exact (data_address_node_output_8531 inputs path old current result S8314 S8530 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8314 ltac:(do 0 right; left; reflexivity)) as S8314.
   apply writer_concrete_ground in S8314.
   pose proof (Sources 8579 ltac:(do 1 right; left; reflexivity)) as S8579.
   apply writer_concrete_ground in S8579.
   change (exists ground bits, VM.find (N.of_nat 8580) result = Some (Gval ground bits)).
   exact (data_address_node_output_8580 inputs path old current result S8314 S8579 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8314 ltac:(do 0 right; left; reflexivity)) as S8314.
   apply writer_concrete_ground in S8314.
   pose proof (Sources 8726 ltac:(do 1 right; left; reflexivity)) as S8726.
   apply writer_concrete_ground in S8726.
   change (exists ground bits, VM.find (N.of_nat 8727) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8727 inputs path old current result S8314 S8726 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8314 ltac:(do 0 right; left; reflexivity)) as S8314.
   apply writer_concrete_ground in S8314.
   pose proof (Sources 8775 ltac:(do 1 right; left; reflexivity)) as S8775.
   apply writer_concrete_ground in S8775.
   change (exists ground bits, VM.find (N.of_nat 8776) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8776 inputs path old current result S8314 S8775 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 877 ltac:(do 1 right; left; reflexivity)) as S877.
   apply writer_concrete_ground in S877.
   pose proof (Sources 909 ltac:(do 2 right; left; reflexivity)) as S909.
   apply writer_concrete_ground in S909.
   change (exists ground bits, VM.find (N.of_nat 910) result = Some (Gval ground bits)).
   exact (data_address_node_output_910 inputs path old current result S780 S877 S909 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 877 ltac:(do 1 right; left; reflexivity)) as S877.
   apply writer_concrete_ground in S877.
   pose proof (Sources 944 ltac:(do 2 right; left; reflexivity)) as S944.
   apply writer_concrete_ground in S944.
   change (exists ground bits, VM.find (N.of_nat 945) result = Some (Gval ground bits)).
   exact (data_address_node_output_945 inputs path old current result S781 S877 S944 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8312 ltac:(do 0 right; left; reflexivity)) as S8312.
   apply writer_concrete_ground in S8312.
   pose proof (Sources 8433 ltac:(do 1 right; left; reflexivity)) as S8433.
   apply writer_concrete_ground in S8433.
   change (exists ground bits, VM.find (N.of_nat 8434) result = Some (Gval ground bits)).
   exact (data_address_node_output_8434 inputs path old current result S8312 S8433 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8312 ltac:(do 0 right; left; reflexivity)) as S8312.
   apply writer_concrete_ground in S8312.
   pose proof (Sources 8482 ltac:(do 1 right; left; reflexivity)) as S8482.
   apply writer_concrete_ground in S8482.
   change (exists ground bits, VM.find (N.of_nat 8483) result = Some (Gval ground bits)).
   exact (data_address_node_output_8483 inputs path old current result S8312 S8482 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8312 ltac:(do 0 right; left; reflexivity)) as S8312.
   apply writer_concrete_ground in S8312.
   pose proof (Sources 8531 ltac:(do 1 right; left; reflexivity)) as S8531.
   apply writer_concrete_ground in S8531.
   change (exists ground bits, VM.find (N.of_nat 8532) result = Some (Gval ground bits)).
   exact (data_address_node_output_8532 inputs path old current result S8312 S8531 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8312 ltac:(do 0 right; left; reflexivity)) as S8312.
   apply writer_concrete_ground in S8312.
   pose proof (Sources 8580 ltac:(do 1 right; left; reflexivity)) as S8580.
   apply writer_concrete_ground in S8580.
   change (exists ground bits, VM.find (N.of_nat 8581) result = Some (Gval ground bits)).
   exact (data_address_node_output_8581 inputs path old current result S8312 S8580 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8312 ltac:(do 0 right; left; reflexivity)) as S8312.
   apply writer_concrete_ground in S8312.
   pose proof (Sources 8727 ltac:(do 1 right; left; reflexivity)) as S8727.
   apply writer_concrete_ground in S8727.
   change (exists ground bits, VM.find (N.of_nat 8728) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8728 inputs path old current result S8312 S8727 Step). }
 constructor.
Qed.
Definition data_writer_chunk_17 : list (nat * (nat * list nat)) := [::(8777,(29,[::8312;8776]));(911,(30,[::780;878;910]));(946,(30,[::781;878;945]));(8435,(30,[::8310;8434]));(8484,(30,[::8310;8483]));(8533,(30,[::8310;8532]));(8582,(30,[::8310;8581]));(8729,(30,[::8310;8728]));(8778,(30,[::8310;8777]));(912,(31,[::780;879;911]));(947,(31,[::781;879;946]));(8436,(31,[::8308;8435]));(8485,(31,[::8308;8484]));(8534,(31,[::8308;8533]));(8583,(31,[::8308;8582]));(8730,(31,[::8308;8729]));(8779,(31,[::8308;8778]));(913,(32,[::780;880;912]));(948,(32,[::781;880;947]));(8437,(32,[::8306;8436]));(8486,(32,[::8306;8485]));(8535,(32,[::8306;8534]));(8584,(32,[::8306;8583]));(8731,(32,[::8306;8730]))].
Lemma data_writer_chunk_17_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_17.
Proof.
 intros Memory Step. unfold data_writer_chunk_17.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8312 ltac:(do 0 right; left; reflexivity)) as S8312.
   apply writer_concrete_ground in S8312.
   pose proof (Sources 8776 ltac:(do 1 right; left; reflexivity)) as S8776.
   apply writer_concrete_ground in S8776.
   change (exists ground bits, VM.find (N.of_nat 8777) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8777 inputs path old current result S8312 S8776 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 878 ltac:(do 1 right; left; reflexivity)) as S878.
   apply writer_concrete_ground in S878.
   pose proof (Sources 910 ltac:(do 2 right; left; reflexivity)) as S910.
   apply writer_concrete_ground in S910.
   change (exists ground bits, VM.find (N.of_nat 911) result = Some (Gval ground bits)).
   exact (data_address_node_output_911 inputs path old current result S780 S878 S910 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 878 ltac:(do 1 right; left; reflexivity)) as S878.
   apply writer_concrete_ground in S878.
   pose proof (Sources 945 ltac:(do 2 right; left; reflexivity)) as S945.
   apply writer_concrete_ground in S945.
   change (exists ground bits, VM.find (N.of_nat 946) result = Some (Gval ground bits)).
   exact (data_address_node_output_946 inputs path old current result S781 S878 S945 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8310 ltac:(do 0 right; left; reflexivity)) as S8310.
   apply writer_concrete_ground in S8310.
   pose proof (Sources 8434 ltac:(do 1 right; left; reflexivity)) as S8434.
   apply writer_concrete_ground in S8434.
   change (exists ground bits, VM.find (N.of_nat 8435) result = Some (Gval ground bits)).
   exact (data_address_node_output_8435 inputs path old current result S8310 S8434 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8310 ltac:(do 0 right; left; reflexivity)) as S8310.
   apply writer_concrete_ground in S8310.
   pose proof (Sources 8483 ltac:(do 1 right; left; reflexivity)) as S8483.
   apply writer_concrete_ground in S8483.
   change (exists ground bits, VM.find (N.of_nat 8484) result = Some (Gval ground bits)).
   exact (data_address_node_output_8484 inputs path old current result S8310 S8483 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8310 ltac:(do 0 right; left; reflexivity)) as S8310.
   apply writer_concrete_ground in S8310.
   pose proof (Sources 8532 ltac:(do 1 right; left; reflexivity)) as S8532.
   apply writer_concrete_ground in S8532.
   change (exists ground bits, VM.find (N.of_nat 8533) result = Some (Gval ground bits)).
   exact (data_address_node_output_8533 inputs path old current result S8310 S8532 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8310 ltac:(do 0 right; left; reflexivity)) as S8310.
   apply writer_concrete_ground in S8310.
   pose proof (Sources 8581 ltac:(do 1 right; left; reflexivity)) as S8581.
   apply writer_concrete_ground in S8581.
   change (exists ground bits, VM.find (N.of_nat 8582) result = Some (Gval ground bits)).
   exact (data_address_node_output_8582 inputs path old current result S8310 S8581 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8310 ltac:(do 0 right; left; reflexivity)) as S8310.
   apply writer_concrete_ground in S8310.
   pose proof (Sources 8728 ltac:(do 1 right; left; reflexivity)) as S8728.
   apply writer_concrete_ground in S8728.
   change (exists ground bits, VM.find (N.of_nat 8729) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8729 inputs path old current result S8310 S8728 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8310 ltac:(do 0 right; left; reflexivity)) as S8310.
   apply writer_concrete_ground in S8310.
   pose proof (Sources 8777 ltac:(do 1 right; left; reflexivity)) as S8777.
   apply writer_concrete_ground in S8777.
   change (exists ground bits, VM.find (N.of_nat 8778) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8778 inputs path old current result S8310 S8777 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 879 ltac:(do 1 right; left; reflexivity)) as S879.
   apply writer_concrete_ground in S879.
   pose proof (Sources 911 ltac:(do 2 right; left; reflexivity)) as S911.
   apply writer_concrete_ground in S911.
   change (exists ground bits, VM.find (N.of_nat 912) result = Some (Gval ground bits)).
   exact (data_address_node_output_912 inputs path old current result S780 S879 S911 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 879 ltac:(do 1 right; left; reflexivity)) as S879.
   apply writer_concrete_ground in S879.
   pose proof (Sources 946 ltac:(do 2 right; left; reflexivity)) as S946.
   apply writer_concrete_ground in S946.
   change (exists ground bits, VM.find (N.of_nat 947) result = Some (Gval ground bits)).
   exact (data_address_node_output_947 inputs path old current result S781 S879 S946 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8308 ltac:(do 0 right; left; reflexivity)) as S8308.
   apply writer_concrete_ground in S8308.
   pose proof (Sources 8435 ltac:(do 1 right; left; reflexivity)) as S8435.
   apply writer_concrete_ground in S8435.
   change (exists ground bits, VM.find (N.of_nat 8436) result = Some (Gval ground bits)).
   exact (data_address_node_output_8436 inputs path old current result S8308 S8435 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8308 ltac:(do 0 right; left; reflexivity)) as S8308.
   apply writer_concrete_ground in S8308.
   pose proof (Sources 8484 ltac:(do 1 right; left; reflexivity)) as S8484.
   apply writer_concrete_ground in S8484.
   change (exists ground bits, VM.find (N.of_nat 8485) result = Some (Gval ground bits)).
   exact (data_address_node_output_8485 inputs path old current result S8308 S8484 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8308 ltac:(do 0 right; left; reflexivity)) as S8308.
   apply writer_concrete_ground in S8308.
   pose proof (Sources 8533 ltac:(do 1 right; left; reflexivity)) as S8533.
   apply writer_concrete_ground in S8533.
   change (exists ground bits, VM.find (N.of_nat 8534) result = Some (Gval ground bits)).
   exact (data_address_node_output_8534 inputs path old current result S8308 S8533 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8308 ltac:(do 0 right; left; reflexivity)) as S8308.
   apply writer_concrete_ground in S8308.
   pose proof (Sources 8582 ltac:(do 1 right; left; reflexivity)) as S8582.
   apply writer_concrete_ground in S8582.
   change (exists ground bits, VM.find (N.of_nat 8583) result = Some (Gval ground bits)).
   exact (data_address_node_output_8583 inputs path old current result S8308 S8582 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8308 ltac:(do 0 right; left; reflexivity)) as S8308.
   apply writer_concrete_ground in S8308.
   pose proof (Sources 8729 ltac:(do 1 right; left; reflexivity)) as S8729.
   apply writer_concrete_ground in S8729.
   change (exists ground bits, VM.find (N.of_nat 8730) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8730 inputs path old current result S8308 S8729 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8308 ltac:(do 0 right; left; reflexivity)) as S8308.
   apply writer_concrete_ground in S8308.
   pose proof (Sources 8778 ltac:(do 1 right; left; reflexivity)) as S8778.
   apply writer_concrete_ground in S8778.
   change (exists ground bits, VM.find (N.of_nat 8779) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8779 inputs path old current result S8308 S8778 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 880 ltac:(do 1 right; left; reflexivity)) as S880.
   apply writer_concrete_ground in S880.
   pose proof (Sources 912 ltac:(do 2 right; left; reflexivity)) as S912.
   apply writer_concrete_ground in S912.
   change (exists ground bits, VM.find (N.of_nat 913) result = Some (Gval ground bits)).
   exact (data_address_node_output_913 inputs path old current result S780 S880 S912 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 880 ltac:(do 1 right; left; reflexivity)) as S880.
   apply writer_concrete_ground in S880.
   pose proof (Sources 947 ltac:(do 2 right; left; reflexivity)) as S947.
   apply writer_concrete_ground in S947.
   change (exists ground bits, VM.find (N.of_nat 948) result = Some (Gval ground bits)).
   exact (data_address_node_output_948 inputs path old current result S781 S880 S947 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8306 ltac:(do 0 right; left; reflexivity)) as S8306.
   apply writer_concrete_ground in S8306.
   pose proof (Sources 8436 ltac:(do 1 right; left; reflexivity)) as S8436.
   apply writer_concrete_ground in S8436.
   change (exists ground bits, VM.find (N.of_nat 8437) result = Some (Gval ground bits)).
   exact (data_address_node_output_8437 inputs path old current result S8306 S8436 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8306 ltac:(do 0 right; left; reflexivity)) as S8306.
   apply writer_concrete_ground in S8306.
   pose proof (Sources 8485 ltac:(do 1 right; left; reflexivity)) as S8485.
   apply writer_concrete_ground in S8485.
   change (exists ground bits, VM.find (N.of_nat 8486) result = Some (Gval ground bits)).
   exact (data_address_node_output_8486 inputs path old current result S8306 S8485 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8306 ltac:(do 0 right; left; reflexivity)) as S8306.
   apply writer_concrete_ground in S8306.
   pose proof (Sources 8534 ltac:(do 1 right; left; reflexivity)) as S8534.
   apply writer_concrete_ground in S8534.
   change (exists ground bits, VM.find (N.of_nat 8535) result = Some (Gval ground bits)).
   exact (data_address_node_output_8535 inputs path old current result S8306 S8534 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8306 ltac:(do 0 right; left; reflexivity)) as S8306.
   apply writer_concrete_ground in S8306.
   pose proof (Sources 8583 ltac:(do 1 right; left; reflexivity)) as S8583.
   apply writer_concrete_ground in S8583.
   change (exists ground bits, VM.find (N.of_nat 8584) result = Some (Gval ground bits)).
   exact (data_address_node_output_8584 inputs path old current result S8306 S8583 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8306 ltac:(do 0 right; left; reflexivity)) as S8306.
   apply writer_concrete_ground in S8306.
   pose proof (Sources 8730 ltac:(do 1 right; left; reflexivity)) as S8730.
   apply writer_concrete_ground in S8730.
   change (exists ground bits, VM.find (N.of_nat 8731) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8731 inputs path old current result S8306 S8730 Step). }
 constructor.
Qed.
Definition data_writer_chunk_18 : list (nat * (nat * list nat)) := [::(8780,(32,[::8306;8779]));(914,(33,[::780;881;913]));(949,(33,[::781;881;948]));(8438,(33,[::8304;8437]));(8487,(33,[::8304;8486]));(8536,(33,[::8304;8535]));(8585,(33,[::8304;8584]));(8732,(33,[::8304;8731]));(8781,(33,[::8304;8780]));(915,(34,[::780;882;914]));(950,(34,[::781;882;949]));(8439,(34,[::8302;8438]));(8488,(34,[::8302;8487]));(8537,(34,[::8302;8536]));(8586,(34,[::8302;8585]));(8733,(34,[::8302;8732]));(8782,(34,[::8302;8781]));(916,(35,[::915]));(951,(35,[::950]));(8440,(35,[::8300;8439]));(8489,(35,[::8300;8488]));(8538,(35,[::8300;8537]));(8587,(35,[::8300;8586]));(8734,(35,[::8300;8733]))].
Lemma data_writer_chunk_18_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_18.
Proof.
 intros Memory Step. unfold data_writer_chunk_18.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8306 ltac:(do 0 right; left; reflexivity)) as S8306.
   apply writer_concrete_ground in S8306.
   pose proof (Sources 8779 ltac:(do 1 right; left; reflexivity)) as S8779.
   apply writer_concrete_ground in S8779.
   change (exists ground bits, VM.find (N.of_nat 8780) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8780 inputs path old current result S8306 S8779 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 881 ltac:(do 1 right; left; reflexivity)) as S881.
   apply writer_concrete_ground in S881.
   pose proof (Sources 913 ltac:(do 2 right; left; reflexivity)) as S913.
   apply writer_concrete_ground in S913.
   change (exists ground bits, VM.find (N.of_nat 914) result = Some (Gval ground bits)).
   exact (data_address_node_output_914 inputs path old current result S780 S881 S913 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 881 ltac:(do 1 right; left; reflexivity)) as S881.
   apply writer_concrete_ground in S881.
   pose proof (Sources 948 ltac:(do 2 right; left; reflexivity)) as S948.
   apply writer_concrete_ground in S948.
   change (exists ground bits, VM.find (N.of_nat 949) result = Some (Gval ground bits)).
   exact (data_address_node_output_949 inputs path old current result S781 S881 S948 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8304 ltac:(do 0 right; left; reflexivity)) as S8304.
   apply writer_concrete_ground in S8304.
   pose proof (Sources 8437 ltac:(do 1 right; left; reflexivity)) as S8437.
   apply writer_concrete_ground in S8437.
   change (exists ground bits, VM.find (N.of_nat 8438) result = Some (Gval ground bits)).
   exact (data_address_node_output_8438 inputs path old current result S8304 S8437 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8304 ltac:(do 0 right; left; reflexivity)) as S8304.
   apply writer_concrete_ground in S8304.
   pose proof (Sources 8486 ltac:(do 1 right; left; reflexivity)) as S8486.
   apply writer_concrete_ground in S8486.
   change (exists ground bits, VM.find (N.of_nat 8487) result = Some (Gval ground bits)).
   exact (data_address_node_output_8487 inputs path old current result S8304 S8486 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8304 ltac:(do 0 right; left; reflexivity)) as S8304.
   apply writer_concrete_ground in S8304.
   pose proof (Sources 8535 ltac:(do 1 right; left; reflexivity)) as S8535.
   apply writer_concrete_ground in S8535.
   change (exists ground bits, VM.find (N.of_nat 8536) result = Some (Gval ground bits)).
   exact (data_address_node_output_8536 inputs path old current result S8304 S8535 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8304 ltac:(do 0 right; left; reflexivity)) as S8304.
   apply writer_concrete_ground in S8304.
   pose proof (Sources 8584 ltac:(do 1 right; left; reflexivity)) as S8584.
   apply writer_concrete_ground in S8584.
   change (exists ground bits, VM.find (N.of_nat 8585) result = Some (Gval ground bits)).
   exact (data_address_node_output_8585 inputs path old current result S8304 S8584 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8304 ltac:(do 0 right; left; reflexivity)) as S8304.
   apply writer_concrete_ground in S8304.
   pose proof (Sources 8731 ltac:(do 1 right; left; reflexivity)) as S8731.
   apply writer_concrete_ground in S8731.
   change (exists ground bits, VM.find (N.of_nat 8732) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8732 inputs path old current result S8304 S8731 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8304 ltac:(do 0 right; left; reflexivity)) as S8304.
   apply writer_concrete_ground in S8304.
   pose proof (Sources 8780 ltac:(do 1 right; left; reflexivity)) as S8780.
   apply writer_concrete_ground in S8780.
   change (exists ground bits, VM.find (N.of_nat 8781) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8781 inputs path old current result S8304 S8780 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 780 ltac:(do 0 right; left; reflexivity)) as S780.
   apply writer_concrete_ground in S780.
   pose proof (Sources 882 ltac:(do 1 right; left; reflexivity)) as S882.
   apply writer_concrete_ground in S882.
   pose proof (Sources 914 ltac:(do 2 right; left; reflexivity)) as S914.
   apply writer_concrete_ground in S914.
   change (exists ground bits, VM.find (N.of_nat 915) result = Some (Gval ground bits)).
   exact (data_address_node_output_915 inputs path old current result S780 S882 S914 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 781 ltac:(do 0 right; left; reflexivity)) as S781.
   apply writer_concrete_ground in S781.
   pose proof (Sources 882 ltac:(do 1 right; left; reflexivity)) as S882.
   apply writer_concrete_ground in S882.
   pose proof (Sources 949 ltac:(do 2 right; left; reflexivity)) as S949.
   apply writer_concrete_ground in S949.
   change (exists ground bits, VM.find (N.of_nat 950) result = Some (Gval ground bits)).
   exact (data_address_node_output_950 inputs path old current result S781 S882 S949 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8302 ltac:(do 0 right; left; reflexivity)) as S8302.
   apply writer_concrete_ground in S8302.
   pose proof (Sources 8438 ltac:(do 1 right; left; reflexivity)) as S8438.
   apply writer_concrete_ground in S8438.
   change (exists ground bits, VM.find (N.of_nat 8439) result = Some (Gval ground bits)).
   exact (data_address_node_output_8439 inputs path old current result S8302 S8438 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8302 ltac:(do 0 right; left; reflexivity)) as S8302.
   apply writer_concrete_ground in S8302.
   pose proof (Sources 8487 ltac:(do 1 right; left; reflexivity)) as S8487.
   apply writer_concrete_ground in S8487.
   change (exists ground bits, VM.find (N.of_nat 8488) result = Some (Gval ground bits)).
   exact (data_address_node_output_8488 inputs path old current result S8302 S8487 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8302 ltac:(do 0 right; left; reflexivity)) as S8302.
   apply writer_concrete_ground in S8302.
   pose proof (Sources 8536 ltac:(do 1 right; left; reflexivity)) as S8536.
   apply writer_concrete_ground in S8536.
   change (exists ground bits, VM.find (N.of_nat 8537) result = Some (Gval ground bits)).
   exact (data_address_node_output_8537 inputs path old current result S8302 S8536 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8302 ltac:(do 0 right; left; reflexivity)) as S8302.
   apply writer_concrete_ground in S8302.
   pose proof (Sources 8585 ltac:(do 1 right; left; reflexivity)) as S8585.
   apply writer_concrete_ground in S8585.
   change (exists ground bits, VM.find (N.of_nat 8586) result = Some (Gval ground bits)).
   exact (data_address_node_output_8586 inputs path old current result S8302 S8585 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8302 ltac:(do 0 right; left; reflexivity)) as S8302.
   apply writer_concrete_ground in S8302.
   pose proof (Sources 8732 ltac:(do 1 right; left; reflexivity)) as S8732.
   apply writer_concrete_ground in S8732.
   change (exists ground bits, VM.find (N.of_nat 8733) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8733 inputs path old current result S8302 S8732 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8302 ltac:(do 0 right; left; reflexivity)) as S8302.
   apply writer_concrete_ground in S8302.
   pose proof (Sources 8781 ltac:(do 1 right; left; reflexivity)) as S8781.
   apply writer_concrete_ground in S8781.
   change (exists ground bits, VM.find (N.of_nat 8782) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8782 inputs path old current result S8302 S8781 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 915 ltac:(do 0 right; left; reflexivity)) as S915.
   apply writer_concrete_ground in S915.
   change (exists ground bits, VM.find (N.of_nat 916) result = Some (Gval ground bits)).
   exact (data_address_node_output_916 inputs path old current result S915 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 950 ltac:(do 0 right; left; reflexivity)) as S950.
   apply writer_concrete_ground in S950.
   change (exists ground bits, VM.find (N.of_nat 951) result = Some (Gval ground bits)).
   exact (data_address_node_output_951 inputs path old current result S950 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8300 ltac:(do 0 right; left; reflexivity)) as S8300.
   apply writer_concrete_ground in S8300.
   pose proof (Sources 8439 ltac:(do 1 right; left; reflexivity)) as S8439.
   apply writer_concrete_ground in S8439.
   change (exists ground bits, VM.find (N.of_nat 8440) result = Some (Gval ground bits)).
   exact (data_address_node_output_8440 inputs path old current result S8300 S8439 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8300 ltac:(do 0 right; left; reflexivity)) as S8300.
   apply writer_concrete_ground in S8300.
   pose proof (Sources 8488 ltac:(do 1 right; left; reflexivity)) as S8488.
   apply writer_concrete_ground in S8488.
   change (exists ground bits, VM.find (N.of_nat 8489) result = Some (Gval ground bits)).
   exact (data_address_node_output_8489 inputs path old current result S8300 S8488 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8300 ltac:(do 0 right; left; reflexivity)) as S8300.
   apply writer_concrete_ground in S8300.
   pose proof (Sources 8537 ltac:(do 1 right; left; reflexivity)) as S8537.
   apply writer_concrete_ground in S8537.
   change (exists ground bits, VM.find (N.of_nat 8538) result = Some (Gval ground bits)).
   exact (data_address_node_output_8538 inputs path old current result S8300 S8537 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8300 ltac:(do 0 right; left; reflexivity)) as S8300.
   apply writer_concrete_ground in S8300.
   pose proof (Sources 8586 ltac:(do 1 right; left; reflexivity)) as S8586.
   apply writer_concrete_ground in S8586.
   change (exists ground bits, VM.find (N.of_nat 8587) result = Some (Gval ground bits)).
   exact (data_address_node_output_8587 inputs path old current result S8300 S8586 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8300 ltac:(do 0 right; left; reflexivity)) as S8300.
   apply writer_concrete_ground in S8300.
   pose proof (Sources 8733 ltac:(do 1 right; left; reflexivity)) as S8733.
   apply writer_concrete_ground in S8733.
   change (exists ground bits, VM.find (N.of_nat 8734) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8734 inputs path old current result S8300 S8733 Step). }
 constructor.
Qed.
Definition data_writer_chunk_19 : list (nat * (nat * list nat)) := [::(8783,(35,[::8300;8782]));(917,(36,[::883;916]));(952,(36,[::918;951]));(8441,(36,[::8298;8440]));(8490,(36,[::8298;8489]));(8539,(36,[::8298;8538]));(8588,(36,[::8298;8587]));(8735,(36,[::8298;8734]));(8784,(36,[::8298;8783]));(782,(37,[::917]));(783,(37,[::952]));(8442,(37,[::8296;8441]));(8491,(37,[::8296;8490]));(8540,(37,[::8296;8539]));(8589,(37,[::8296;8588]));(8736,(37,[::8296;8735]));(8785,(37,[::8296;8784]));(7816,(38,[::782;7752;7815]));(7819,(38,[::783;7752;7818]));(8443,(38,[::8294;8442]));(8492,(38,[::8294;8491]));(8541,(38,[::8294;8540]));(8590,(38,[::8294;8589]));(8737,(38,[::8294;8736]))].
Lemma data_writer_chunk_19_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_19.
Proof.
 intros Memory Step. unfold data_writer_chunk_19.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8300 ltac:(do 0 right; left; reflexivity)) as S8300.
   apply writer_concrete_ground in S8300.
   pose proof (Sources 8782 ltac:(do 1 right; left; reflexivity)) as S8782.
   apply writer_concrete_ground in S8782.
   change (exists ground bits, VM.find (N.of_nat 8783) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8783 inputs path old current result S8300 S8782 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 883 ltac:(do 0 right; left; reflexivity)) as S883.
   apply writer_concrete_ground in S883.
   pose proof (Sources 916 ltac:(do 1 right; left; reflexivity)) as S916.
   apply writer_concrete_ground in S916.
   change (exists ground bits, VM.find (N.of_nat 917) result = Some (Gval ground bits)).
   exact (data_address_node_output_917 inputs path old current result S883 S916 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 918 ltac:(do 0 right; left; reflexivity)) as S918.
   apply writer_concrete_ground in S918.
   pose proof (Sources 951 ltac:(do 1 right; left; reflexivity)) as S951.
   apply writer_concrete_ground in S951.
   change (exists ground bits, VM.find (N.of_nat 952) result = Some (Gval ground bits)).
   exact (data_address_node_output_952 inputs path old current result S918 S951 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8298 ltac:(do 0 right; left; reflexivity)) as S8298.
   apply writer_concrete_ground in S8298.
   pose proof (Sources 8440 ltac:(do 1 right; left; reflexivity)) as S8440.
   apply writer_concrete_ground in S8440.
   change (exists ground bits, VM.find (N.of_nat 8441) result = Some (Gval ground bits)).
   exact (data_address_node_output_8441 inputs path old current result S8298 S8440 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8298 ltac:(do 0 right; left; reflexivity)) as S8298.
   apply writer_concrete_ground in S8298.
   pose proof (Sources 8489 ltac:(do 1 right; left; reflexivity)) as S8489.
   apply writer_concrete_ground in S8489.
   change (exists ground bits, VM.find (N.of_nat 8490) result = Some (Gval ground bits)).
   exact (data_address_node_output_8490 inputs path old current result S8298 S8489 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8298 ltac:(do 0 right; left; reflexivity)) as S8298.
   apply writer_concrete_ground in S8298.
   pose proof (Sources 8538 ltac:(do 1 right; left; reflexivity)) as S8538.
   apply writer_concrete_ground in S8538.
   change (exists ground bits, VM.find (N.of_nat 8539) result = Some (Gval ground bits)).
   exact (data_address_node_output_8539 inputs path old current result S8298 S8538 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8298 ltac:(do 0 right; left; reflexivity)) as S8298.
   apply writer_concrete_ground in S8298.
   pose proof (Sources 8587 ltac:(do 1 right; left; reflexivity)) as S8587.
   apply writer_concrete_ground in S8587.
   change (exists ground bits, VM.find (N.of_nat 8588) result = Some (Gval ground bits)).
   exact (data_address_node_output_8588 inputs path old current result S8298 S8587 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8298 ltac:(do 0 right; left; reflexivity)) as S8298.
   apply writer_concrete_ground in S8298.
   pose proof (Sources 8734 ltac:(do 1 right; left; reflexivity)) as S8734.
   apply writer_concrete_ground in S8734.
   change (exists ground bits, VM.find (N.of_nat 8735) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8735 inputs path old current result S8298 S8734 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8298 ltac:(do 0 right; left; reflexivity)) as S8298.
   apply writer_concrete_ground in S8298.
   pose proof (Sources 8783 ltac:(do 1 right; left; reflexivity)) as S8783.
   apply writer_concrete_ground in S8783.
   change (exists ground bits, VM.find (N.of_nat 8784) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8784 inputs path old current result S8298 S8783 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 917 ltac:(do 0 right; left; reflexivity)) as S917.
   apply writer_concrete_ground in S917.
   change (exists ground bits, VM.find (N.of_nat 782) result = Some (Gval ground bits)).
   destruct (data_address_connection_782_output (formal_invalid_policy inputs path) old current result S917 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 952 ltac:(do 0 right; left; reflexivity)) as S952.
   apply writer_concrete_ground in S952.
   change (exists ground bits, VM.find (N.of_nat 783) result = Some (Gval ground bits)).
   destruct (data_address_connection_783_output (formal_invalid_policy inputs path) old current result S952 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8296 ltac:(do 0 right; left; reflexivity)) as S8296.
   apply writer_concrete_ground in S8296.
   pose proof (Sources 8441 ltac:(do 1 right; left; reflexivity)) as S8441.
   apply writer_concrete_ground in S8441.
   change (exists ground bits, VM.find (N.of_nat 8442) result = Some (Gval ground bits)).
   exact (data_address_node_output_8442 inputs path old current result S8296 S8441 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8296 ltac:(do 0 right; left; reflexivity)) as S8296.
   apply writer_concrete_ground in S8296.
   pose proof (Sources 8490 ltac:(do 1 right; left; reflexivity)) as S8490.
   apply writer_concrete_ground in S8490.
   change (exists ground bits, VM.find (N.of_nat 8491) result = Some (Gval ground bits)).
   exact (data_address_node_output_8491 inputs path old current result S8296 S8490 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8296 ltac:(do 0 right; left; reflexivity)) as S8296.
   apply writer_concrete_ground in S8296.
   pose proof (Sources 8539 ltac:(do 1 right; left; reflexivity)) as S8539.
   apply writer_concrete_ground in S8539.
   change (exists ground bits, VM.find (N.of_nat 8540) result = Some (Gval ground bits)).
   exact (data_address_node_output_8540 inputs path old current result S8296 S8539 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8296 ltac:(do 0 right; left; reflexivity)) as S8296.
   apply writer_concrete_ground in S8296.
   pose proof (Sources 8588 ltac:(do 1 right; left; reflexivity)) as S8588.
   apply writer_concrete_ground in S8588.
   change (exists ground bits, VM.find (N.of_nat 8589) result = Some (Gval ground bits)).
   exact (data_address_node_output_8589 inputs path old current result S8296 S8588 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8296 ltac:(do 0 right; left; reflexivity)) as S8296.
   apply writer_concrete_ground in S8296.
   pose proof (Sources 8735 ltac:(do 1 right; left; reflexivity)) as S8735.
   apply writer_concrete_ground in S8735.
   change (exists ground bits, VM.find (N.of_nat 8736) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8736 inputs path old current result S8296 S8735 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8296 ltac:(do 0 right; left; reflexivity)) as S8296.
   apply writer_concrete_ground in S8296.
   pose proof (Sources 8784 ltac:(do 1 right; left; reflexivity)) as S8784.
   apply writer_concrete_ground in S8784.
   change (exists ground bits, VM.find (N.of_nat 8785) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8785 inputs path old current result S8296 S8784 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 782 ltac:(do 0 right; left; reflexivity)) as S782.
   apply writer_concrete_ground in S782.
   pose proof (Sources 7752 ltac:(do 1 right; left; reflexivity)) as S7752.
   apply writer_concrete_ground in S7752.
   pose proof (Sources 7815 ltac:(do 2 right; left; reflexivity)) as S7815.
   apply writer_concrete_ground in S7815.
   change (exists ground bits, VM.find (N.of_nat 7816) result = Some (Gval ground bits)).
   exact (data_address_node_output_7816 inputs path old current result S782 S7752 S7815 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 783 ltac:(do 0 right; left; reflexivity)) as S783.
   apply writer_concrete_ground in S783.
   pose proof (Sources 7752 ltac:(do 1 right; left; reflexivity)) as S7752.
   apply writer_concrete_ground in S7752.
   pose proof (Sources 7818 ltac:(do 2 right; left; reflexivity)) as S7818.
   apply writer_concrete_ground in S7818.
   change (exists ground bits, VM.find (N.of_nat 7819) result = Some (Gval ground bits)).
   exact (data_address_node_output_7819 inputs path old current result S783 S7752 S7818 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8294 ltac:(do 0 right; left; reflexivity)) as S8294.
   apply writer_concrete_ground in S8294.
   pose proof (Sources 8442 ltac:(do 1 right; left; reflexivity)) as S8442.
   apply writer_concrete_ground in S8442.
   change (exists ground bits, VM.find (N.of_nat 8443) result = Some (Gval ground bits)).
   exact (data_address_node_output_8443 inputs path old current result S8294 S8442 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8294 ltac:(do 0 right; left; reflexivity)) as S8294.
   apply writer_concrete_ground in S8294.
   pose proof (Sources 8491 ltac:(do 1 right; left; reflexivity)) as S8491.
   apply writer_concrete_ground in S8491.
   change (exists ground bits, VM.find (N.of_nat 8492) result = Some (Gval ground bits)).
   exact (data_address_node_output_8492 inputs path old current result S8294 S8491 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8294 ltac:(do 0 right; left; reflexivity)) as S8294.
   apply writer_concrete_ground in S8294.
   pose proof (Sources 8540 ltac:(do 1 right; left; reflexivity)) as S8540.
   apply writer_concrete_ground in S8540.
   change (exists ground bits, VM.find (N.of_nat 8541) result = Some (Gval ground bits)).
   exact (data_address_node_output_8541 inputs path old current result S8294 S8540 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8294 ltac:(do 0 right; left; reflexivity)) as S8294.
   apply writer_concrete_ground in S8294.
   pose proof (Sources 8589 ltac:(do 1 right; left; reflexivity)) as S8589.
   apply writer_concrete_ground in S8589.
   change (exists ground bits, VM.find (N.of_nat 8590) result = Some (Gval ground bits)).
   exact (data_address_node_output_8590 inputs path old current result S8294 S8589 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8294 ltac:(do 0 right; left; reflexivity)) as S8294.
   apply writer_concrete_ground in S8294.
   pose proof (Sources 8736 ltac:(do 1 right; left; reflexivity)) as S8736.
   apply writer_concrete_ground in S8736.
   change (exists ground bits, VM.find (N.of_nat 8737) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8737 inputs path old current result S8294 S8736 Step). }
 constructor.
Qed.
Definition data_writer_chunk_20 : list (nat * (nat * list nat)) := [::(8786,(38,[::8294;8785]));(8444,(39,[::8292;8443]));(8493,(39,[::8292;8492]));(8542,(39,[::8292;8541]));(8591,(39,[::8292;8590]));(8738,(39,[::8292;8737]));(8787,(39,[::8292;8786]));(8445,(40,[::8290;8444]));(8494,(40,[::8290;8493]));(8543,(40,[::8290;8542]));(8592,(40,[::8290;8591]));(8739,(40,[::8290;8738]));(8788,(40,[::8290;8787]));(8446,(41,[::8288;8445]));(8495,(41,[::8288;8494]));(8544,(41,[::8288;8543]));(8593,(41,[::8288;8592]));(8740,(41,[::8288;8739]));(8789,(41,[::8288;8788]));(8447,(42,[::8286;8446]));(8496,(42,[::8286;8495]));(8545,(42,[::8286;8544]));(8594,(42,[::8286;8593]));(8741,(42,[::8286;8740]))].
Lemma data_writer_chunk_20_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_20.
Proof.
 intros Memory Step. unfold data_writer_chunk_20.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8294 ltac:(do 0 right; left; reflexivity)) as S8294.
   apply writer_concrete_ground in S8294.
   pose proof (Sources 8785 ltac:(do 1 right; left; reflexivity)) as S8785.
   apply writer_concrete_ground in S8785.
   change (exists ground bits, VM.find (N.of_nat 8786) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8786 inputs path old current result S8294 S8785 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8292 ltac:(do 0 right; left; reflexivity)) as S8292.
   apply writer_concrete_ground in S8292.
   pose proof (Sources 8443 ltac:(do 1 right; left; reflexivity)) as S8443.
   apply writer_concrete_ground in S8443.
   change (exists ground bits, VM.find (N.of_nat 8444) result = Some (Gval ground bits)).
   exact (data_address_node_output_8444 inputs path old current result S8292 S8443 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8292 ltac:(do 0 right; left; reflexivity)) as S8292.
   apply writer_concrete_ground in S8292.
   pose proof (Sources 8492 ltac:(do 1 right; left; reflexivity)) as S8492.
   apply writer_concrete_ground in S8492.
   change (exists ground bits, VM.find (N.of_nat 8493) result = Some (Gval ground bits)).
   exact (data_address_node_output_8493 inputs path old current result S8292 S8492 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8292 ltac:(do 0 right; left; reflexivity)) as S8292.
   apply writer_concrete_ground in S8292.
   pose proof (Sources 8541 ltac:(do 1 right; left; reflexivity)) as S8541.
   apply writer_concrete_ground in S8541.
   change (exists ground bits, VM.find (N.of_nat 8542) result = Some (Gval ground bits)).
   exact (data_address_node_output_8542 inputs path old current result S8292 S8541 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8292 ltac:(do 0 right; left; reflexivity)) as S8292.
   apply writer_concrete_ground in S8292.
   pose proof (Sources 8590 ltac:(do 1 right; left; reflexivity)) as S8590.
   apply writer_concrete_ground in S8590.
   change (exists ground bits, VM.find (N.of_nat 8591) result = Some (Gval ground bits)).
   exact (data_address_node_output_8591 inputs path old current result S8292 S8590 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8292 ltac:(do 0 right; left; reflexivity)) as S8292.
   apply writer_concrete_ground in S8292.
   pose proof (Sources 8737 ltac:(do 1 right; left; reflexivity)) as S8737.
   apply writer_concrete_ground in S8737.
   change (exists ground bits, VM.find (N.of_nat 8738) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8738 inputs path old current result S8292 S8737 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8292 ltac:(do 0 right; left; reflexivity)) as S8292.
   apply writer_concrete_ground in S8292.
   pose proof (Sources 8786 ltac:(do 1 right; left; reflexivity)) as S8786.
   apply writer_concrete_ground in S8786.
   change (exists ground bits, VM.find (N.of_nat 8787) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8787 inputs path old current result S8292 S8786 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8290 ltac:(do 0 right; left; reflexivity)) as S8290.
   apply writer_concrete_ground in S8290.
   pose proof (Sources 8444 ltac:(do 1 right; left; reflexivity)) as S8444.
   apply writer_concrete_ground in S8444.
   change (exists ground bits, VM.find (N.of_nat 8445) result = Some (Gval ground bits)).
   exact (data_address_node_output_8445 inputs path old current result S8290 S8444 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8290 ltac:(do 0 right; left; reflexivity)) as S8290.
   apply writer_concrete_ground in S8290.
   pose proof (Sources 8493 ltac:(do 1 right; left; reflexivity)) as S8493.
   apply writer_concrete_ground in S8493.
   change (exists ground bits, VM.find (N.of_nat 8494) result = Some (Gval ground bits)).
   exact (data_address_node_output_8494 inputs path old current result S8290 S8493 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8290 ltac:(do 0 right; left; reflexivity)) as S8290.
   apply writer_concrete_ground in S8290.
   pose proof (Sources 8542 ltac:(do 1 right; left; reflexivity)) as S8542.
   apply writer_concrete_ground in S8542.
   change (exists ground bits, VM.find (N.of_nat 8543) result = Some (Gval ground bits)).
   exact (data_address_node_output_8543 inputs path old current result S8290 S8542 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8290 ltac:(do 0 right; left; reflexivity)) as S8290.
   apply writer_concrete_ground in S8290.
   pose proof (Sources 8591 ltac:(do 1 right; left; reflexivity)) as S8591.
   apply writer_concrete_ground in S8591.
   change (exists ground bits, VM.find (N.of_nat 8592) result = Some (Gval ground bits)).
   exact (data_address_node_output_8592 inputs path old current result S8290 S8591 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8290 ltac:(do 0 right; left; reflexivity)) as S8290.
   apply writer_concrete_ground in S8290.
   pose proof (Sources 8738 ltac:(do 1 right; left; reflexivity)) as S8738.
   apply writer_concrete_ground in S8738.
   change (exists ground bits, VM.find (N.of_nat 8739) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8739 inputs path old current result S8290 S8738 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8290 ltac:(do 0 right; left; reflexivity)) as S8290.
   apply writer_concrete_ground in S8290.
   pose proof (Sources 8787 ltac:(do 1 right; left; reflexivity)) as S8787.
   apply writer_concrete_ground in S8787.
   change (exists ground bits, VM.find (N.of_nat 8788) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8788 inputs path old current result S8290 S8787 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8288 ltac:(do 0 right; left; reflexivity)) as S8288.
   apply writer_concrete_ground in S8288.
   pose proof (Sources 8445 ltac:(do 1 right; left; reflexivity)) as S8445.
   apply writer_concrete_ground in S8445.
   change (exists ground bits, VM.find (N.of_nat 8446) result = Some (Gval ground bits)).
   exact (data_address_node_output_8446 inputs path old current result S8288 S8445 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8288 ltac:(do 0 right; left; reflexivity)) as S8288.
   apply writer_concrete_ground in S8288.
   pose proof (Sources 8494 ltac:(do 1 right; left; reflexivity)) as S8494.
   apply writer_concrete_ground in S8494.
   change (exists ground bits, VM.find (N.of_nat 8495) result = Some (Gval ground bits)).
   exact (data_address_node_output_8495 inputs path old current result S8288 S8494 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8288 ltac:(do 0 right; left; reflexivity)) as S8288.
   apply writer_concrete_ground in S8288.
   pose proof (Sources 8543 ltac:(do 1 right; left; reflexivity)) as S8543.
   apply writer_concrete_ground in S8543.
   change (exists ground bits, VM.find (N.of_nat 8544) result = Some (Gval ground bits)).
   exact (data_address_node_output_8544 inputs path old current result S8288 S8543 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8288 ltac:(do 0 right; left; reflexivity)) as S8288.
   apply writer_concrete_ground in S8288.
   pose proof (Sources 8592 ltac:(do 1 right; left; reflexivity)) as S8592.
   apply writer_concrete_ground in S8592.
   change (exists ground bits, VM.find (N.of_nat 8593) result = Some (Gval ground bits)).
   exact (data_address_node_output_8593 inputs path old current result S8288 S8592 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8288 ltac:(do 0 right; left; reflexivity)) as S8288.
   apply writer_concrete_ground in S8288.
   pose proof (Sources 8739 ltac:(do 1 right; left; reflexivity)) as S8739.
   apply writer_concrete_ground in S8739.
   change (exists ground bits, VM.find (N.of_nat 8740) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8740 inputs path old current result S8288 S8739 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8288 ltac:(do 0 right; left; reflexivity)) as S8288.
   apply writer_concrete_ground in S8288.
   pose proof (Sources 8788 ltac:(do 1 right; left; reflexivity)) as S8788.
   apply writer_concrete_ground in S8788.
   change (exists ground bits, VM.find (N.of_nat 8789) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8789 inputs path old current result S8288 S8788 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8286 ltac:(do 0 right; left; reflexivity)) as S8286.
   apply writer_concrete_ground in S8286.
   pose proof (Sources 8446 ltac:(do 1 right; left; reflexivity)) as S8446.
   apply writer_concrete_ground in S8446.
   change (exists ground bits, VM.find (N.of_nat 8447) result = Some (Gval ground bits)).
   exact (data_address_node_output_8447 inputs path old current result S8286 S8446 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8286 ltac:(do 0 right; left; reflexivity)) as S8286.
   apply writer_concrete_ground in S8286.
   pose proof (Sources 8495 ltac:(do 1 right; left; reflexivity)) as S8495.
   apply writer_concrete_ground in S8495.
   change (exists ground bits, VM.find (N.of_nat 8496) result = Some (Gval ground bits)).
   exact (data_address_node_output_8496 inputs path old current result S8286 S8495 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8286 ltac:(do 0 right; left; reflexivity)) as S8286.
   apply writer_concrete_ground in S8286.
   pose proof (Sources 8544 ltac:(do 1 right; left; reflexivity)) as S8544.
   apply writer_concrete_ground in S8544.
   change (exists ground bits, VM.find (N.of_nat 8545) result = Some (Gval ground bits)).
   exact (data_address_node_output_8545 inputs path old current result S8286 S8544 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8286 ltac:(do 0 right; left; reflexivity)) as S8286.
   apply writer_concrete_ground in S8286.
   pose proof (Sources 8593 ltac:(do 1 right; left; reflexivity)) as S8593.
   apply writer_concrete_ground in S8593.
   change (exists ground bits, VM.find (N.of_nat 8594) result = Some (Gval ground bits)).
   exact (data_address_node_output_8594 inputs path old current result S8286 S8593 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8286 ltac:(do 0 right; left; reflexivity)) as S8286.
   apply writer_concrete_ground in S8286.
   pose proof (Sources 8740 ltac:(do 1 right; left; reflexivity)) as S8740.
   apply writer_concrete_ground in S8740.
   change (exists ground bits, VM.find (N.of_nat 8741) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8741 inputs path old current result S8286 S8740 Step). }
 constructor.
Qed.
Definition data_writer_chunk_21 : list (nat * (nat * list nat)) := [::(8790,(42,[::8286;8789]));(8448,(43,[::8284;8447]));(8497,(43,[::8284;8496]));(8546,(43,[::8284;8545]));(8595,(43,[::8284;8594]));(8742,(43,[::8284;8741]));(8791,(43,[::8284;8790]));(8449,(44,[::8282;8448]));(8498,(44,[::8282;8497]));(8547,(44,[::8282;8546]));(8596,(44,[::8282;8595]));(8743,(44,[::8282;8742]));(8792,(44,[::8282;8791]));(8450,(45,[::8280;8449]));(8499,(45,[::8280;8498]));(8548,(45,[::8280;8547]));(8597,(45,[::8280;8596]));(8744,(45,[::8280;8743]));(8793,(45,[::8280;8792]));(8451,(46,[::8278;8450]));(8500,(46,[::8278;8499]));(8549,(46,[::8278;8548]));(8598,(46,[::8278;8597]));(8745,(46,[::8278;8744]))].
Lemma data_writer_chunk_21_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_21.
Proof.
 intros Memory Step. unfold data_writer_chunk_21.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8286 ltac:(do 0 right; left; reflexivity)) as S8286.
   apply writer_concrete_ground in S8286.
   pose proof (Sources 8789 ltac:(do 1 right; left; reflexivity)) as S8789.
   apply writer_concrete_ground in S8789.
   change (exists ground bits, VM.find (N.of_nat 8790) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8790 inputs path old current result S8286 S8789 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8284 ltac:(do 0 right; left; reflexivity)) as S8284.
   apply writer_concrete_ground in S8284.
   pose proof (Sources 8447 ltac:(do 1 right; left; reflexivity)) as S8447.
   apply writer_concrete_ground in S8447.
   change (exists ground bits, VM.find (N.of_nat 8448) result = Some (Gval ground bits)).
   exact (data_address_node_output_8448 inputs path old current result S8284 S8447 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8284 ltac:(do 0 right; left; reflexivity)) as S8284.
   apply writer_concrete_ground in S8284.
   pose proof (Sources 8496 ltac:(do 1 right; left; reflexivity)) as S8496.
   apply writer_concrete_ground in S8496.
   change (exists ground bits, VM.find (N.of_nat 8497) result = Some (Gval ground bits)).
   exact (data_address_node_output_8497 inputs path old current result S8284 S8496 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8284 ltac:(do 0 right; left; reflexivity)) as S8284.
   apply writer_concrete_ground in S8284.
   pose proof (Sources 8545 ltac:(do 1 right; left; reflexivity)) as S8545.
   apply writer_concrete_ground in S8545.
   change (exists ground bits, VM.find (N.of_nat 8546) result = Some (Gval ground bits)).
   exact (data_address_node_output_8546 inputs path old current result S8284 S8545 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8284 ltac:(do 0 right; left; reflexivity)) as S8284.
   apply writer_concrete_ground in S8284.
   pose proof (Sources 8594 ltac:(do 1 right; left; reflexivity)) as S8594.
   apply writer_concrete_ground in S8594.
   change (exists ground bits, VM.find (N.of_nat 8595) result = Some (Gval ground bits)).
   exact (data_address_node_output_8595 inputs path old current result S8284 S8594 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8284 ltac:(do 0 right; left; reflexivity)) as S8284.
   apply writer_concrete_ground in S8284.
   pose proof (Sources 8741 ltac:(do 1 right; left; reflexivity)) as S8741.
   apply writer_concrete_ground in S8741.
   change (exists ground bits, VM.find (N.of_nat 8742) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8742 inputs path old current result S8284 S8741 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8284 ltac:(do 0 right; left; reflexivity)) as S8284.
   apply writer_concrete_ground in S8284.
   pose proof (Sources 8790 ltac:(do 1 right; left; reflexivity)) as S8790.
   apply writer_concrete_ground in S8790.
   change (exists ground bits, VM.find (N.of_nat 8791) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8791 inputs path old current result S8284 S8790 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8282 ltac:(do 0 right; left; reflexivity)) as S8282.
   apply writer_concrete_ground in S8282.
   pose proof (Sources 8448 ltac:(do 1 right; left; reflexivity)) as S8448.
   apply writer_concrete_ground in S8448.
   change (exists ground bits, VM.find (N.of_nat 8449) result = Some (Gval ground bits)).
   exact (data_address_node_output_8449 inputs path old current result S8282 S8448 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8282 ltac:(do 0 right; left; reflexivity)) as S8282.
   apply writer_concrete_ground in S8282.
   pose proof (Sources 8497 ltac:(do 1 right; left; reflexivity)) as S8497.
   apply writer_concrete_ground in S8497.
   change (exists ground bits, VM.find (N.of_nat 8498) result = Some (Gval ground bits)).
   exact (data_address_node_output_8498 inputs path old current result S8282 S8497 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8282 ltac:(do 0 right; left; reflexivity)) as S8282.
   apply writer_concrete_ground in S8282.
   pose proof (Sources 8546 ltac:(do 1 right; left; reflexivity)) as S8546.
   apply writer_concrete_ground in S8546.
   change (exists ground bits, VM.find (N.of_nat 8547) result = Some (Gval ground bits)).
   exact (data_address_node_output_8547 inputs path old current result S8282 S8546 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8282 ltac:(do 0 right; left; reflexivity)) as S8282.
   apply writer_concrete_ground in S8282.
   pose proof (Sources 8595 ltac:(do 1 right; left; reflexivity)) as S8595.
   apply writer_concrete_ground in S8595.
   change (exists ground bits, VM.find (N.of_nat 8596) result = Some (Gval ground bits)).
   exact (data_address_node_output_8596 inputs path old current result S8282 S8595 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8282 ltac:(do 0 right; left; reflexivity)) as S8282.
   apply writer_concrete_ground in S8282.
   pose proof (Sources 8742 ltac:(do 1 right; left; reflexivity)) as S8742.
   apply writer_concrete_ground in S8742.
   change (exists ground bits, VM.find (N.of_nat 8743) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8743 inputs path old current result S8282 S8742 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8282 ltac:(do 0 right; left; reflexivity)) as S8282.
   apply writer_concrete_ground in S8282.
   pose proof (Sources 8791 ltac:(do 1 right; left; reflexivity)) as S8791.
   apply writer_concrete_ground in S8791.
   change (exists ground bits, VM.find (N.of_nat 8792) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8792 inputs path old current result S8282 S8791 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8280 ltac:(do 0 right; left; reflexivity)) as S8280.
   apply writer_concrete_ground in S8280.
   pose proof (Sources 8449 ltac:(do 1 right; left; reflexivity)) as S8449.
   apply writer_concrete_ground in S8449.
   change (exists ground bits, VM.find (N.of_nat 8450) result = Some (Gval ground bits)).
   exact (data_address_node_output_8450 inputs path old current result S8280 S8449 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8280 ltac:(do 0 right; left; reflexivity)) as S8280.
   apply writer_concrete_ground in S8280.
   pose proof (Sources 8498 ltac:(do 1 right; left; reflexivity)) as S8498.
   apply writer_concrete_ground in S8498.
   change (exists ground bits, VM.find (N.of_nat 8499) result = Some (Gval ground bits)).
   exact (data_address_node_output_8499 inputs path old current result S8280 S8498 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8280 ltac:(do 0 right; left; reflexivity)) as S8280.
   apply writer_concrete_ground in S8280.
   pose proof (Sources 8547 ltac:(do 1 right; left; reflexivity)) as S8547.
   apply writer_concrete_ground in S8547.
   change (exists ground bits, VM.find (N.of_nat 8548) result = Some (Gval ground bits)).
   exact (data_address_node_output_8548 inputs path old current result S8280 S8547 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8280 ltac:(do 0 right; left; reflexivity)) as S8280.
   apply writer_concrete_ground in S8280.
   pose proof (Sources 8596 ltac:(do 1 right; left; reflexivity)) as S8596.
   apply writer_concrete_ground in S8596.
   change (exists ground bits, VM.find (N.of_nat 8597) result = Some (Gval ground bits)).
   exact (data_address_node_output_8597 inputs path old current result S8280 S8596 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8280 ltac:(do 0 right; left; reflexivity)) as S8280.
   apply writer_concrete_ground in S8280.
   pose proof (Sources 8743 ltac:(do 1 right; left; reflexivity)) as S8743.
   apply writer_concrete_ground in S8743.
   change (exists ground bits, VM.find (N.of_nat 8744) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8744 inputs path old current result S8280 S8743 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8280 ltac:(do 0 right; left; reflexivity)) as S8280.
   apply writer_concrete_ground in S8280.
   pose proof (Sources 8792 ltac:(do 1 right; left; reflexivity)) as S8792.
   apply writer_concrete_ground in S8792.
   change (exists ground bits, VM.find (N.of_nat 8793) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8793 inputs path old current result S8280 S8792 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8278 ltac:(do 0 right; left; reflexivity)) as S8278.
   apply writer_concrete_ground in S8278.
   pose proof (Sources 8450 ltac:(do 1 right; left; reflexivity)) as S8450.
   apply writer_concrete_ground in S8450.
   change (exists ground bits, VM.find (N.of_nat 8451) result = Some (Gval ground bits)).
   exact (data_address_node_output_8451 inputs path old current result S8278 S8450 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8278 ltac:(do 0 right; left; reflexivity)) as S8278.
   apply writer_concrete_ground in S8278.
   pose proof (Sources 8499 ltac:(do 1 right; left; reflexivity)) as S8499.
   apply writer_concrete_ground in S8499.
   change (exists ground bits, VM.find (N.of_nat 8500) result = Some (Gval ground bits)).
   exact (data_address_node_output_8500 inputs path old current result S8278 S8499 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8278 ltac:(do 0 right; left; reflexivity)) as S8278.
   apply writer_concrete_ground in S8278.
   pose proof (Sources 8548 ltac:(do 1 right; left; reflexivity)) as S8548.
   apply writer_concrete_ground in S8548.
   change (exists ground bits, VM.find (N.of_nat 8549) result = Some (Gval ground bits)).
   exact (data_address_node_output_8549 inputs path old current result S8278 S8548 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8278 ltac:(do 0 right; left; reflexivity)) as S8278.
   apply writer_concrete_ground in S8278.
   pose proof (Sources 8597 ltac:(do 1 right; left; reflexivity)) as S8597.
   apply writer_concrete_ground in S8597.
   change (exists ground bits, VM.find (N.of_nat 8598) result = Some (Gval ground bits)).
   exact (data_address_node_output_8598 inputs path old current result S8278 S8597 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8278 ltac:(do 0 right; left; reflexivity)) as S8278.
   apply writer_concrete_ground in S8278.
   pose proof (Sources 8744 ltac:(do 1 right; left; reflexivity)) as S8744.
   apply writer_concrete_ground in S8744.
   change (exists ground bits, VM.find (N.of_nat 8745) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8745 inputs path old current result S8278 S8744 Step). }
 constructor.
Qed.
Definition data_writer_chunk_22 : list (nat * (nat * list nat)) := [::(8794,(46,[::8278;8793]));(8452,(47,[::8276;8451]));(8501,(47,[::8276;8500]));(8550,(47,[::8276;8549]));(8599,(47,[::8276;8598]));(8746,(47,[::8276;8745]));(8795,(47,[::8276;8794]));(8453,(48,[::8274;8452]));(8502,(48,[::8274;8501]));(8551,(48,[::8274;8550]));(8600,(48,[::8274;8599]));(8747,(48,[::8274;8746]));(8796,(48,[::8274;8795]));(8454,(49,[::8272;8453]));(8503,(49,[::8272;8502]));(8552,(49,[::8272;8551]));(8601,(49,[::8272;8600]));(8748,(49,[::8272;8747]));(8797,(49,[::8272;8796]));(8455,(50,[::8270;8454]));(8504,(50,[::8270;8503]));(8553,(50,[::8270;8552]));(8602,(50,[::8270;8601]));(8749,(50,[::8270;8748]))].
Lemma data_writer_chunk_22_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_22.
Proof.
 intros Memory Step. unfold data_writer_chunk_22.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8278 ltac:(do 0 right; left; reflexivity)) as S8278.
   apply writer_concrete_ground in S8278.
   pose proof (Sources 8793 ltac:(do 1 right; left; reflexivity)) as S8793.
   apply writer_concrete_ground in S8793.
   change (exists ground bits, VM.find (N.of_nat 8794) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8794 inputs path old current result S8278 S8793 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8276 ltac:(do 0 right; left; reflexivity)) as S8276.
   apply writer_concrete_ground in S8276.
   pose proof (Sources 8451 ltac:(do 1 right; left; reflexivity)) as S8451.
   apply writer_concrete_ground in S8451.
   change (exists ground bits, VM.find (N.of_nat 8452) result = Some (Gval ground bits)).
   exact (data_address_node_output_8452 inputs path old current result S8276 S8451 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8276 ltac:(do 0 right; left; reflexivity)) as S8276.
   apply writer_concrete_ground in S8276.
   pose proof (Sources 8500 ltac:(do 1 right; left; reflexivity)) as S8500.
   apply writer_concrete_ground in S8500.
   change (exists ground bits, VM.find (N.of_nat 8501) result = Some (Gval ground bits)).
   exact (data_address_node_output_8501 inputs path old current result S8276 S8500 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8276 ltac:(do 0 right; left; reflexivity)) as S8276.
   apply writer_concrete_ground in S8276.
   pose proof (Sources 8549 ltac:(do 1 right; left; reflexivity)) as S8549.
   apply writer_concrete_ground in S8549.
   change (exists ground bits, VM.find (N.of_nat 8550) result = Some (Gval ground bits)).
   exact (data_address_node_output_8550 inputs path old current result S8276 S8549 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8276 ltac:(do 0 right; left; reflexivity)) as S8276.
   apply writer_concrete_ground in S8276.
   pose proof (Sources 8598 ltac:(do 1 right; left; reflexivity)) as S8598.
   apply writer_concrete_ground in S8598.
   change (exists ground bits, VM.find (N.of_nat 8599) result = Some (Gval ground bits)).
   exact (data_address_node_output_8599 inputs path old current result S8276 S8598 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8276 ltac:(do 0 right; left; reflexivity)) as S8276.
   apply writer_concrete_ground in S8276.
   pose proof (Sources 8745 ltac:(do 1 right; left; reflexivity)) as S8745.
   apply writer_concrete_ground in S8745.
   change (exists ground bits, VM.find (N.of_nat 8746) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8746 inputs path old current result S8276 S8745 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8276 ltac:(do 0 right; left; reflexivity)) as S8276.
   apply writer_concrete_ground in S8276.
   pose proof (Sources 8794 ltac:(do 1 right; left; reflexivity)) as S8794.
   apply writer_concrete_ground in S8794.
   change (exists ground bits, VM.find (N.of_nat 8795) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8795 inputs path old current result S8276 S8794 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8274 ltac:(do 0 right; left; reflexivity)) as S8274.
   apply writer_concrete_ground in S8274.
   pose proof (Sources 8452 ltac:(do 1 right; left; reflexivity)) as S8452.
   apply writer_concrete_ground in S8452.
   change (exists ground bits, VM.find (N.of_nat 8453) result = Some (Gval ground bits)).
   exact (data_address_node_output_8453 inputs path old current result S8274 S8452 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8274 ltac:(do 0 right; left; reflexivity)) as S8274.
   apply writer_concrete_ground in S8274.
   pose proof (Sources 8501 ltac:(do 1 right; left; reflexivity)) as S8501.
   apply writer_concrete_ground in S8501.
   change (exists ground bits, VM.find (N.of_nat 8502) result = Some (Gval ground bits)).
   exact (data_address_node_output_8502 inputs path old current result S8274 S8501 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8274 ltac:(do 0 right; left; reflexivity)) as S8274.
   apply writer_concrete_ground in S8274.
   pose proof (Sources 8550 ltac:(do 1 right; left; reflexivity)) as S8550.
   apply writer_concrete_ground in S8550.
   change (exists ground bits, VM.find (N.of_nat 8551) result = Some (Gval ground bits)).
   exact (data_address_node_output_8551 inputs path old current result S8274 S8550 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8274 ltac:(do 0 right; left; reflexivity)) as S8274.
   apply writer_concrete_ground in S8274.
   pose proof (Sources 8599 ltac:(do 1 right; left; reflexivity)) as S8599.
   apply writer_concrete_ground in S8599.
   change (exists ground bits, VM.find (N.of_nat 8600) result = Some (Gval ground bits)).
   exact (data_address_node_output_8600 inputs path old current result S8274 S8599 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8274 ltac:(do 0 right; left; reflexivity)) as S8274.
   apply writer_concrete_ground in S8274.
   pose proof (Sources 8746 ltac:(do 1 right; left; reflexivity)) as S8746.
   apply writer_concrete_ground in S8746.
   change (exists ground bits, VM.find (N.of_nat 8747) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8747 inputs path old current result S8274 S8746 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8274 ltac:(do 0 right; left; reflexivity)) as S8274.
   apply writer_concrete_ground in S8274.
   pose proof (Sources 8795 ltac:(do 1 right; left; reflexivity)) as S8795.
   apply writer_concrete_ground in S8795.
   change (exists ground bits, VM.find (N.of_nat 8796) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8796 inputs path old current result S8274 S8795 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8272 ltac:(do 0 right; left; reflexivity)) as S8272.
   apply writer_concrete_ground in S8272.
   pose proof (Sources 8453 ltac:(do 1 right; left; reflexivity)) as S8453.
   apply writer_concrete_ground in S8453.
   change (exists ground bits, VM.find (N.of_nat 8454) result = Some (Gval ground bits)).
   exact (data_address_node_output_8454 inputs path old current result S8272 S8453 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8272 ltac:(do 0 right; left; reflexivity)) as S8272.
   apply writer_concrete_ground in S8272.
   pose proof (Sources 8502 ltac:(do 1 right; left; reflexivity)) as S8502.
   apply writer_concrete_ground in S8502.
   change (exists ground bits, VM.find (N.of_nat 8503) result = Some (Gval ground bits)).
   exact (data_address_node_output_8503 inputs path old current result S8272 S8502 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8272 ltac:(do 0 right; left; reflexivity)) as S8272.
   apply writer_concrete_ground in S8272.
   pose proof (Sources 8551 ltac:(do 1 right; left; reflexivity)) as S8551.
   apply writer_concrete_ground in S8551.
   change (exists ground bits, VM.find (N.of_nat 8552) result = Some (Gval ground bits)).
   exact (data_address_node_output_8552 inputs path old current result S8272 S8551 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8272 ltac:(do 0 right; left; reflexivity)) as S8272.
   apply writer_concrete_ground in S8272.
   pose proof (Sources 8600 ltac:(do 1 right; left; reflexivity)) as S8600.
   apply writer_concrete_ground in S8600.
   change (exists ground bits, VM.find (N.of_nat 8601) result = Some (Gval ground bits)).
   exact (data_address_node_output_8601 inputs path old current result S8272 S8600 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8272 ltac:(do 0 right; left; reflexivity)) as S8272.
   apply writer_concrete_ground in S8272.
   pose proof (Sources 8747 ltac:(do 1 right; left; reflexivity)) as S8747.
   apply writer_concrete_ground in S8747.
   change (exists ground bits, VM.find (N.of_nat 8748) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8748 inputs path old current result S8272 S8747 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8272 ltac:(do 0 right; left; reflexivity)) as S8272.
   apply writer_concrete_ground in S8272.
   pose proof (Sources 8796 ltac:(do 1 right; left; reflexivity)) as S8796.
   apply writer_concrete_ground in S8796.
   change (exists ground bits, VM.find (N.of_nat 8797) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8797 inputs path old current result S8272 S8796 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8270 ltac:(do 0 right; left; reflexivity)) as S8270.
   apply writer_concrete_ground in S8270.
   pose proof (Sources 8454 ltac:(do 1 right; left; reflexivity)) as S8454.
   apply writer_concrete_ground in S8454.
   change (exists ground bits, VM.find (N.of_nat 8455) result = Some (Gval ground bits)).
   exact (data_address_node_output_8455 inputs path old current result S8270 S8454 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8270 ltac:(do 0 right; left; reflexivity)) as S8270.
   apply writer_concrete_ground in S8270.
   pose proof (Sources 8503 ltac:(do 1 right; left; reflexivity)) as S8503.
   apply writer_concrete_ground in S8503.
   change (exists ground bits, VM.find (N.of_nat 8504) result = Some (Gval ground bits)).
   exact (data_address_node_output_8504 inputs path old current result S8270 S8503 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8270 ltac:(do 0 right; left; reflexivity)) as S8270.
   apply writer_concrete_ground in S8270.
   pose proof (Sources 8552 ltac:(do 1 right; left; reflexivity)) as S8552.
   apply writer_concrete_ground in S8552.
   change (exists ground bits, VM.find (N.of_nat 8553) result = Some (Gval ground bits)).
   exact (data_address_node_output_8553 inputs path old current result S8270 S8552 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8270 ltac:(do 0 right; left; reflexivity)) as S8270.
   apply writer_concrete_ground in S8270.
   pose proof (Sources 8601 ltac:(do 1 right; left; reflexivity)) as S8601.
   apply writer_concrete_ground in S8601.
   change (exists ground bits, VM.find (N.of_nat 8602) result = Some (Gval ground bits)).
   exact (data_address_node_output_8602 inputs path old current result S8270 S8601 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8270 ltac:(do 0 right; left; reflexivity)) as S8270.
   apply writer_concrete_ground in S8270.
   pose proof (Sources 8748 ltac:(do 1 right; left; reflexivity)) as S8748.
   apply writer_concrete_ground in S8748.
   change (exists ground bits, VM.find (N.of_nat 8749) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8749 inputs path old current result S8270 S8748 Step). }
 constructor.
Qed.
Definition data_writer_chunk_23 : list (nat * (nat * list nat)) := [::(8798,(50,[::8270;8797]));(8456,(51,[::8268;8455]));(8505,(51,[::8268;8504]));(8554,(51,[::8268;8553]));(8603,(51,[::8268;8602]));(8750,(51,[::8268;8749]));(8799,(51,[::8268;8798]));(8457,(52,[::8266;8456]));(8506,(52,[::8266;8505]));(8555,(52,[::8266;8554]));(8604,(52,[::8266;8603]));(8751,(52,[::8266;8750]));(8800,(52,[::8266;8799]));(8458,(53,[::8264;8457]));(8507,(53,[::8264;8506]));(8556,(53,[::8264;8555]));(8605,(53,[::8264;8604]));(8752,(53,[::8264;8751]));(8801,(53,[::8264;8800]));(8252,(54,[::8458]));(8253,(54,[::8507]));(8254,(54,[::8556]));(8255,(54,[::8605]));(8257,(54,[::8752]))].
Lemma data_writer_chunk_23_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_23.
Proof.
 intros Memory Step. unfold data_writer_chunk_23.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8270 ltac:(do 0 right; left; reflexivity)) as S8270.
   apply writer_concrete_ground in S8270.
   pose proof (Sources 8797 ltac:(do 1 right; left; reflexivity)) as S8797.
   apply writer_concrete_ground in S8797.
   change (exists ground bits, VM.find (N.of_nat 8798) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8798 inputs path old current result S8270 S8797 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8268 ltac:(do 0 right; left; reflexivity)) as S8268.
   apply writer_concrete_ground in S8268.
   pose proof (Sources 8455 ltac:(do 1 right; left; reflexivity)) as S8455.
   apply writer_concrete_ground in S8455.
   change (exists ground bits, VM.find (N.of_nat 8456) result = Some (Gval ground bits)).
   exact (data_address_node_output_8456 inputs path old current result S8268 S8455 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8268 ltac:(do 0 right; left; reflexivity)) as S8268.
   apply writer_concrete_ground in S8268.
   pose proof (Sources 8504 ltac:(do 1 right; left; reflexivity)) as S8504.
   apply writer_concrete_ground in S8504.
   change (exists ground bits, VM.find (N.of_nat 8505) result = Some (Gval ground bits)).
   exact (data_address_node_output_8505 inputs path old current result S8268 S8504 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8268 ltac:(do 0 right; left; reflexivity)) as S8268.
   apply writer_concrete_ground in S8268.
   pose proof (Sources 8553 ltac:(do 1 right; left; reflexivity)) as S8553.
   apply writer_concrete_ground in S8553.
   change (exists ground bits, VM.find (N.of_nat 8554) result = Some (Gval ground bits)).
   exact (data_address_node_output_8554 inputs path old current result S8268 S8553 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8268 ltac:(do 0 right; left; reflexivity)) as S8268.
   apply writer_concrete_ground in S8268.
   pose proof (Sources 8602 ltac:(do 1 right; left; reflexivity)) as S8602.
   apply writer_concrete_ground in S8602.
   change (exists ground bits, VM.find (N.of_nat 8603) result = Some (Gval ground bits)).
   exact (data_address_node_output_8603 inputs path old current result S8268 S8602 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8268 ltac:(do 0 right; left; reflexivity)) as S8268.
   apply writer_concrete_ground in S8268.
   pose proof (Sources 8749 ltac:(do 1 right; left; reflexivity)) as S8749.
   apply writer_concrete_ground in S8749.
   change (exists ground bits, VM.find (N.of_nat 8750) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8750 inputs path old current result S8268 S8749 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8268 ltac:(do 0 right; left; reflexivity)) as S8268.
   apply writer_concrete_ground in S8268.
   pose proof (Sources 8798 ltac:(do 1 right; left; reflexivity)) as S8798.
   apply writer_concrete_ground in S8798.
   change (exists ground bits, VM.find (N.of_nat 8799) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8799 inputs path old current result S8268 S8798 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8266 ltac:(do 0 right; left; reflexivity)) as S8266.
   apply writer_concrete_ground in S8266.
   pose proof (Sources 8456 ltac:(do 1 right; left; reflexivity)) as S8456.
   apply writer_concrete_ground in S8456.
   change (exists ground bits, VM.find (N.of_nat 8457) result = Some (Gval ground bits)).
   exact (data_address_node_output_8457 inputs path old current result S8266 S8456 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8266 ltac:(do 0 right; left; reflexivity)) as S8266.
   apply writer_concrete_ground in S8266.
   pose proof (Sources 8505 ltac:(do 1 right; left; reflexivity)) as S8505.
   apply writer_concrete_ground in S8505.
   change (exists ground bits, VM.find (N.of_nat 8506) result = Some (Gval ground bits)).
   exact (data_address_node_output_8506 inputs path old current result S8266 S8505 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8266 ltac:(do 0 right; left; reflexivity)) as S8266.
   apply writer_concrete_ground in S8266.
   pose proof (Sources 8554 ltac:(do 1 right; left; reflexivity)) as S8554.
   apply writer_concrete_ground in S8554.
   change (exists ground bits, VM.find (N.of_nat 8555) result = Some (Gval ground bits)).
   exact (data_address_node_output_8555 inputs path old current result S8266 S8554 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8266 ltac:(do 0 right; left; reflexivity)) as S8266.
   apply writer_concrete_ground in S8266.
   pose proof (Sources 8603 ltac:(do 1 right; left; reflexivity)) as S8603.
   apply writer_concrete_ground in S8603.
   change (exists ground bits, VM.find (N.of_nat 8604) result = Some (Gval ground bits)).
   exact (data_address_node_output_8604 inputs path old current result S8266 S8603 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8266 ltac:(do 0 right; left; reflexivity)) as S8266.
   apply writer_concrete_ground in S8266.
   pose proof (Sources 8750 ltac:(do 1 right; left; reflexivity)) as S8750.
   apply writer_concrete_ground in S8750.
   change (exists ground bits, VM.find (N.of_nat 8751) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8751 inputs path old current result S8266 S8750 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8266 ltac:(do 0 right; left; reflexivity)) as S8266.
   apply writer_concrete_ground in S8266.
   pose proof (Sources 8799 ltac:(do 1 right; left; reflexivity)) as S8799.
   apply writer_concrete_ground in S8799.
   change (exists ground bits, VM.find (N.of_nat 8800) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8800 inputs path old current result S8266 S8799 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8264 ltac:(do 0 right; left; reflexivity)) as S8264.
   apply writer_concrete_ground in S8264.
   pose proof (Sources 8457 ltac:(do 1 right; left; reflexivity)) as S8457.
   apply writer_concrete_ground in S8457.
   change (exists ground bits, VM.find (N.of_nat 8458) result = Some (Gval ground bits)).
   exact (data_address_node_output_8458 inputs path old current result S8264 S8457 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8264 ltac:(do 0 right; left; reflexivity)) as S8264.
   apply writer_concrete_ground in S8264.
   pose proof (Sources 8506 ltac:(do 1 right; left; reflexivity)) as S8506.
   apply writer_concrete_ground in S8506.
   change (exists ground bits, VM.find (N.of_nat 8507) result = Some (Gval ground bits)).
   exact (data_address_node_output_8507 inputs path old current result S8264 S8506 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8264 ltac:(do 0 right; left; reflexivity)) as S8264.
   apply writer_concrete_ground in S8264.
   pose proof (Sources 8555 ltac:(do 1 right; left; reflexivity)) as S8555.
   apply writer_concrete_ground in S8555.
   change (exists ground bits, VM.find (N.of_nat 8556) result = Some (Gval ground bits)).
   exact (data_address_node_output_8556 inputs path old current result S8264 S8555 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8264 ltac:(do 0 right; left; reflexivity)) as S8264.
   apply writer_concrete_ground in S8264.
   pose proof (Sources 8604 ltac:(do 1 right; left; reflexivity)) as S8604.
   apply writer_concrete_ground in S8604.
   change (exists ground bits, VM.find (N.of_nat 8605) result = Some (Gval ground bits)).
   exact (data_address_node_output_8605 inputs path old current result S8264 S8604 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8264 ltac:(do 0 right; left; reflexivity)) as S8264.
   apply writer_concrete_ground in S8264.
   pose proof (Sources 8751 ltac:(do 1 right; left; reflexivity)) as S8751.
   apply writer_concrete_ground in S8751.
   change (exists ground bits, VM.find (N.of_nat 8752) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8752 inputs path old current result S8264 S8751 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8264 ltac:(do 0 right; left; reflexivity)) as S8264.
   apply writer_concrete_ground in S8264.
   pose proof (Sources 8800 ltac:(do 1 right; left; reflexivity)) as S8800.
   apply writer_concrete_ground in S8800.
   change (exists ground bits, VM.find (N.of_nat 8801) result = Some (Gval ground bits)).
   exact (data_writer_node_output_8801 inputs path old current result S8264 S8800 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8458 ltac:(do 0 right; left; reflexivity)) as S8458.
   apply writer_concrete_ground in S8458.
   change (exists ground bits, VM.find (N.of_nat 8252) result = Some (Gval ground bits)).
   destruct (data_address_connection_8252_output (formal_invalid_policy inputs path) old current result S8458 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8507 ltac:(do 0 right; left; reflexivity)) as S8507.
   apply writer_concrete_ground in S8507.
   change (exists ground bits, VM.find (N.of_nat 8253) result = Some (Gval ground bits)).
   destruct (data_address_connection_8253_output (formal_invalid_policy inputs path) old current result S8507 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8556 ltac:(do 0 right; left; reflexivity)) as S8556.
   apply writer_concrete_ground in S8556.
   change (exists ground bits, VM.find (N.of_nat 8254) result = Some (Gval ground bits)).
   destruct (data_address_connection_8254_output (formal_invalid_policy inputs path) old current result S8556 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8605 ltac:(do 0 right; left; reflexivity)) as S8605.
   apply writer_concrete_ground in S8605.
   change (exists ground bits, VM.find (N.of_nat 8255) result = Some (Gval ground bits)).
   destruct (data_address_connection_8255_output (formal_invalid_policy inputs path) old current result S8605 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8752 ltac:(do 0 right; left; reflexivity)) as S8752.
   apply writer_concrete_ground in S8752.
   change (exists ground bits, VM.find (N.of_nat 8257) result = Some (Gval ground bits)).
   destruct (data_writer_connection_8257_output (formal_invalid_policy inputs path) old current result S8752 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
Qed.
Definition data_writer_chunk_24 : list (nat * (nat * list nat)) := [::(8258,(54,[::8801]));(86,(55,[::8252]));(87,(55,[::8253]));(88,(55,[::8254]));(89,(55,[::8255]));(91,(55,[::8257]));(92,(55,[::8258]));(1153,(56,[::89]));(1307,(56,[::88]));(7820,(56,[::86]));(7822,(56,[::87]));(7833,(56,[::91]));(7834,(56,[::92]));(7838,(56,[::91;7754;7765]));(1156,(57,[::1153]));(1342,(57,[::1307]));(1344,(57,[::1307]));(1346,(57,[::1307]));(1348,(57,[::1307]));(1350,(57,[::1307]));(1352,(57,[::1307]));(7821,(57,[::7749;7816;7820]));(7835,(57,[::7833;7834]));(7843,(57,[::7838]))].
Lemma data_writer_chunk_24_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_24.
Proof.
 intros Memory Step. unfold data_writer_chunk_24.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8801 ltac:(do 0 right; left; reflexivity)) as S8801.
   apply writer_concrete_ground in S8801.
   change (exists ground bits, VM.find (N.of_nat 8258) result = Some (Gval ground bits)).
   destruct (data_writer_connection_8258_output (formal_invalid_policy inputs path) old current result S8801 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8252 ltac:(do 0 right; left; reflexivity)) as S8252.
   apply writer_concrete_ground in S8252.
   change (exists ground bits, VM.find (N.of_nat 86) result = Some (Gval ground bits)).
   destruct (data_address_connection_86_output (formal_invalid_policy inputs path) old current result S8252 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8253 ltac:(do 0 right; left; reflexivity)) as S8253.
   apply writer_concrete_ground in S8253.
   change (exists ground bits, VM.find (N.of_nat 87) result = Some (Gval ground bits)).
   destruct (data_address_connection_87_output (formal_invalid_policy inputs path) old current result S8253 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8254 ltac:(do 0 right; left; reflexivity)) as S8254.
   apply writer_concrete_ground in S8254.
   change (exists ground bits, VM.find (N.of_nat 88) result = Some (Gval ground bits)).
   destruct (data_address_connection_88_output (formal_invalid_policy inputs path) old current result S8254 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8255 ltac:(do 0 right; left; reflexivity)) as S8255.
   apply writer_concrete_ground in S8255.
   change (exists ground bits, VM.find (N.of_nat 89) result = Some (Gval ground bits)).
   destruct (data_address_connection_89_output (formal_invalid_policy inputs path) old current result S8255 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8257 ltac:(do 0 right; left; reflexivity)) as S8257.
   apply writer_concrete_ground in S8257.
   change (exists ground bits, VM.find (N.of_nat 91) result = Some (Gval ground bits)).
   destruct (data_writer_connection_91_output (formal_invalid_policy inputs path) old current result S8257 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 8258 ltac:(do 0 right; left; reflexivity)) as S8258.
   apply writer_concrete_ground in S8258.
   change (exists ground bits, VM.find (N.of_nat 92) result = Some (Gval ground bits)).
   destruct (data_writer_connection_92_output (formal_invalid_policy inputs path) old current result S8258 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 89 ltac:(do 0 right; left; reflexivity)) as S89.
   apply writer_concrete_ground in S89.
   change (exists ground bits, VM.find (N.of_nat 1153) result = Some (Gval ground bits)).
   destruct (data_address_connection_1153_output (formal_invalid_policy inputs path) old current result S89 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 88 ltac:(do 0 right; left; reflexivity)) as S88.
   apply writer_concrete_ground in S88.
   change (exists ground bits, VM.find (N.of_nat 1307) result = Some (Gval ground bits)).
   destruct (data_address_connection_1307_output (formal_invalid_policy inputs path) old current result S88 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 86 ltac:(do 0 right; left; reflexivity)) as S86.
   apply writer_concrete_ground in S86.
   change (exists ground bits, VM.find (N.of_nat 7820) result = Some (Gval ground bits)).
   exact (data_address_node_output_7820 inputs path old current result S86 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 87 ltac:(do 0 right; left; reflexivity)) as S87.
   apply writer_concrete_ground in S87.
   change (exists ground bits, VM.find (N.of_nat 7822) result = Some (Gval ground bits)).
   exact (data_address_node_output_7822 inputs path old current result S87 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 91 ltac:(do 0 right; left; reflexivity)) as S91.
   apply writer_concrete_ground in S91.
   change (exists ground bits, VM.find (N.of_nat 7833) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7833 inputs path old current result S91 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 92 ltac:(do 0 right; left; reflexivity)) as S92.
   apply writer_concrete_ground in S92.
   change (exists ground bits, VM.find (N.of_nat 7834) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7834 inputs path old current result S92 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 91 ltac:(do 0 right; left; reflexivity)) as S91.
   apply writer_concrete_ground in S91.
   pose proof (Sources 7754 ltac:(do 1 right; left; reflexivity)) as S7754.
   apply writer_concrete_ground in S7754.
   pose proof (Sources 7765 ltac:(do 2 right; left; reflexivity)) as S7765.
   apply writer_concrete_ground in S7765.
   change (exists ground bits, VM.find (N.of_nat 7838) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7838 inputs path old current result S91 S7754 S7765 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1153 ltac:(do 0 right; left; reflexivity)) as S1153.
   apply writer_concrete_ground in S1153.
   change (exists ground bits, VM.find (N.of_nat 1156) result = Some (Gval ground bits)).
   exact (data_address_node_output_1156 inputs path old current result S1153 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1307 ltac:(do 0 right; left; reflexivity)) as S1307.
   apply writer_concrete_ground in S1307.
   change (exists ground bits, VM.find (N.of_nat 1342) result = Some (Gval ground bits)).
   exact (data_address_node_output_1342 inputs path old current result S1307 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1307 ltac:(do 0 right; left; reflexivity)) as S1307.
   apply writer_concrete_ground in S1307.
   change (exists ground bits, VM.find (N.of_nat 1344) result = Some (Gval ground bits)).
   exact (data_address_node_output_1344 inputs path old current result S1307 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1307 ltac:(do 0 right; left; reflexivity)) as S1307.
   apply writer_concrete_ground in S1307.
   change (exists ground bits, VM.find (N.of_nat 1346) result = Some (Gval ground bits)).
   exact (data_address_node_output_1346 inputs path old current result S1307 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1307 ltac:(do 0 right; left; reflexivity)) as S1307.
   apply writer_concrete_ground in S1307.
   change (exists ground bits, VM.find (N.of_nat 1348) result = Some (Gval ground bits)).
   exact (data_address_node_output_1348 inputs path old current result S1307 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1307 ltac:(do 0 right; left; reflexivity)) as S1307.
   apply writer_concrete_ground in S1307.
   change (exists ground bits, VM.find (N.of_nat 1350) result = Some (Gval ground bits)).
   exact (data_address_node_output_1350 inputs path old current result S1307 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1307 ltac:(do 0 right; left; reflexivity)) as S1307.
   apply writer_concrete_ground in S1307.
   change (exists ground bits, VM.find (N.of_nat 1352) result = Some (Gval ground bits)).
   exact (data_address_node_output_1352 inputs path old current result S1307 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7749 ltac:(do 0 right; left; reflexivity)) as S7749.
   apply writer_concrete_ground in S7749.
   pose proof (Sources 7816 ltac:(do 1 right; left; reflexivity)) as S7816.
   apply writer_concrete_ground in S7816.
   pose proof (Sources 7820 ltac:(do 2 right; left; reflexivity)) as S7820.
   apply writer_concrete_ground in S7820.
   change (exists ground bits, VM.find (N.of_nat 7821) result = Some (Gval ground bits)).
   exact (data_address_node_output_7821 inputs path old current result S7749 S7816 S7820 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7833 ltac:(do 0 right; left; reflexivity)) as S7833.
   apply writer_concrete_ground in S7833.
   pose proof (Sources 7834 ltac:(do 1 right; left; reflexivity)) as S7834.
   apply writer_concrete_ground in S7834.
   change (exists ground bits, VM.find (N.of_nat 7835) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7835 inputs path old current result S7833 S7834 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7838 ltac:(do 0 right; left; reflexivity)) as S7838.
   apply writer_concrete_ground in S7838.
   change (exists ground bits, VM.find (N.of_nat 7843) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7843 inputs path old current result S7838 Step). }
 constructor.
Qed.
Definition data_writer_chunk_25 : list (nat * (nat * list nat)) := [::(7845,(57,[::7838]));(7847,(57,[::7838]));(1151,(58,[::7821]));(1343,(58,[::1310;1341;1342]));(7836,(58,[::7832;7835]));(7844,(58,[::7843]));(77,(59,[::7836]));(1345,(59,[::1314;1343;1344]));(36,(60,[::77]));(1347,(60,[::1323;1345;1346]));(1349,(61,[::1326;1347;1348]));(1351,(62,[::1337;1349;1350]));(1353,(63,[::1339;1351;1352]));(1354,(64,[::1353]));(1308,(65,[::1354]));(7823,(66,[::1308;7819;7822]));(1152,(67,[::7823]));(1157,(68,[::1152]));(1158,(69,[::1157]));(1159,(70,[::1152;1156;1158]));(1160,(71,[::1151;1159]));(1161,(72,[::1160]));(1155,(73,[::1161]));(7824,(74,[::1155;7752;7765]))].
Lemma data_writer_chunk_25_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_25.
Proof.
 intros Memory Step. unfold data_writer_chunk_25.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7838 ltac:(do 0 right; left; reflexivity)) as S7838.
   apply writer_concrete_ground in S7838.
   change (exists ground bits, VM.find (N.of_nat 7845) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7845 inputs path old current result S7838 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7838 ltac:(do 0 right; left; reflexivity)) as S7838.
   apply writer_concrete_ground in S7838.
   change (exists ground bits, VM.find (N.of_nat 7847) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7847 inputs path old current result S7838 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7821 ltac:(do 0 right; left; reflexivity)) as S7821.
   apply writer_concrete_ground in S7821.
   change (exists ground bits, VM.find (N.of_nat 1151) result = Some (Gval ground bits)).
   destruct (data_address_connection_1151_output (formal_invalid_policy inputs path) old current result S7821 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1310 ltac:(do 0 right; left; reflexivity)) as S1310.
   apply writer_concrete_ground in S1310.
   pose proof (Sources 1341 ltac:(do 1 right; left; reflexivity)) as S1341.
   apply writer_concrete_ground in S1341.
   pose proof (Sources 1342 ltac:(do 2 right; left; reflexivity)) as S1342.
   apply writer_concrete_ground in S1342.
   change (exists ground bits, VM.find (N.of_nat 1343) result = Some (Gval ground bits)).
   exact (data_address_node_output_1343 inputs path old current result S1310 S1341 S1342 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7832 ltac:(do 0 right; left; reflexivity)) as S7832.
   apply writer_concrete_ground in S7832.
   pose proof (Sources 7835 ltac:(do 1 right; left; reflexivity)) as S7835.
   apply writer_concrete_ground in S7835.
   change (exists ground bits, VM.find (N.of_nat 7836) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7836 inputs path old current result S7832 S7835 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7843 ltac:(do 0 right; left; reflexivity)) as S7843.
   apply writer_concrete_ground in S7843.
   change (exists ground bits, VM.find (N.of_nat 7844) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7844 inputs path old current result S7843 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7836 ltac:(do 0 right; left; reflexivity)) as S7836.
   apply writer_concrete_ground in S7836.
   change (exists ground bits, VM.find (N.of_nat 77) result = Some (Gval ground bits)).
   destruct (data_writer_connection_77_output (formal_invalid_policy inputs path) old current result S7836 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1314 ltac:(do 0 right; left; reflexivity)) as S1314.
   apply writer_concrete_ground in S1314.
   pose proof (Sources 1343 ltac:(do 1 right; left; reflexivity)) as S1343.
   apply writer_concrete_ground in S1343.
   pose proof (Sources 1344 ltac:(do 2 right; left; reflexivity)) as S1344.
   apply writer_concrete_ground in S1344.
   change (exists ground bits, VM.find (N.of_nat 1345) result = Some (Gval ground bits)).
   exact (data_address_node_output_1345 inputs path old current result S1314 S1343 S1344 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 77 ltac:(do 0 right; left; reflexivity)) as S77.
   apply writer_concrete_ground in S77.
   change (exists ground bits, VM.find (N.of_nat 36) result = Some (Gval ground bits)).
   destruct (data_writer_connection_36_output (formal_invalid_policy inputs path) old current result S77 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1323 ltac:(do 0 right; left; reflexivity)) as S1323.
   apply writer_concrete_ground in S1323.
   pose proof (Sources 1345 ltac:(do 1 right; left; reflexivity)) as S1345.
   apply writer_concrete_ground in S1345.
   pose proof (Sources 1346 ltac:(do 2 right; left; reflexivity)) as S1346.
   apply writer_concrete_ground in S1346.
   change (exists ground bits, VM.find (N.of_nat 1347) result = Some (Gval ground bits)).
   exact (data_address_node_output_1347 inputs path old current result S1323 S1345 S1346 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1326 ltac:(do 0 right; left; reflexivity)) as S1326.
   apply writer_concrete_ground in S1326.
   pose proof (Sources 1347 ltac:(do 1 right; left; reflexivity)) as S1347.
   apply writer_concrete_ground in S1347.
   pose proof (Sources 1348 ltac:(do 2 right; left; reflexivity)) as S1348.
   apply writer_concrete_ground in S1348.
   change (exists ground bits, VM.find (N.of_nat 1349) result = Some (Gval ground bits)).
   exact (data_address_node_output_1349 inputs path old current result S1326 S1347 S1348 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1337 ltac:(do 0 right; left; reflexivity)) as S1337.
   apply writer_concrete_ground in S1337.
   pose proof (Sources 1349 ltac:(do 1 right; left; reflexivity)) as S1349.
   apply writer_concrete_ground in S1349.
   pose proof (Sources 1350 ltac:(do 2 right; left; reflexivity)) as S1350.
   apply writer_concrete_ground in S1350.
   change (exists ground bits, VM.find (N.of_nat 1351) result = Some (Gval ground bits)).
   exact (data_address_node_output_1351 inputs path old current result S1337 S1349 S1350 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1339 ltac:(do 0 right; left; reflexivity)) as S1339.
   apply writer_concrete_ground in S1339.
   pose proof (Sources 1351 ltac:(do 1 right; left; reflexivity)) as S1351.
   apply writer_concrete_ground in S1351.
   pose proof (Sources 1352 ltac:(do 2 right; left; reflexivity)) as S1352.
   apply writer_concrete_ground in S1352.
   change (exists ground bits, VM.find (N.of_nat 1353) result = Some (Gval ground bits)).
   exact (data_address_node_output_1353 inputs path old current result S1339 S1351 S1352 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1353 ltac:(do 0 right; left; reflexivity)) as S1353.
   apply writer_concrete_ground in S1353.
   change (exists ground bits, VM.find (N.of_nat 1354) result = Some (Gval ground bits)).
   exact (data_address_node_output_1354 inputs path old current result S1353 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1354 ltac:(do 0 right; left; reflexivity)) as S1354.
   apply writer_concrete_ground in S1354.
   change (exists ground bits, VM.find (N.of_nat 1308) result = Some (Gval ground bits)).
   destruct (data_address_connection_1308_output (formal_invalid_policy inputs path) old current result S1354 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1308 ltac:(do 0 right; left; reflexivity)) as S1308.
   apply writer_concrete_ground in S1308.
   pose proof (Sources 7819 ltac:(do 1 right; left; reflexivity)) as S7819.
   apply writer_concrete_ground in S7819.
   pose proof (Sources 7822 ltac:(do 2 right; left; reflexivity)) as S7822.
   apply writer_concrete_ground in S7822.
   change (exists ground bits, VM.find (N.of_nat 7823) result = Some (Gval ground bits)).
   exact (data_address_node_output_7823 inputs path old current result S1308 S7819 S7822 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7823 ltac:(do 0 right; left; reflexivity)) as S7823.
   apply writer_concrete_ground in S7823.
   change (exists ground bits, VM.find (N.of_nat 1152) result = Some (Gval ground bits)).
   destruct (data_address_connection_1152_output (formal_invalid_policy inputs path) old current result S7823 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1152 ltac:(do 0 right; left; reflexivity)) as S1152.
   apply writer_concrete_ground in S1152.
   change (exists ground bits, VM.find (N.of_nat 1157) result = Some (Gval ground bits)).
   exact (data_address_node_output_1157 inputs path old current result S1152 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1157 ltac:(do 0 right; left; reflexivity)) as S1157.
   apply writer_concrete_ground in S1157.
   change (exists ground bits, VM.find (N.of_nat 1158) result = Some (Gval ground bits)).
   exact (data_address_node_output_1158 inputs path old current result S1157 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1152 ltac:(do 0 right; left; reflexivity)) as S1152.
   apply writer_concrete_ground in S1152.
   pose proof (Sources 1156 ltac:(do 1 right; left; reflexivity)) as S1156.
   apply writer_concrete_ground in S1156.
   pose proof (Sources 1158 ltac:(do 2 right; left; reflexivity)) as S1158.
   apply writer_concrete_ground in S1158.
   change (exists ground bits, VM.find (N.of_nat 1159) result = Some (Gval ground bits)).
   exact (data_address_node_output_1159 inputs path old current result S1152 S1156 S1158 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1151 ltac:(do 0 right; left; reflexivity)) as S1151.
   apply writer_concrete_ground in S1151.
   pose proof (Sources 1159 ltac:(do 1 right; left; reflexivity)) as S1159.
   apply writer_concrete_ground in S1159.
   change (exists ground bits, VM.find (N.of_nat 1160) result = Some (Gval ground bits)).
   exact (data_address_node_output_1160 inputs path old current result S1151 S1159 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1160 ltac:(do 0 right; left; reflexivity)) as S1160.
   apply writer_concrete_ground in S1160.
   change (exists ground bits, VM.find (N.of_nat 1161) result = Some (Gval ground bits)).
   exact (data_address_node_output_1161 inputs path old current result S1160 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1161 ltac:(do 0 right; left; reflexivity)) as S1161.
   apply writer_concrete_ground in S1161.
   change (exists ground bits, VM.find (N.of_nat 1155) result = Some (Gval ground bits)).
   destruct (data_address_connection_1155_output (formal_invalid_policy inputs path) old current result S1161 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1155 ltac:(do 0 right; left; reflexivity)) as S1155.
   apply writer_concrete_ground in S1155.
   pose proof (Sources 7752 ltac:(do 1 right; left; reflexivity)) as S7752.
   apply writer_concrete_ground in S7752.
   pose proof (Sources 7765 ltac:(do 2 right; left; reflexivity)) as S7765.
   apply writer_concrete_ground in S7765.
   change (exists ground bits, VM.find (N.of_nat 7824) result = Some (Gval ground bits)).
   exact (data_address_node_output_7824 inputs path old current result S1155 S7752 S7765 Step). }
 constructor.
Qed.
Definition data_writer_chunk_26 : list (nat * (nat * list nat)) := [::(7827,(74,[::1155]));(7829,(74,[::1155]));(7839,(74,[::1155]));(7841,(74,[::1155]));(7825,(75,[::7824]));(7828,(75,[::7827]));(7830,(75,[::7829]));(7840,(75,[::7839]));(7842,(75,[::7841]));(7826,(76,[::7825]));(7831,(76,[::7828;7830]));(7846,(76,[::7840;7844;7845]));(78,(77,[::7826]));(7837,(77,[::7819;7831]));(7848,(77,[::7842;7846;7847]));(37,(78,[::78]));(79,(78,[::7837]));(80,(78,[::7848]));(38,(79,[::79]));(39,(79,[::80]));(9182,(79,[::37]));(9183,(80,[::39]));(9191,(80,[::39]));(9199,(80,[::39]))].
Lemma data_writer_chunk_26_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_26.
Proof.
 intros Memory Step. unfold data_writer_chunk_26.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1155 ltac:(do 0 right; left; reflexivity)) as S1155.
   apply writer_concrete_ground in S1155.
   change (exists ground bits, VM.find (N.of_nat 7827) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7827 inputs path old current result S1155 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1155 ltac:(do 0 right; left; reflexivity)) as S1155.
   apply writer_concrete_ground in S1155.
   change (exists ground bits, VM.find (N.of_nat 7829) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7829 inputs path old current result S1155 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1155 ltac:(do 0 right; left; reflexivity)) as S1155.
   apply writer_concrete_ground in S1155.
   change (exists ground bits, VM.find (N.of_nat 7839) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7839 inputs path old current result S1155 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 1155 ltac:(do 0 right; left; reflexivity)) as S1155.
   apply writer_concrete_ground in S1155.
   change (exists ground bits, VM.find (N.of_nat 7841) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7841 inputs path old current result S1155 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7824 ltac:(do 0 right; left; reflexivity)) as S7824.
   apply writer_concrete_ground in S7824.
   change (exists ground bits, VM.find (N.of_nat 7825) result = Some (Gval ground bits)).
   exact (data_address_node_output_7825 inputs path old current result S7824 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7827 ltac:(do 0 right; left; reflexivity)) as S7827.
   apply writer_concrete_ground in S7827.
   change (exists ground bits, VM.find (N.of_nat 7828) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7828 inputs path old current result S7827 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7829 ltac:(do 0 right; left; reflexivity)) as S7829.
   apply writer_concrete_ground in S7829.
   change (exists ground bits, VM.find (N.of_nat 7830) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7830 inputs path old current result S7829 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7839 ltac:(do 0 right; left; reflexivity)) as S7839.
   apply writer_concrete_ground in S7839.
   change (exists ground bits, VM.find (N.of_nat 7840) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7840 inputs path old current result S7839 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7841 ltac:(do 0 right; left; reflexivity)) as S7841.
   apply writer_concrete_ground in S7841.
   change (exists ground bits, VM.find (N.of_nat 7842) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7842 inputs path old current result S7841 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7825 ltac:(do 0 right; left; reflexivity)) as S7825.
   apply writer_concrete_ground in S7825.
   change (exists ground bits, VM.find (N.of_nat 7826) result = Some (Gval ground bits)).
   exact (data_address_node_output_7826 inputs path old current result S7825 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7828 ltac:(do 0 right; left; reflexivity)) as S7828.
   apply writer_concrete_ground in S7828.
   pose proof (Sources 7830 ltac:(do 1 right; left; reflexivity)) as S7830.
   apply writer_concrete_ground in S7830.
   change (exists ground bits, VM.find (N.of_nat 7831) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7831 inputs path old current result S7828 S7830 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7840 ltac:(do 0 right; left; reflexivity)) as S7840.
   apply writer_concrete_ground in S7840.
   pose proof (Sources 7844 ltac:(do 1 right; left; reflexivity)) as S7844.
   apply writer_concrete_ground in S7844.
   pose proof (Sources 7845 ltac:(do 2 right; left; reflexivity)) as S7845.
   apply writer_concrete_ground in S7845.
   change (exists ground bits, VM.find (N.of_nat 7846) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7846 inputs path old current result S7840 S7844 S7845 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7826 ltac:(do 0 right; left; reflexivity)) as S7826.
   apply writer_concrete_ground in S7826.
   change (exists ground bits, VM.find (N.of_nat 78) result = Some (Gval ground bits)).
   destruct (data_address_connection_78_output (formal_invalid_policy inputs path) old current result S7826 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7819 ltac:(do 0 right; left; reflexivity)) as S7819.
   apply writer_concrete_ground in S7819.
   pose proof (Sources 7831 ltac:(do 1 right; left; reflexivity)) as S7831.
   apply writer_concrete_ground in S7831.
   change (exists ground bits, VM.find (N.of_nat 7837) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7837 inputs path old current result S7819 S7831 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7842 ltac:(do 0 right; left; reflexivity)) as S7842.
   apply writer_concrete_ground in S7842.
   pose proof (Sources 7846 ltac:(do 1 right; left; reflexivity)) as S7846.
   apply writer_concrete_ground in S7846.
   pose proof (Sources 7847 ltac:(do 2 right; left; reflexivity)) as S7847.
   apply writer_concrete_ground in S7847.
   change (exists ground bits, VM.find (N.of_nat 7848) result = Some (Gval ground bits)).
   exact (data_writer_node_output_7848 inputs path old current result S7842 S7846 S7847 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 78 ltac:(do 0 right; left; reflexivity)) as S78.
   apply writer_concrete_ground in S78.
   change (exists ground bits, VM.find (N.of_nat 37) result = Some (Gval ground bits)).
   destruct (data_address_connection_37_output (formal_invalid_policy inputs path) old current result S78 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7837 ltac:(do 0 right; left; reflexivity)) as S7837.
   apply writer_concrete_ground in S7837.
   change (exists ground bits, VM.find (N.of_nat 79) result = Some (Gval ground bits)).
   destruct (data_writer_connection_79_output (formal_invalid_policy inputs path) old current result S7837 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 7848 ltac:(do 0 right; left; reflexivity)) as S7848.
   apply writer_concrete_ground in S7848.
   change (exists ground bits, VM.find (N.of_nat 80) result = Some (Gval ground bits)).
   destruct (data_writer_connection_80_output (formal_invalid_policy inputs path) old current result S7848 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 79 ltac:(do 0 right; left; reflexivity)) as S79.
   apply writer_concrete_ground in S79.
   change (exists ground bits, VM.find (N.of_nat 38) result = Some (Gval ground bits)).
   destruct (data_writer_connection_38_output (formal_invalid_policy inputs path) old current result S79 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 80 ltac:(do 0 right; left; reflexivity)) as S80.
   apply writer_concrete_ground in S80.
   change (exists ground bits, VM.find (N.of_nat 39) result = Some (Gval ground bits)).
   destruct (data_writer_connection_39_output (formal_invalid_policy inputs path) old current result S80 Step) as [bits Value].
   do 2 eexists; exact Value. }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 37 ltac:(do 0 right; left; reflexivity)) as S37.
   apply writer_concrete_ground in S37.
   change (exists ground bits, VM.find (N.of_nat 9182) result = Some (Gval ground bits)).
   exact (data_address_node_output_9182 inputs path old current result S37 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 39 ltac:(do 0 right; left; reflexivity)) as S39.
   apply writer_concrete_ground in S39.
   change (exists ground bits, VM.find (N.of_nat 9183) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9183 inputs path old current result S39 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 39 ltac:(do 0 right; left; reflexivity)) as S39.
   apply writer_concrete_ground in S39.
   change (exists ground bits, VM.find (N.of_nat 9191) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9191 inputs path old current result S39 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 39 ltac:(do 0 right; left; reflexivity)) as S39.
   apply writer_concrete_ground in S39.
   change (exists ground bits, VM.find (N.of_nat 9199) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9199 inputs path old current result S39 Step). }
 constructor.
Qed.
Definition data_writer_chunk_27 : list (nat * (nat * list nat)) := [::(9207,(80,[::39]));(9223,(80,[::39]));(9224,(80,[::9182]));(9184,(81,[::36;9183]));(9192,(81,[::36;9191]));(9200,(81,[::36;9199]));(9208,(81,[::36;9207]));(9225,(81,[::9223;9224]));(9227,(81,[::9223]));(9228,(81,[::9223]));(9185,(82,[::9184]));(9193,(82,[::9192]));(9201,(82,[::9200]));(9209,(82,[::9208]));(9230,(82,[::36;9225]));(9232,(82,[::36;9227]));(9233,(82,[::36;9228]));(9187,(83,[::38;9185]));(9195,(83,[::38;9193]));(9203,(83,[::38;9201]));(9211,(83,[::38;9209]));(9188,(84,[::9187]));(9196,(84,[::9195]));(9204,(84,[::9203]))].
Lemma data_writer_chunk_27_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_27.
Proof.
 intros Memory Step. unfold data_writer_chunk_27.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 39 ltac:(do 0 right; left; reflexivity)) as S39.
   apply writer_concrete_ground in S39.
   change (exists ground bits, VM.find (N.of_nat 9207) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9207 inputs path old current result S39 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 39 ltac:(do 0 right; left; reflexivity)) as S39.
   apply writer_concrete_ground in S39.
   change (exists ground bits, VM.find (N.of_nat 9223) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9223 inputs path old current result S39 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9182 ltac:(do 0 right; left; reflexivity)) as S9182.
   apply writer_concrete_ground in S9182.
   change (exists width bits, VM.find (N.of_nat 9224) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9224 inputs path old current result S9182 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 36 ltac:(do 0 right; left; reflexivity)) as S36.
   apply writer_concrete_ground in S36.
   pose proof (Sources 9183 ltac:(do 1 right; left; reflexivity)) as S9183.
   apply writer_concrete_ground in S9183.
   change (exists ground bits, VM.find (N.of_nat 9184) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9184 inputs path old current result S36 S9183 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 36 ltac:(do 0 right; left; reflexivity)) as S36.
   apply writer_concrete_ground in S36.
   pose proof (Sources 9191 ltac:(do 1 right; left; reflexivity)) as S9191.
   apply writer_concrete_ground in S9191.
   change (exists ground bits, VM.find (N.of_nat 9192) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9192 inputs path old current result S36 S9191 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 36 ltac:(do 0 right; left; reflexivity)) as S36.
   apply writer_concrete_ground in S36.
   pose proof (Sources 9199 ltac:(do 1 right; left; reflexivity)) as S9199.
   apply writer_concrete_ground in S9199.
   change (exists ground bits, VM.find (N.of_nat 9200) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9200 inputs path old current result S36 S9199 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 36 ltac:(do 0 right; left; reflexivity)) as S36.
   apply writer_concrete_ground in S36.
   pose proof (Sources 9207 ltac:(do 1 right; left; reflexivity)) as S9207.
   apply writer_concrete_ground in S9207.
   change (exists ground bits, VM.find (N.of_nat 9208) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9208 inputs path old current result S36 S9207 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9223 ltac:(do 0 right; left; reflexivity)) as S9223.
   apply writer_concrete_ground in S9223.
   pose proof (Sources 9224 ltac:(do 1 right; left; reflexivity)) as S9224.
   change (exists width bits, VM.find (N.of_nat 9225) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9225 inputs path old current result S9223 S9224 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9223 ltac:(do 0 right; left; reflexivity)) as S9223.
   apply writer_concrete_ground in S9223.
   change (exists width bits, VM.find (N.of_nat 9227) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9227 inputs path old current result S9223 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9223 ltac:(do 0 right; left; reflexivity)) as S9223.
   apply writer_concrete_ground in S9223.
   change (exists width bits, VM.find (N.of_nat 9228) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9228 inputs path old current result S9223 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9184 ltac:(do 0 right; left; reflexivity)) as S9184.
   apply writer_concrete_ground in S9184.
   change (exists ground bits, VM.find (N.of_nat 9185) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9185 inputs path old current result S9184 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9192 ltac:(do 0 right; left; reflexivity)) as S9192.
   apply writer_concrete_ground in S9192.
   change (exists ground bits, VM.find (N.of_nat 9193) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9193 inputs path old current result S9192 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9200 ltac:(do 0 right; left; reflexivity)) as S9200.
   apply writer_concrete_ground in S9200.
   change (exists ground bits, VM.find (N.of_nat 9201) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9201 inputs path old current result S9200 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9208 ltac:(do 0 right; left; reflexivity)) as S9208.
   apply writer_concrete_ground in S9208.
   change (exists ground bits, VM.find (N.of_nat 9209) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9209 inputs path old current result S9208 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 36 ltac:(do 0 right; left; reflexivity)) as S36.
   apply writer_concrete_ground in S36.
   pose proof (Sources 9225 ltac:(do 1 right; left; reflexivity)) as S9225.
   change (exists width bits, VM.find (N.of_nat 9230) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9230 inputs path old current result S36 S9225 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 36 ltac:(do 0 right; left; reflexivity)) as S36.
   apply writer_concrete_ground in S36.
   pose proof (Sources 9227 ltac:(do 1 right; left; reflexivity)) as S9227.
   apply writer_concrete_ground in S9227.
   change (exists width bits, VM.find (N.of_nat 9232) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9232 inputs path old current result S36 S9227 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 36 ltac:(do 0 right; left; reflexivity)) as S36.
   apply writer_concrete_ground in S36.
   pose proof (Sources 9228 ltac:(do 1 right; left; reflexivity)) as S9228.
   change (exists width bits, VM.find (N.of_nat 9233) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9233 inputs path old current result S36 S9228 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 38 ltac:(do 0 right; left; reflexivity)) as S38.
   apply writer_concrete_ground in S38.
   pose proof (Sources 9185 ltac:(do 1 right; left; reflexivity)) as S9185.
   apply writer_concrete_ground in S9185.
   change (exists ground bits, VM.find (N.of_nat 9187) result = Some (Gval ground bits)).
   destruct Memory as [values [Storage [Concrete Ports]]].
   destruct (Ports (N.of_nat 2) ltac:(do 0 right; left; reflexivity)) as [Enable [width [address Address]]].
   exact (data_memory_mux_output_9187 inputs path old current result values address width Storage Concrete Enable Address S9185 S38 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 38 ltac:(do 0 right; left; reflexivity)) as S38.
   apply writer_concrete_ground in S38.
   pose proof (Sources 9193 ltac:(do 1 right; left; reflexivity)) as S9193.
   apply writer_concrete_ground in S9193.
   change (exists ground bits, VM.find (N.of_nat 9195) result = Some (Gval ground bits)).
   destruct Memory as [values [Storage [Concrete Ports]]].
   destruct (Ports (N.of_nat 3) ltac:(do 1 right; left; reflexivity)) as [Enable [width [address Address]]].
   exact (data_memory_mux_output_9195 inputs path old current result values address width Storage Concrete Enable Address S9193 S38 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 38 ltac:(do 0 right; left; reflexivity)) as S38.
   apply writer_concrete_ground in S38.
   pose proof (Sources 9201 ltac:(do 1 right; left; reflexivity)) as S9201.
   apply writer_concrete_ground in S9201.
   change (exists ground bits, VM.find (N.of_nat 9203) result = Some (Gval ground bits)).
   destruct Memory as [values [Storage [Concrete Ports]]].
   destruct (Ports (N.of_nat 4) ltac:(do 2 right; left; reflexivity)) as [Enable [width [address Address]]].
   exact (data_memory_mux_output_9203 inputs path old current result values address width Storage Concrete Enable Address S9201 S38 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 38 ltac:(do 0 right; left; reflexivity)) as S38.
   apply writer_concrete_ground in S38.
   pose proof (Sources 9209 ltac:(do 1 right; left; reflexivity)) as S9209.
   apply writer_concrete_ground in S9209.
   change (exists ground bits, VM.find (N.of_nat 9211) result = Some (Gval ground bits)).
   destruct Memory as [values [Storage [Concrete Ports]]].
   destruct (Ports (N.of_nat 5) ltac:(do 3 right; left; reflexivity)) as [Enable [width [address Address]]].
   exact (data_memory_mux_output_9211 inputs path old current result values address width Storage Concrete Enable Address S9209 S38 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9187 ltac:(do 0 right; left; reflexivity)) as S9187.
   apply writer_concrete_ground in S9187.
   change (exists ground bits, VM.find (N.of_nat 9188) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9188 inputs path old current result S9187 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9195 ltac:(do 0 right; left; reflexivity)) as S9195.
   apply writer_concrete_ground in S9195.
   change (exists ground bits, VM.find (N.of_nat 9196) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9196 inputs path old current result S9195 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9203 ltac:(do 0 right; left; reflexivity)) as S9203.
   apply writer_concrete_ground in S9203.
   change (exists ground bits, VM.find (N.of_nat 9204) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9204 inputs path old current result S9203 Step). }
 constructor.
Qed.
Definition data_writer_chunk_28 : list (nat * (nat * list nat)) := [::(9212,(84,[::9211]));(9189,(85,[::9188]));(9197,(85,[::9196]));(9205,(85,[::9204]));(9213,(85,[::9212]));(9190,(86,[::9189]));(9198,(87,[::9190;9197]));(9206,(88,[::9198;9205]));(9214,(89,[::9206;9213]));(9229,(90,[::9214;9223]));(9234,(91,[::36;9229]))].
Lemma data_writer_chunk_28_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_chunk_28.
Proof.
 intros Memory Step. unfold data_writer_chunk_28.
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9211 ltac:(do 0 right; left; reflexivity)) as S9211.
   apply writer_concrete_ground in S9211.
   change (exists ground bits, VM.find (N.of_nat 9212) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9212 inputs path old current result S9211 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9188 ltac:(do 0 right; left; reflexivity)) as S9188.
   apply writer_concrete_ground in S9188.
   change (exists ground bits, VM.find (N.of_nat 9189) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9189 inputs path old current result S9188 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9196 ltac:(do 0 right; left; reflexivity)) as S9196.
   apply writer_concrete_ground in S9196.
   change (exists ground bits, VM.find (N.of_nat 9197) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9197 inputs path old current result S9196 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9204 ltac:(do 0 right; left; reflexivity)) as S9204.
   apply writer_concrete_ground in S9204.
   change (exists ground bits, VM.find (N.of_nat 9205) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9205 inputs path old current result S9204 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9212 ltac:(do 0 right; left; reflexivity)) as S9212.
   apply writer_concrete_ground in S9212.
   change (exists ground bits, VM.find (N.of_nat 9213) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9213 inputs path old current result S9212 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9189 ltac:(do 0 right; left; reflexivity)) as S9189.
   apply writer_concrete_ground in S9189.
   change (exists ground bits, VM.find (N.of_nat 9190) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9190 inputs path old current result S9189 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9190 ltac:(do 0 right; left; reflexivity)) as S9190.
   apply writer_concrete_ground in S9190.
   pose proof (Sources 9197 ltac:(do 1 right; left; reflexivity)) as S9197.
   apply writer_concrete_ground in S9197.
   change (exists ground bits, VM.find (N.of_nat 9198) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9198 inputs path old current result S9190 S9197 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9198 ltac:(do 0 right; left; reflexivity)) as S9198.
   apply writer_concrete_ground in S9198.
   pose proof (Sources 9205 ltac:(do 1 right; left; reflexivity)) as S9205.
   apply writer_concrete_ground in S9205.
   change (exists ground bits, VM.find (N.of_nat 9206) result = Some (Gval ground bits)).
   exact (data_writer_node_output_9206 inputs path old current result S9198 S9205 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9206 ltac:(do 0 right; left; reflexivity)) as S9206.
   apply writer_concrete_ground in S9206.
   pose proof (Sources 9213 ltac:(do 1 right; left; reflexivity)) as S9213.
   apply writer_concrete_ground in S9213.
   change (exists width bits, VM.find (N.of_nat 9214) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9214 inputs path old current result S9206 S9213 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 9214 ltac:(do 0 right; left; reflexivity)) as S9214.
   pose proof (Sources 9223 ltac:(do 1 right; left; reflexivity)) as S9223.
   apply writer_concrete_ground in S9223.
   change (exists width bits, VM.find (N.of_nat 9229) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9229 inputs path old current result S9214 S9223 Step). }
 constructor.
 { unfold writer_transfer. intros Positive Sources.
   pose proof (Sources 36 ltac:(do 0 right; left; reflexivity)) as S36.
   apply writer_concrete_ground in S36.
   pose proof (Sources 9229 ltac:(do 1 right; left; reflexivity)) as S9229.
   change (exists width bits, VM.find (N.of_nat 9234) result = Some (Gval (Fuint width) bits)).
   exact (data_writer_uint_output_9234 inputs path old current result S36 S9229 Step). }
 constructor.
Qed.
Theorem data_writer_dependency_transfers inputs path old current result :
 writer_memory_ready old ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (writer_transfer old result) data_writer_dependency_ranks.
Proof.
 intros Memory Step.
 change (List.Forall (writer_transfer old result) (List.app data_writer_chunk_0 (List.app data_writer_chunk_1 (List.app data_writer_chunk_2 (List.app data_writer_chunk_3 (List.app data_writer_chunk_4 (List.app data_writer_chunk_5 (List.app data_writer_chunk_6 (List.app data_writer_chunk_7 (List.app data_writer_chunk_8 (List.app data_writer_chunk_9 (List.app data_writer_chunk_10 (List.app data_writer_chunk_11 (List.app data_writer_chunk_12 (List.app data_writer_chunk_13 (List.app data_writer_chunk_14 (List.app data_writer_chunk_15 (List.app data_writer_chunk_16 (List.app data_writer_chunk_17 (List.app data_writer_chunk_18 (List.app data_writer_chunk_19 (List.app data_writer_chunk_20 (List.app data_writer_chunk_21 (List.app data_writer_chunk_22 (List.app data_writer_chunk_23 (List.app data_writer_chunk_24 (List.app data_writer_chunk_25 (List.app data_writer_chunk_26 (List.app data_writer_chunk_27 (List.app data_writer_chunk_28 [::])))))))))))))))))))))))))))))).
 apply List.Forall_app. split; [exact (data_writer_chunk_0_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_1_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_2_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_3_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_4_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_5_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_6_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_7_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_8_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_9_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_10_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_11_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_12_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_13_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_14_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_15_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_16_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_17_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_18_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_19_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_20_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_21_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_22_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_23_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_24_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_25_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_26_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_27_transfers inputs path old current result Memory Step)|].
 apply List.Forall_app. split; [exact (data_writer_chunk_28_transfers inputs path old current result Memory Step)|].
 constructor.
Qed.
Theorem data_writer_concrete_history inputs path history limit :
 (forall time node dependencies, (time <= limit)%coq_nat ->
 List.In (node,(0%nat,dependencies)) data_writer_dependency_ranks -> writer_concrete_at (history time) node) ->
 (forall time, (time < limit)%coq_nat -> writer_memory_ready (history time)) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path)
 flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time node rank dependencies, (time <= limit)%coq_nat ->
 List.In (node,(rank,dependencies)) data_writer_dependency_ranks -> (rank <= time)%coq_nat ->
 writer_concrete_at (history time) node.
Proof.
 intros Boundary Memory Steps.
 apply (checked_dependency_history data_writer_dependency_ranks (fun time node => writer_concrete_at (history time) node) limit data_writer_dependency_ranks_checked Boundary).
 intros time node rank dependencies Within Member Positive Sources.
 pose proof (data_writer_dependency_transfers inputs path (history time) (history time) (history (S time)) (Memory time Within) (Steps time Within)) as Transfers.
 rewrite List.Forall_forall in Transfers.
 exact (Transfers (node,(rank,dependencies)) Member Positive Sources).
Qed.
Print Assumptions data_writer_concrete_history.
