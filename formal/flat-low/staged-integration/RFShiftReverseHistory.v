Require Import RFShiftNodes RFShiftNodeStep RFShiftReverse CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_shift_word_1173 (word:bits) := zeros 16++ones 16.
Definition rf_shift_word_1174 (word:bits) := xorB  (ones 32) (rf_shift_word_1173 word).
Definition rf_shift_word_1175 (word:bits) := drop 16 word.
Definition rf_shift_word_1176 (word:bits) := andB (rf_shift_word_1175 word) (rf_shift_word_1174 word).
Definition rf_shift_word_1177 (word:bits) := drop 0(take 16 word).
Definition rf_shift_word_1178 (word:bits) := zeros 16++(rf_shift_word_1177 word).
Definition rf_shift_word_1179 (word:bits) := invB (rf_shift_word_1174 word).
Definition rf_shift_word_1180 (word:bits) := andB (rf_shift_word_1178 word) (rf_shift_word_1179 word).
Definition rf_shift_word_1181 (word:bits) := orB (rf_shift_word_1176 word) (rf_shift_word_1180 word).
Definition rf_shift_word_1182 (word:bits) := drop 0(take 24 (rf_shift_word_1174 word)).
Definition rf_shift_word_1183 (word:bits) := zeros 8++(rf_shift_word_1182 word).
Definition rf_shift_word_1184 (word:bits) := xorB (rf_shift_word_1174 word) (rf_shift_word_1183 word).
Definition rf_shift_word_1185 (word:bits) := drop 8 (rf_shift_word_1181 word).
Definition rf_shift_word_1186 (word:bits) := andB (rf_shift_word_1185 word) (rf_shift_word_1184 word).
Definition rf_shift_word_1187 (word:bits) := drop 0(take 24 (rf_shift_word_1181 word)).
Definition rf_shift_word_1188 (word:bits) := zeros 8++(rf_shift_word_1187 word).
Definition rf_shift_word_1189 (word:bits) := invB (rf_shift_word_1184 word).
Definition rf_shift_word_1190 (word:bits) := andB (rf_shift_word_1188 word) (rf_shift_word_1189 word).
Definition rf_shift_word_1191 (word:bits) := orB (rf_shift_word_1186 word) (rf_shift_word_1190 word).
Definition rf_shift_word_1192 (word:bits) := drop 0(take 28 (rf_shift_word_1184 word)).
Definition rf_shift_word_1193 (word:bits) := zeros 4++(rf_shift_word_1192 word).
Definition rf_shift_word_1194 (word:bits) := xorB (rf_shift_word_1184 word) (rf_shift_word_1193 word).
Definition rf_shift_word_1195 (word:bits) := drop 4 (rf_shift_word_1191 word).
Definition rf_shift_word_1196 (word:bits) := andB (rf_shift_word_1195 word) (rf_shift_word_1194 word).
Definition rf_shift_word_1197 (word:bits) := drop 0(take 28 (rf_shift_word_1191 word)).
Definition rf_shift_word_1198 (word:bits) := zeros 4++(rf_shift_word_1197 word).
Definition rf_shift_word_1199 (word:bits) := invB (rf_shift_word_1194 word).
Definition rf_shift_word_1200 (word:bits) := andB (rf_shift_word_1198 word) (rf_shift_word_1199 word).
Definition rf_shift_word_1201 (word:bits) := orB (rf_shift_word_1196 word) (rf_shift_word_1200 word).
Definition rf_shift_word_1202 (word:bits) := drop 0(take 30 (rf_shift_word_1194 word)).
Definition rf_shift_word_1203 (word:bits) := zeros 2++(rf_shift_word_1202 word).
Definition rf_shift_word_1204 (word:bits) := xorB (rf_shift_word_1194 word) (rf_shift_word_1203 word).
Definition rf_shift_word_1205 (word:bits) := drop 2 (rf_shift_word_1201 word).
Definition rf_shift_word_1206 (word:bits) := andB (rf_shift_word_1205 word) (rf_shift_word_1204 word).
Definition rf_shift_word_1207 (word:bits) := drop 0(take 30 (rf_shift_word_1201 word)).
Definition rf_shift_word_1208 (word:bits) := zeros 2++(rf_shift_word_1207 word).
Definition rf_shift_word_1209 (word:bits) := invB (rf_shift_word_1204 word).
Definition rf_shift_word_1210 (word:bits) := andB (rf_shift_word_1208 word) (rf_shift_word_1209 word).
Definition rf_shift_word_1211 (word:bits) := orB (rf_shift_word_1206 word) (rf_shift_word_1210 word).
Definition rf_shift_word_1212 (word:bits) := drop 0(take 31 (rf_shift_word_1204 word)).
Definition rf_shift_word_1213 (word:bits) := zeros 1++(rf_shift_word_1212 word).
Definition rf_shift_word_1214 (word:bits) := xorB (rf_shift_word_1204 word) (rf_shift_word_1213 word).
Definition rf_shift_word_1215 (word:bits) := drop 1 (rf_shift_word_1211 word).
Definition rf_shift_word_1216 (word:bits) := andB (rf_shift_word_1215 word) (rf_shift_word_1214 word).
Definition rf_shift_word_1217 (word:bits) := drop 0(take 31 (rf_shift_word_1211 word)).
Definition rf_shift_word_1218 (word:bits) := zeros 1++(rf_shift_word_1217 word).
Definition rf_shift_word_1219 (word:bits) := invB (rf_shift_word_1214 word).
Definition rf_shift_word_1220 (word:bits) := andB (rf_shift_word_1218 word) (rf_shift_word_1219 word).
Definition rf_shift_word_1221 (word:bits) := orB (rf_shift_word_1216 word) (rf_shift_word_1220 word).
Lemma rf_shift_reverse_1221 word :size word=32%nat ->rf_shift_word_1221 word=rev word.
Proof.
 intro Size. unfold rf_shift_word_1221 , rf_shift_word_1220 , rf_shift_word_1219 , rf_shift_word_1218 , rf_shift_word_1217 , rf_shift_word_1216 , rf_shift_word_1215 , rf_shift_word_1214 , rf_shift_word_1213 , rf_shift_word_1212 , rf_shift_word_1211 , rf_shift_word_1210 , rf_shift_word_1209 , rf_shift_word_1208 , rf_shift_word_1207 , rf_shift_word_1206 , rf_shift_word_1205 , rf_shift_word_1204 , rf_shift_word_1203 , rf_shift_word_1202 , rf_shift_word_1201 , rf_shift_word_1200 , rf_shift_word_1199 , rf_shift_word_1198 , rf_shift_word_1197 , rf_shift_word_1196 , rf_shift_word_1195 , rf_shift_word_1194 , rf_shift_word_1193 , rf_shift_word_1192 , rf_shift_word_1191 , rf_shift_word_1190 , rf_shift_word_1189 , rf_shift_word_1188 , rf_shift_word_1187 , rf_shift_word_1186 , rf_shift_word_1185 , rf_shift_word_1184 , rf_shift_word_1183 , rf_shift_word_1182 , rf_shift_word_1181 , rf_shift_word_1180 , rf_shift_word_1179 , rf_shift_word_1178 , rf_shift_word_1177 , rf_shift_word_1176 , rf_shift_word_1175 , rf_shift_word_1174 , rf_shift_word_1173. rewrite !drop0. change(rf_reverse32 word=rev word). exact(rf_reverse32_correct word Size).
Qed.
Theorem rf_shift_reverse_history_1221 invalid history limit word :
 size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1151(history t)=Some(Gval(Fuint 32)word)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(21<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1221(history t)=Some(Gval(Fuint 32)(rev word)).
Proof.
 intros Size Source Steps.
 assert(V1173:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1173(history t)=Some(Gval(Fuint 32)(rf_shift_word_1173 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1173 rf_shift_expr_1173);
 [apply(List.nth_error_In rf_shift_nodes 2%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1173 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert(V1174:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1174(history t)=Some(Gval(Fuint 32)(rf_shift_word_1174 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1174 rf_shift_expr_1174);
 [apply(List.nth_error_In rf_shift_nodes 3%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1174 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1173 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1175:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1175(history t)=Some(Gval(Fuint 16)(rf_shift_word_1175 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1175 rf_shift_expr_1175);
 [apply(List.nth_error_In rf_shift_nodes 4%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1175 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (Source t ltac:(lia)).
 reflexivity. }
 assert(V1176:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1176(history t)=Some(Gval(Fuint 32)(rf_shift_word_1176 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1176 rf_shift_expr_1176);
 [apply(List.nth_error_In rf_shift_nodes 5%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1176 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1175 t ltac:(lia)ltac:(lia)) (V1174 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1177:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1177(history t)=Some(Gval(Fuint 16)(rf_shift_word_1177 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1177 rf_shift_expr_1177);
 [apply(List.nth_error_In rf_shift_nodes 6%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1177 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (Source t ltac:(lia)).
 reflexivity. }
 assert(V1178:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1178(history t)=Some(Gval(Fuint 32)(rf_shift_word_1178 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1178 rf_shift_expr_1178);
 [apply(List.nth_error_In rf_shift_nodes 7%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1178 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1177 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1179:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1179(history t)=Some(Gval(Fuint 32)(rf_shift_word_1179 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1179 rf_shift_expr_1179);
 [apply(List.nth_error_In rf_shift_nodes 8%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1179 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1174 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1180:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1180(history t)=Some(Gval(Fuint 32)(rf_shift_word_1180 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1180 rf_shift_expr_1180);
 [apply(List.nth_error_In rf_shift_nodes 9%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1180 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1178 t ltac:(lia)ltac:(lia)) (V1179 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1181:forall t,(5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1181(history t)=Some(Gval(Fuint 32)(rf_shift_word_1181 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1181 rf_shift_expr_1181);
 [apply(List.nth_error_In rf_shift_nodes 10%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1181 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1176 t ltac:(lia)ltac:(lia)) (V1180 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1182:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1182(history t)=Some(Gval(Fuint 24)(rf_shift_word_1182 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1182 rf_shift_expr_1182);
 [apply(List.nth_error_In rf_shift_nodes 11%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1182 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1174 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1183:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1183(history t)=Some(Gval(Fuint 32)(rf_shift_word_1183 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1183 rf_shift_expr_1183);
 [apply(List.nth_error_In rf_shift_nodes 12%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1183 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1182 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1184:forall t,(5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1184(history t)=Some(Gval(Fuint 32)(rf_shift_word_1184 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1184 rf_shift_expr_1184);
 [apply(List.nth_error_In rf_shift_nodes 13%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1184 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1174 t ltac:(lia)ltac:(lia)) (V1183 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1185:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1185(history t)=Some(Gval(Fuint 24)(rf_shift_word_1185 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1185 rf_shift_expr_1185);
 [apply(List.nth_error_In rf_shift_nodes 14%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1185 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1181 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1186:forall t,(7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1186(history t)=Some(Gval(Fuint 32)(rf_shift_word_1186 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1186 rf_shift_expr_1186);
 [apply(List.nth_error_In rf_shift_nodes 15%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1186 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1185 t ltac:(lia)ltac:(lia)) (V1184 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1187:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1187(history t)=Some(Gval(Fuint 24)(rf_shift_word_1187 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1187 rf_shift_expr_1187);
 [apply(List.nth_error_In rf_shift_nodes 16%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1187 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1181 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1188:forall t,(7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1188(history t)=Some(Gval(Fuint 32)(rf_shift_word_1188 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1188 rf_shift_expr_1188);
 [apply(List.nth_error_In rf_shift_nodes 17%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1188 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1187 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1189:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1189(history t)=Some(Gval(Fuint 32)(rf_shift_word_1189 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1189 rf_shift_expr_1189);
 [apply(List.nth_error_In rf_shift_nodes 18%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1189 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1184 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1190:forall t,(8<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1190(history t)=Some(Gval(Fuint 32)(rf_shift_word_1190 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1190 rf_shift_expr_1190);
 [apply(List.nth_error_In rf_shift_nodes 19%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1190 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1188 t ltac:(lia)ltac:(lia)) (V1189 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1191:forall t,(9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1191(history t)=Some(Gval(Fuint 32)(rf_shift_word_1191 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1191 rf_shift_expr_1191);
 [apply(List.nth_error_In rf_shift_nodes 20%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1191 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1186 t ltac:(lia)ltac:(lia)) (V1190 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1192:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1192(history t)=Some(Gval(Fuint 28)(rf_shift_word_1192 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1192 rf_shift_expr_1192);
 [apply(List.nth_error_In rf_shift_nodes 21%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1192 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1184 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1193:forall t,(7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1193(history t)=Some(Gval(Fuint 32)(rf_shift_word_1193 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1193 rf_shift_expr_1193);
 [apply(List.nth_error_In rf_shift_nodes 22%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1193 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1192 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1194:forall t,(8<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1194(history t)=Some(Gval(Fuint 32)(rf_shift_word_1194 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1194 rf_shift_expr_1194);
 [apply(List.nth_error_In rf_shift_nodes 23%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1194 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1184 t ltac:(lia)ltac:(lia)) (V1193 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1195:forall t,(10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1195(history t)=Some(Gval(Fuint 28)(rf_shift_word_1195 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1195 rf_shift_expr_1195);
 [apply(List.nth_error_In rf_shift_nodes 24%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1195 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1191 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1196:forall t,(11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1196(history t)=Some(Gval(Fuint 32)(rf_shift_word_1196 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1196 rf_shift_expr_1196);
 [apply(List.nth_error_In rf_shift_nodes 25%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1196 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1195 t ltac:(lia)ltac:(lia)) (V1194 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1197:forall t,(10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1197(history t)=Some(Gval(Fuint 28)(rf_shift_word_1197 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1197 rf_shift_expr_1197);
 [apply(List.nth_error_In rf_shift_nodes 26%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1197 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1191 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1198:forall t,(11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1198(history t)=Some(Gval(Fuint 32)(rf_shift_word_1198 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1198 rf_shift_expr_1198);
 [apply(List.nth_error_In rf_shift_nodes 27%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1198 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1197 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1199:forall t,(9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1199(history t)=Some(Gval(Fuint 32)(rf_shift_word_1199 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1199 rf_shift_expr_1199);
 [apply(List.nth_error_In rf_shift_nodes 28%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1199 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1194 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1200:forall t,(12<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1200(history t)=Some(Gval(Fuint 32)(rf_shift_word_1200 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1200 rf_shift_expr_1200);
 [apply(List.nth_error_In rf_shift_nodes 29%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1200 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1198 t ltac:(lia)ltac:(lia)) (V1199 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1201:forall t,(13<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1201(history t)=Some(Gval(Fuint 32)(rf_shift_word_1201 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1201 rf_shift_expr_1201);
 [apply(List.nth_error_In rf_shift_nodes 30%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1201 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1196 t ltac:(lia)ltac:(lia)) (V1200 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1202:forall t,(9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1202(history t)=Some(Gval(Fuint 30)(rf_shift_word_1202 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1202 rf_shift_expr_1202);
 [apply(List.nth_error_In rf_shift_nodes 31%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1202 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1194 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1203:forall t,(10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1203(history t)=Some(Gval(Fuint 32)(rf_shift_word_1203 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1203 rf_shift_expr_1203);
 [apply(List.nth_error_In rf_shift_nodes 32%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1203 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1202 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1204:forall t,(11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1204(history t)=Some(Gval(Fuint 32)(rf_shift_word_1204 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1204 rf_shift_expr_1204);
 [apply(List.nth_error_In rf_shift_nodes 33%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1204 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1194 t ltac:(lia)ltac:(lia)) (V1203 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1205:forall t,(14<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1205(history t)=Some(Gval(Fuint 30)(rf_shift_word_1205 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1205 rf_shift_expr_1205);
 [apply(List.nth_error_In rf_shift_nodes 34%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1205 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1201 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1206:forall t,(15<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1206(history t)=Some(Gval(Fuint 32)(rf_shift_word_1206 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1206 rf_shift_expr_1206);
 [apply(List.nth_error_In rf_shift_nodes 35%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1206 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1205 t ltac:(lia)ltac:(lia)) (V1204 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1207:forall t,(14<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1207(history t)=Some(Gval(Fuint 30)(rf_shift_word_1207 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1207 rf_shift_expr_1207);
 [apply(List.nth_error_In rf_shift_nodes 36%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1207 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1201 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1208:forall t,(15<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1208(history t)=Some(Gval(Fuint 32)(rf_shift_word_1208 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1208 rf_shift_expr_1208);
 [apply(List.nth_error_In rf_shift_nodes 37%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1208 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1207 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1209:forall t,(12<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1209(history t)=Some(Gval(Fuint 32)(rf_shift_word_1209 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1209 rf_shift_expr_1209);
 [apply(List.nth_error_In rf_shift_nodes 38%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1209 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1204 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1210:forall t,(16<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1210(history t)=Some(Gval(Fuint 32)(rf_shift_word_1210 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1210 rf_shift_expr_1210);
 [apply(List.nth_error_In rf_shift_nodes 39%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1210 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1208 t ltac:(lia)ltac:(lia)) (V1209 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1211:forall t,(17<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1211(history t)=Some(Gval(Fuint 32)(rf_shift_word_1211 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1211 rf_shift_expr_1211);
 [apply(List.nth_error_In rf_shift_nodes 40%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1211 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1206 t ltac:(lia)ltac:(lia)) (V1210 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1212:forall t,(12<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1212(history t)=Some(Gval(Fuint 31)(rf_shift_word_1212 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1212 rf_shift_expr_1212);
 [apply(List.nth_error_In rf_shift_nodes 41%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1212 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1204 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1213:forall t,(13<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1213(history t)=Some(Gval(Fuint 32)(rf_shift_word_1213 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1213 rf_shift_expr_1213);
 [apply(List.nth_error_In rf_shift_nodes 42%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1213 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1212 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1214:forall t,(14<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1214(history t)=Some(Gval(Fuint 32)(rf_shift_word_1214 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1214 rf_shift_expr_1214);
 [apply(List.nth_error_In rf_shift_nodes 43%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1214 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1204 t ltac:(lia)ltac:(lia)) (V1213 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1215:forall t,(18<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1215(history t)=Some(Gval(Fuint 31)(rf_shift_word_1215 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1215 rf_shift_expr_1215);
 [apply(List.nth_error_In rf_shift_nodes 44%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1215 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1211 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1216:forall t,(19<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1216(history t)=Some(Gval(Fuint 32)(rf_shift_word_1216 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1216 rf_shift_expr_1216);
 [apply(List.nth_error_In rf_shift_nodes 45%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1216 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1215 t ltac:(lia)ltac:(lia)) (V1214 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1217:forall t,(18<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1217(history t)=Some(Gval(Fuint 31)(rf_shift_word_1217 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1217 rf_shift_expr_1217);
 [apply(List.nth_error_In rf_shift_nodes 46%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1217 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1211 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1218:forall t,(19<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1218(history t)=Some(Gval(Fuint 32)(rf_shift_word_1218 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1218 rf_shift_expr_1218);
 [apply(List.nth_error_In rf_shift_nodes 47%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1218 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1217 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1219:forall t,(15<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1219(history t)=Some(Gval(Fuint 32)(rf_shift_word_1219 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1219 rf_shift_expr_1219);
 [apply(List.nth_error_In rf_shift_nodes 48%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1219 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1214 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1220:forall t,(20<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1220(history t)=Some(Gval(Fuint 32)(rf_shift_word_1220 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1220 rf_shift_expr_1220);
 [apply(List.nth_error_In rf_shift_nodes 49%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1220 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1218 t ltac:(lia)ltac:(lia)) (V1219 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1221:forall t,(21<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1221(history t)=Some(Gval(Fuint 32)(rf_shift_word_1221 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1221 rf_shift_expr_1221);
 [apply(List.nth_error_In rf_shift_nodes 50%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1221 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1216 t ltac:(lia)ltac:(lia)) (V1220 t ltac:(lia)ltac:(lia)).
 reflexivity. }
intros t Lower Upper. rewrite <-(rf_shift_reverse_1221 word Size). exact(V1221 t Lower Upper).
Qed.
Definition rf_shift_word_1230 (word:bits) := zeros 16++ones 16.
Definition rf_shift_word_1231 (word:bits) := xorB  (ones 32) (rf_shift_word_1230 word).
Definition rf_shift_word_1232 (word:bits) := drop 16 word.
Definition rf_shift_word_1233 (word:bits) := andB (rf_shift_word_1232 word) (rf_shift_word_1231 word).
Definition rf_shift_word_1234 (word:bits) := drop 0(take 16 word).
Definition rf_shift_word_1235 (word:bits) := zeros 16++(rf_shift_word_1234 word).
Definition rf_shift_word_1236 (word:bits) := invB (rf_shift_word_1231 word).
Definition rf_shift_word_1237 (word:bits) := andB (rf_shift_word_1235 word) (rf_shift_word_1236 word).
Definition rf_shift_word_1238 (word:bits) := orB (rf_shift_word_1233 word) (rf_shift_word_1237 word).
Definition rf_shift_word_1239 (word:bits) := drop 0(take 24 (rf_shift_word_1231 word)).
Definition rf_shift_word_1240 (word:bits) := zeros 8++(rf_shift_word_1239 word).
Definition rf_shift_word_1241 (word:bits) := xorB (rf_shift_word_1231 word) (rf_shift_word_1240 word).
Definition rf_shift_word_1242 (word:bits) := drop 8 (rf_shift_word_1238 word).
Definition rf_shift_word_1243 (word:bits) := andB (rf_shift_word_1242 word) (rf_shift_word_1241 word).
Definition rf_shift_word_1244 (word:bits) := drop 0(take 24 (rf_shift_word_1238 word)).
Definition rf_shift_word_1245 (word:bits) := zeros 8++(rf_shift_word_1244 word).
Definition rf_shift_word_1246 (word:bits) := invB (rf_shift_word_1241 word).
Definition rf_shift_word_1247 (word:bits) := andB (rf_shift_word_1245 word) (rf_shift_word_1246 word).
Definition rf_shift_word_1248 (word:bits) := orB (rf_shift_word_1243 word) (rf_shift_word_1247 word).
Definition rf_shift_word_1249 (word:bits) := drop 0(take 28 (rf_shift_word_1241 word)).
Definition rf_shift_word_1250 (word:bits) := zeros 4++(rf_shift_word_1249 word).
Definition rf_shift_word_1251 (word:bits) := xorB (rf_shift_word_1241 word) (rf_shift_word_1250 word).
Definition rf_shift_word_1252 (word:bits) := drop 4 (rf_shift_word_1248 word).
Definition rf_shift_word_1253 (word:bits) := andB (rf_shift_word_1252 word) (rf_shift_word_1251 word).
Definition rf_shift_word_1254 (word:bits) := drop 0(take 28 (rf_shift_word_1248 word)).
Definition rf_shift_word_1255 (word:bits) := zeros 4++(rf_shift_word_1254 word).
Definition rf_shift_word_1256 (word:bits) := invB (rf_shift_word_1251 word).
Definition rf_shift_word_1257 (word:bits) := andB (rf_shift_word_1255 word) (rf_shift_word_1256 word).
Definition rf_shift_word_1258 (word:bits) := orB (rf_shift_word_1253 word) (rf_shift_word_1257 word).
Definition rf_shift_word_1259 (word:bits) := drop 0(take 30 (rf_shift_word_1251 word)).
Definition rf_shift_word_1260 (word:bits) := zeros 2++(rf_shift_word_1259 word).
Definition rf_shift_word_1261 (word:bits) := xorB (rf_shift_word_1251 word) (rf_shift_word_1260 word).
Definition rf_shift_word_1262 (word:bits) := drop 2 (rf_shift_word_1258 word).
Definition rf_shift_word_1263 (word:bits) := andB (rf_shift_word_1262 word) (rf_shift_word_1261 word).
Definition rf_shift_word_1264 (word:bits) := drop 0(take 30 (rf_shift_word_1258 word)).
Definition rf_shift_word_1265 (word:bits) := zeros 2++(rf_shift_word_1264 word).
Definition rf_shift_word_1266 (word:bits) := invB (rf_shift_word_1261 word).
Definition rf_shift_word_1267 (word:bits) := andB (rf_shift_word_1265 word) (rf_shift_word_1266 word).
Definition rf_shift_word_1268 (word:bits) := orB (rf_shift_word_1263 word) (rf_shift_word_1267 word).
Definition rf_shift_word_1269 (word:bits) := drop 0(take 31 (rf_shift_word_1261 word)).
Definition rf_shift_word_1270 (word:bits) := zeros 1++(rf_shift_word_1269 word).
Definition rf_shift_word_1271 (word:bits) := xorB (rf_shift_word_1261 word) (rf_shift_word_1270 word).
Definition rf_shift_word_1272 (word:bits) := drop 1 (rf_shift_word_1268 word).
Definition rf_shift_word_1273 (word:bits) := andB (rf_shift_word_1272 word) (rf_shift_word_1271 word).
Definition rf_shift_word_1274 (word:bits) := drop 0(take 31 (rf_shift_word_1268 word)).
Definition rf_shift_word_1275 (word:bits) := zeros 1++(rf_shift_word_1274 word).
Definition rf_shift_word_1276 (word:bits) := invB (rf_shift_word_1271 word).
Definition rf_shift_word_1277 (word:bits) := andB (rf_shift_word_1275 word) (rf_shift_word_1276 word).
Definition rf_shift_word_1278 (word:bits) := orB (rf_shift_word_1273 word) (rf_shift_word_1277 word).
Lemma rf_shift_reverse_1278 word :size word=32%nat ->rf_shift_word_1278 word=rev word.
Proof.
 intro Size. unfold rf_shift_word_1278 , rf_shift_word_1277 , rf_shift_word_1276 , rf_shift_word_1275 , rf_shift_word_1274 , rf_shift_word_1273 , rf_shift_word_1272 , rf_shift_word_1271 , rf_shift_word_1270 , rf_shift_word_1269 , rf_shift_word_1268 , rf_shift_word_1267 , rf_shift_word_1266 , rf_shift_word_1265 , rf_shift_word_1264 , rf_shift_word_1263 , rf_shift_word_1262 , rf_shift_word_1261 , rf_shift_word_1260 , rf_shift_word_1259 , rf_shift_word_1258 , rf_shift_word_1257 , rf_shift_word_1256 , rf_shift_word_1255 , rf_shift_word_1254 , rf_shift_word_1253 , rf_shift_word_1252 , rf_shift_word_1251 , rf_shift_word_1250 , rf_shift_word_1249 , rf_shift_word_1248 , rf_shift_word_1247 , rf_shift_word_1246 , rf_shift_word_1245 , rf_shift_word_1244 , rf_shift_word_1243 , rf_shift_word_1242 , rf_shift_word_1241 , rf_shift_word_1240 , rf_shift_word_1239 , rf_shift_word_1238 , rf_shift_word_1237 , rf_shift_word_1236 , rf_shift_word_1235 , rf_shift_word_1234 , rf_shift_word_1233 , rf_shift_word_1232 , rf_shift_word_1231 , rf_shift_word_1230. rewrite !drop0. change(rf_reverse32 word=rev word). exact(rf_reverse32_correct word Size).
Qed.
Theorem rf_shift_reverse_history_1278 invalid history limit word :
 size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1229(history t)=Some(Gval(Fuint 32)word)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(21<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1278(history t)=Some(Gval(Fuint 32)(rev word)).
Proof.
 intros Size Source Steps.
 assert(V1230:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1230(history t)=Some(Gval(Fuint 32)(rf_shift_word_1230 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1230 rf_shift_expr_1230);
 [apply(List.nth_error_In rf_shift_nodes 59%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1230 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert(V1231:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1231(history t)=Some(Gval(Fuint 32)(rf_shift_word_1231 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1231 rf_shift_expr_1231);
 [apply(List.nth_error_In rf_shift_nodes 60%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1231 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1230 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1232:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1232(history t)=Some(Gval(Fuint 16)(rf_shift_word_1232 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1232 rf_shift_expr_1232);
 [apply(List.nth_error_In rf_shift_nodes 61%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1232 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (Source t ltac:(lia)).
 reflexivity. }
 assert(V1233:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1233(history t)=Some(Gval(Fuint 32)(rf_shift_word_1233 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1233 rf_shift_expr_1233);
 [apply(List.nth_error_In rf_shift_nodes 62%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1233 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1232 t ltac:(lia)ltac:(lia)) (V1231 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1234:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1234(history t)=Some(Gval(Fuint 16)(rf_shift_word_1234 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1234 rf_shift_expr_1234);
 [apply(List.nth_error_In rf_shift_nodes 63%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1234 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (Source t ltac:(lia)).
 reflexivity. }
 assert(V1235:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1235(history t)=Some(Gval(Fuint 32)(rf_shift_word_1235 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1235 rf_shift_expr_1235);
 [apply(List.nth_error_In rf_shift_nodes 64%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1235 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1234 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1236:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1236(history t)=Some(Gval(Fuint 32)(rf_shift_word_1236 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1236 rf_shift_expr_1236);
 [apply(List.nth_error_In rf_shift_nodes 65%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1236 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1231 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1237:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1237(history t)=Some(Gval(Fuint 32)(rf_shift_word_1237 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1237 rf_shift_expr_1237);
 [apply(List.nth_error_In rf_shift_nodes 66%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1237 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1235 t ltac:(lia)ltac:(lia)) (V1236 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1238:forall t,(5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1238(history t)=Some(Gval(Fuint 32)(rf_shift_word_1238 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1238 rf_shift_expr_1238);
 [apply(List.nth_error_In rf_shift_nodes 67%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1238 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1233 t ltac:(lia)ltac:(lia)) (V1237 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1239:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1239(history t)=Some(Gval(Fuint 24)(rf_shift_word_1239 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1239 rf_shift_expr_1239);
 [apply(List.nth_error_In rf_shift_nodes 68%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1239 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1231 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1240:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1240(history t)=Some(Gval(Fuint 32)(rf_shift_word_1240 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1240 rf_shift_expr_1240);
 [apply(List.nth_error_In rf_shift_nodes 69%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1240 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1239 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1241:forall t,(5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1241(history t)=Some(Gval(Fuint 32)(rf_shift_word_1241 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1241 rf_shift_expr_1241);
 [apply(List.nth_error_In rf_shift_nodes 70%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1241 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1231 t ltac:(lia)ltac:(lia)) (V1240 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1242:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1242(history t)=Some(Gval(Fuint 24)(rf_shift_word_1242 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1242 rf_shift_expr_1242);
 [apply(List.nth_error_In rf_shift_nodes 71%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1242 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1238 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1243:forall t,(7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1243(history t)=Some(Gval(Fuint 32)(rf_shift_word_1243 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1243 rf_shift_expr_1243);
 [apply(List.nth_error_In rf_shift_nodes 72%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1243 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1242 t ltac:(lia)ltac:(lia)) (V1241 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1244:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1244(history t)=Some(Gval(Fuint 24)(rf_shift_word_1244 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1244 rf_shift_expr_1244);
 [apply(List.nth_error_In rf_shift_nodes 73%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1244 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1238 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1245:forall t,(7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1245(history t)=Some(Gval(Fuint 32)(rf_shift_word_1245 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1245 rf_shift_expr_1245);
 [apply(List.nth_error_In rf_shift_nodes 74%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1245 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1244 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1246:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1246(history t)=Some(Gval(Fuint 32)(rf_shift_word_1246 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1246 rf_shift_expr_1246);
 [apply(List.nth_error_In rf_shift_nodes 75%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1246 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1241 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1247:forall t,(8<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1247(history t)=Some(Gval(Fuint 32)(rf_shift_word_1247 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1247 rf_shift_expr_1247);
 [apply(List.nth_error_In rf_shift_nodes 76%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1247 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1245 t ltac:(lia)ltac:(lia)) (V1246 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1248:forall t,(9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1248(history t)=Some(Gval(Fuint 32)(rf_shift_word_1248 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1248 rf_shift_expr_1248);
 [apply(List.nth_error_In rf_shift_nodes 77%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1248 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1243 t ltac:(lia)ltac:(lia)) (V1247 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1249:forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1249(history t)=Some(Gval(Fuint 28)(rf_shift_word_1249 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1249 rf_shift_expr_1249);
 [apply(List.nth_error_In rf_shift_nodes 78%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1249 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1241 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1250:forall t,(7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1250(history t)=Some(Gval(Fuint 32)(rf_shift_word_1250 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1250 rf_shift_expr_1250);
 [apply(List.nth_error_In rf_shift_nodes 79%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1250 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1249 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1251:forall t,(8<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1251(history t)=Some(Gval(Fuint 32)(rf_shift_word_1251 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1251 rf_shift_expr_1251);
 [apply(List.nth_error_In rf_shift_nodes 80%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1251 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1241 t ltac:(lia)ltac:(lia)) (V1250 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1252:forall t,(10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1252(history t)=Some(Gval(Fuint 28)(rf_shift_word_1252 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1252 rf_shift_expr_1252);
 [apply(List.nth_error_In rf_shift_nodes 81%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1252 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1248 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1253:forall t,(11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1253(history t)=Some(Gval(Fuint 32)(rf_shift_word_1253 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1253 rf_shift_expr_1253);
 [apply(List.nth_error_In rf_shift_nodes 82%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1253 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1252 t ltac:(lia)ltac:(lia)) (V1251 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1254:forall t,(10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1254(history t)=Some(Gval(Fuint 28)(rf_shift_word_1254 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1254 rf_shift_expr_1254);
 [apply(List.nth_error_In rf_shift_nodes 83%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1254 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1248 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1255:forall t,(11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1255(history t)=Some(Gval(Fuint 32)(rf_shift_word_1255 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1255 rf_shift_expr_1255);
 [apply(List.nth_error_In rf_shift_nodes 84%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1255 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1254 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1256:forall t,(9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1256(history t)=Some(Gval(Fuint 32)(rf_shift_word_1256 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1256 rf_shift_expr_1256);
 [apply(List.nth_error_In rf_shift_nodes 85%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1256 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1251 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1257:forall t,(12<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1257(history t)=Some(Gval(Fuint 32)(rf_shift_word_1257 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1257 rf_shift_expr_1257);
 [apply(List.nth_error_In rf_shift_nodes 86%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1257 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1255 t ltac:(lia)ltac:(lia)) (V1256 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1258:forall t,(13<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1258(history t)=Some(Gval(Fuint 32)(rf_shift_word_1258 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1258 rf_shift_expr_1258);
 [apply(List.nth_error_In rf_shift_nodes 87%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1258 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1253 t ltac:(lia)ltac:(lia)) (V1257 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1259:forall t,(9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1259(history t)=Some(Gval(Fuint 30)(rf_shift_word_1259 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1259 rf_shift_expr_1259);
 [apply(List.nth_error_In rf_shift_nodes 88%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1259 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1251 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1260:forall t,(10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1260(history t)=Some(Gval(Fuint 32)(rf_shift_word_1260 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1260 rf_shift_expr_1260);
 [apply(List.nth_error_In rf_shift_nodes 89%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1260 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1259 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1261:forall t,(11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1261(history t)=Some(Gval(Fuint 32)(rf_shift_word_1261 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1261 rf_shift_expr_1261);
 [apply(List.nth_error_In rf_shift_nodes 90%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1261 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1251 t ltac:(lia)ltac:(lia)) (V1260 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1262:forall t,(14<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1262(history t)=Some(Gval(Fuint 30)(rf_shift_word_1262 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1262 rf_shift_expr_1262);
 [apply(List.nth_error_In rf_shift_nodes 91%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1262 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1258 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1263:forall t,(15<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1263(history t)=Some(Gval(Fuint 32)(rf_shift_word_1263 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1263 rf_shift_expr_1263);
 [apply(List.nth_error_In rf_shift_nodes 92%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1263 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1262 t ltac:(lia)ltac:(lia)) (V1261 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1264:forall t,(14<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1264(history t)=Some(Gval(Fuint 30)(rf_shift_word_1264 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1264 rf_shift_expr_1264);
 [apply(List.nth_error_In rf_shift_nodes 93%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1264 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1258 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1265:forall t,(15<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1265(history t)=Some(Gval(Fuint 32)(rf_shift_word_1265 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1265 rf_shift_expr_1265);
 [apply(List.nth_error_In rf_shift_nodes 94%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1265 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1264 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1266:forall t,(12<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1266(history t)=Some(Gval(Fuint 32)(rf_shift_word_1266 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1266 rf_shift_expr_1266);
 [apply(List.nth_error_In rf_shift_nodes 95%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1266 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1261 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1267:forall t,(16<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1267(history t)=Some(Gval(Fuint 32)(rf_shift_word_1267 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1267 rf_shift_expr_1267);
 [apply(List.nth_error_In rf_shift_nodes 96%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1267 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1265 t ltac:(lia)ltac:(lia)) (V1266 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1268:forall t,(17<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1268(history t)=Some(Gval(Fuint 32)(rf_shift_word_1268 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1268 rf_shift_expr_1268);
 [apply(List.nth_error_In rf_shift_nodes 97%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1268 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1263 t ltac:(lia)ltac:(lia)) (V1267 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1269:forall t,(12<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1269(history t)=Some(Gval(Fuint 31)(rf_shift_word_1269 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1269 rf_shift_expr_1269);
 [apply(List.nth_error_In rf_shift_nodes 98%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1269 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1261 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1270:forall t,(13<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1270(history t)=Some(Gval(Fuint 32)(rf_shift_word_1270 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1270 rf_shift_expr_1270);
 [apply(List.nth_error_In rf_shift_nodes 99%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1270 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1269 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1271:forall t,(14<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1271(history t)=Some(Gval(Fuint 32)(rf_shift_word_1271 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1271 rf_shift_expr_1271);
 [apply(List.nth_error_In rf_shift_nodes 100%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1271 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1261 t ltac:(lia)ltac:(lia)) (V1270 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1272:forall t,(18<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1272(history t)=Some(Gval(Fuint 31)(rf_shift_word_1272 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1272 rf_shift_expr_1272);
 [apply(List.nth_error_In rf_shift_nodes 101%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1272 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1268 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1273:forall t,(19<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1273(history t)=Some(Gval(Fuint 32)(rf_shift_word_1273 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1273 rf_shift_expr_1273);
 [apply(List.nth_error_In rf_shift_nodes 102%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1273 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1272 t ltac:(lia)ltac:(lia)) (V1271 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1274:forall t,(18<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1274(history t)=Some(Gval(Fuint 31)(rf_shift_word_1274 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1274 rf_shift_expr_1274);
 [apply(List.nth_error_In rf_shift_nodes 103%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1274 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1268 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1275:forall t,(19<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1275(history t)=Some(Gval(Fuint 32)(rf_shift_word_1275 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1275 rf_shift_expr_1275);
 [apply(List.nth_error_In rf_shift_nodes 104%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1275 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1274 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1276:forall t,(15<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1276(history t)=Some(Gval(Fuint 32)(rf_shift_word_1276 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1276 rf_shift_expr_1276);
 [apply(List.nth_error_In rf_shift_nodes 105%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1276 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1271 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1277:forall t,(20<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1277(history t)=Some(Gval(Fuint 32)(rf_shift_word_1277 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1277 rf_shift_expr_1277);
 [apply(List.nth_error_In rf_shift_nodes 106%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1277 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1275 t ltac:(lia)ltac:(lia)) (V1276 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V1278:forall t,(21<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1278(history t)=Some(Gval(Fuint 32)(rf_shift_word_1278 word))).
 { intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step 1278 rf_shift_expr_1278);
 [apply(List.nth_error_In rf_shift_nodes 107%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_1278 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (V1273 t ltac:(lia)ltac:(lia)) (V1277 t ltac:(lia)ltac:(lia)).
 reflexivity. }
intros t Lower Upper. rewrite <-(rf_shift_reverse_1278 word Size). exact(V1278 t Lower Upper).
Qed.
