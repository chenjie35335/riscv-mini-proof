Require Import ConcreteExpressionClosure ConcreteScalarExpressions ConcreteGroundOperations.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Ltac solve_joint_update_ready :=
 first [apply closure_scalar; solve [repeat first [eapply scalar_ready_ref; eassumption | apply scalar_ready_const | apply scalar_ready_unary | apply scalar_ready_binary | apply scalar_ready_cast]]
 | apply closure_mux; solve_joint_update_ready | apply closure_unary; solve_joint_update_ready | apply closure_binary; solve_joint_update_ready].
Definition joint_update_expr_140 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 20) (@Eref VarOrder.T (@Eid VarOrder.T 123))).
Lemma joint_update_ready_140 old :
 (exists ground bits, VM.find 123 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_140.
Proof.
 intros [g123 [b123 H123]].
 unfold joint_update_expr_140.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_141 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 19 15) (@Eref VarOrder.T (@Eid VarOrder.T 123))).
Lemma joint_update_ready_141 old :
 (exists ground bits, VM.find 123 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_141.
Proof.
 intros [g123 [b123 H123]].
 unfold joint_update_expr_141.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_148 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; false])).
Lemma joint_update_ready_148 old :
 concrete_expression_ready old joint_update_expr_148.
Proof.
 unfold joint_update_expr_148.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_149 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 148)) (@Econst VarOrder.T (Fuint 26) [::false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; true; false; false; false; false; false])).
Lemma joint_update_ready_149 old :
 (exists ground bits, VM.find 148 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_149.
Proof.
 intros [g148 [b148 H148]].
 unfold joint_update_expr_149.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_154 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 153)) (@Eref VarOrder.T (@Eid VarOrder.T 150))).
Lemma joint_update_ready_154 old :
 (exists ground bits, VM.find 150 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_154.
Proof.
 intros [g150 [b150 H150]].
 intros [g153 [b153 H153]].
 unfold joint_update_expr_154.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_155 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 154)) (@Eref VarOrder.T (@Eid VarOrder.T 152))).
Lemma joint_update_ready_155 old :
 (exists ground bits, VM.find 152 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 154 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_155.
Proof.
 intros [g152 [b152 H152]].
 intros [g154 [b154 H154]].
 unfold joint_update_expr_155.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_156 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 151))).
Lemma joint_update_ready_156 old :
 (exists ground bits, VM.find 151 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_156.
Proof.
 intros [g151 [b151 H151]].
 unfold joint_update_expr_156.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_157 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Lemma joint_update_ready_157 old :
 concrete_expression_ready old joint_update_expr_157.
Proof.
 unfold joint_update_expr_157.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_158 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 157)) (@Eref VarOrder.T (@Eid VarOrder.T 156))).
Lemma joint_update_ready_158 old :
 (exists ground bits, VM.find 156 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 157 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_158.
Proof.
 intros [g156 [b156 H156]].
 intros [g157 [b157 H157]].
 unfold joint_update_expr_158.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_159 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 158)) (@Eref VarOrder.T (@Eid VarOrder.T 155))).
Lemma joint_update_ready_159 old :
 (exists ground bits, VM.find 155 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 158 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_159.
Proof.
 intros [g155 [b155 H155]].
 intros [g158 [b158 H158]].
 unfold joint_update_expr_159.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_160 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Lemma joint_update_ready_160 old :
 concrete_expression_ready old joint_update_expr_160.
Proof.
 unfold joint_update_expr_160.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_161 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 160)) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Lemma joint_update_ready_161 old :
 (exists ground bits, VM.find 160 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_161.
Proof.
 intros [g160 [b160 H160]].
 unfold joint_update_expr_161.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_162 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; false]) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_162 old :
 concrete_expression_ready old joint_update_expr_162.
Proof.
 unfold joint_update_expr_162.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_163 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 9) [::false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_163 old :
 concrete_expression_ready old joint_update_expr_163.
Proof.
 unfold joint_update_expr_163.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_164 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 163)) (@Eref VarOrder.T (@Eid VarOrder.T 162))).
Lemma joint_update_ready_164 old :
 (exists ground bits, VM.find 162 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 163 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_164.
Proof.
 intros [g162 [b162 H162]].
 intros [g163 [b163 H163]].
 unfold joint_update_expr_164.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_165 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 164)) (@Eref VarOrder.T (@Eid VarOrder.T 161))).
Lemma joint_update_ready_165 old :
 (exists ground bits, VM.find 161 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 164 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_165.
Proof.
 intros [g161 [b161 H161]].
 intros [g164 [b164 H164]].
 unfold joint_update_expr_165.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_166 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 165)) (@Eref VarOrder.T (@Eid VarOrder.T 159))).
Lemma joint_update_ready_166 old :
 (exists ground bits, VM.find 159 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 165 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_166.
Proof.
 intros [g159 [b159 H159]].
 intros [g165 [b165 H165]].
 unfold joint_update_expr_166.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_171 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_171 old :
 concrete_expression_ready old joint_update_expr_171.
Proof.
 unfold joint_update_expr_171.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_172 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 169)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_172 old :
 (exists ground bits, VM.find 169 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_172.
Proof.
 intros [g169 [b169 H169]].
 unfold joint_update_expr_172.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_173 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 172)) (@Eref VarOrder.T (@Eid VarOrder.T 171))).
Lemma joint_update_ready_173 old :
 (exists ground bits, VM.find 171 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 172 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_173.
Proof.
 intros [g171 [b171 H171]].
 intros [g172 [b172 H172]].
 unfold joint_update_expr_173.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_174 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_174 old :
 concrete_expression_ready old joint_update_expr_174.
Proof.
 unfold joint_update_expr_174.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_175 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 24) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 167))).
Lemma joint_update_ready_175 old :
 (exists ground bits, VM.find 167 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_175.
Proof.
 intros [g167 [b167 H167]].
 unfold joint_update_expr_175.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_176 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 175)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_176 old :
 (exists ground bits, VM.find 175 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_176.
Proof.
 intros [g175 [b175 H175]].
 unfold joint_update_expr_176.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_177 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 176)) (@Eref VarOrder.T (@Eid VarOrder.T 174))).
Lemma joint_update_ready_177 old :
 (exists ground bits, VM.find 174 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 176 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_177.
Proof.
 intros [g174 [b174 H174]].
 intros [g176 [b176 H176]].
 unfold joint_update_expr_177.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_178 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 177)) (@Eref VarOrder.T (@Eid VarOrder.T 173))).
Lemma joint_update_ready_178 old :
 (exists ground bits, VM.find 173 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 177 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_178.
Proof.
 intros [g173 [b173 H173]].
 intros [g177 [b177 H177]].
 unfold joint_update_expr_178.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_179 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_179 old :
 concrete_expression_ready old joint_update_expr_179.
Proof.
 unfold joint_update_expr_179.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_180 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 170)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_180 old :
 (exists ground bits, VM.find 170 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_180.
Proof.
 intros [g170 [b170 H170]].
 unfold joint_update_expr_180.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_181 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 180)) (@Eref VarOrder.T (@Eid VarOrder.T 179))).
Lemma joint_update_ready_181 old :
 (exists ground bits, VM.find 179 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 180 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_181.
Proof.
 intros [g179 [b179 H179]].
 intros [g180 [b180 H180]].
 unfold joint_update_expr_181.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_182 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_182 old :
 concrete_expression_ready old joint_update_expr_182.
Proof.
 unfold joint_update_expr_182.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_183 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Econst VarOrder.T (Fuint 24) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 168))).
Lemma joint_update_ready_183 old :
 (exists ground bits, VM.find 168 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_183.
Proof.
 intros [g168 [b168 H168]].
 unfold joint_update_expr_183.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_184 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 183)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_184 old :
 (exists ground bits, VM.find 183 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_184.
Proof.
 intros [g183 [b183 H183]].
 unfold joint_update_expr_184.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_185 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 184)) (@Eref VarOrder.T (@Eid VarOrder.T 182))).
Lemma joint_update_ready_185 old :
 (exists ground bits, VM.find 182 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 184 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_185.
Proof.
 intros [g182 [b182 H182]].
 intros [g184 [b184 H184]].
 unfold joint_update_expr_185.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_186 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 185)) (@Eref VarOrder.T (@Eid VarOrder.T 181))).
Lemma joint_update_ready_186 old :
 (exists ground bits, VM.find 181 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 185 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_186.
Proof.
 intros [g181 [b181 H181]].
 intros [g185 [b185 H185]].
 unfold joint_update_expr_186.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_194 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 131)) (@Eref VarOrder.T (@Eid VarOrder.T 132)) (@Eref VarOrder.T (@Eid VarOrder.T 193))).
Lemma joint_update_ready_194 old :
 (exists ground bits, VM.find 131 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 132 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 193 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_194.
Proof.
 intros [g131 [b131 H131]].
 intros [g132 [b132 H132]].
 intros [g193 [b193 H193]].
 unfold joint_update_expr_194.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_195 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_195 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_195.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_195.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_196 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 195))).
Lemma joint_update_ready_196 old :
 (exists ground bits, VM.find 195 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_196.
Proof.
 intros [g195 [b195 H195]].
 unfold joint_update_expr_196.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_197 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_197 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_197.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_197.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_198 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 197))).
Lemma joint_update_ready_198 old :
 (exists ground bits, VM.find 197 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_198.
Proof.
 intros [g197 [b197 H197]].
 unfold joint_update_expr_198.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_199 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_199 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_199.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_199.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_200 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 199))).
Lemma joint_update_ready_200 old :
 (exists ground bits, VM.find 199 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_200.
Proof.
 intros [g199 [b199 H199]].
 unfold joint_update_expr_200.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_201 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_201 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_201.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_201.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_202 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 201))).
Lemma joint_update_ready_202 old :
 (exists ground bits, VM.find 201 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_202.
Proof.
 intros [g201 [b201 H201]].
 unfold joint_update_expr_202.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_203 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_203 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_203.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_203.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_204 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 203))).
Lemma joint_update_ready_204 old :
 (exists ground bits, VM.find 203 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_204.
Proof.
 intros [g203 [b203 H203]].
 unfold joint_update_expr_204.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_205 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_205 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_205.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_205.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_206 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 205))).
Lemma joint_update_ready_206 old :
 (exists ground bits, VM.find 205 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_206.
Proof.
 intros [g205 [b205 H205]].
 unfold joint_update_expr_206.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_207 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_207 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_207.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_207.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_208 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 207))).
Lemma joint_update_ready_208 old :
 (exists ground bits, VM.find 207 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_208.
Proof.
 intros [g207 [b207 H207]].
 unfold joint_update_expr_208.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_209 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_209 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_209.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_209.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_210 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 209))).
Lemma joint_update_ready_210 old :
 (exists ground bits, VM.find 209 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_210.
Proof.
 intros [g209 [b209 H209]].
 unfold joint_update_expr_210.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_211 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_211 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_211.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_211.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_212 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 211))).
Lemma joint_update_ready_212 old :
 (exists ground bits, VM.find 211 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_212.
Proof.
 intros [g211 [b211 H211]].
 unfold joint_update_expr_212.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_213 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_213 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_213.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_213.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_214 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 213))).
Lemma joint_update_ready_214 old :
 (exists ground bits, VM.find 213 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_214.
Proof.
 intros [g213 [b213 H213]].
 unfold joint_update_expr_214.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_215 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_215 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_215.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_215.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_216 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 215))).
Lemma joint_update_ready_216 old :
 (exists ground bits, VM.find 215 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_216.
Proof.
 intros [g215 [b215 H215]].
 unfold joint_update_expr_216.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_217 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_217 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_217.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_217.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_218 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 217))).
Lemma joint_update_ready_218 old :
 (exists ground bits, VM.find 217 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_218.
Proof.
 intros [g217 [b217 H217]].
 unfold joint_update_expr_218.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_219 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_219 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_219.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_219.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_220 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 219))).
Lemma joint_update_ready_220 old :
 (exists ground bits, VM.find 219 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_220.
Proof.
 intros [g219 [b219 H219]].
 unfold joint_update_expr_220.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_221 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_221 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_221.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_221.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_222 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 221))).
Lemma joint_update_ready_222 old :
 (exists ground bits, VM.find 221 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_222.
Proof.
 intros [g221 [b221 H221]].
 unfold joint_update_expr_222.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_223 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_223 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_223.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_223.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_224 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; true; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 223))).
Lemma joint_update_ready_224 old :
 (exists ground bits, VM.find 223 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_224.
Proof.
 intros [g223 [b223 H223]].
 unfold joint_update_expr_224.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_225 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_225 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_225.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_225.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_226 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 225))).
Lemma joint_update_ready_226 old :
 (exists ground bits, VM.find 225 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_226.
Proof.
 intros [g225 [b225 H225]].
 unfold joint_update_expr_226.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_227 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_227 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_227.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_227.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_228 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; true; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 227))).
Lemma joint_update_ready_228 old :
 (exists ground bits, VM.find 227 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_228.
Proof.
 intros [g227 [b227 H227]].
 unfold joint_update_expr_228.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_229 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_229 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_229.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_229.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_230 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; true; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 229))).
Lemma joint_update_ready_230 old :
 (exists ground bits, VM.find 229 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_230.
Proof.
 intros [g229 [b229 H229]].
 unfold joint_update_expr_230.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_231 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_231 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_231.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_231.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_232 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 231))).
Lemma joint_update_ready_232 old :
 (exists ground bits, VM.find 231 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_232.
Proof.
 intros [g231 [b231 H231]].
 unfold joint_update_expr_232.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_233 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_233 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_233.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_233.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_234 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::true; false; false; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 233))).
Lemma joint_update_ready_234 old :
 (exists ground bits, VM.find 233 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_234.
Proof.
 intros [g233 [b233 H233]].
 unfold joint_update_expr_234.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_235 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_235 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_235.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_235.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_236 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::true; false; false; false; false; false; true; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 235))).
Lemma joint_update_ready_236 old :
 (exists ground bits, VM.find 235 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_236.
Proof.
 intros [g235 [b235 H235]].
 unfold joint_update_expr_236.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_237 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_237 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_237.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_237.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_238 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 237))).
Lemma joint_update_ready_238 old :
 (exists ground bits, VM.find 237 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_238.
Proof.
 intros [g237 [b237 H237]].
 unfold joint_update_expr_238.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_239 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_239 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_239.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_239.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_240 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; false; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 239))).
Lemma joint_update_ready_240 old :
 (exists ground bits, VM.find 239 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_240.
Proof.
 intros [g239 [b239 H239]].
 unfold joint_update_expr_240.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_241 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_241 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_241.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_241.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_242 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; true; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 241))).
Lemma joint_update_ready_242 old :
 (exists ground bits, VM.find 241 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_242.
Proof.
 intros [g241 [b241 H241]].
 unfold joint_update_expr_242.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_243 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_243 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_243.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_243.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_244 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; true; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 243))).
Lemma joint_update_ready_244 old :
 (exists ground bits, VM.find 243 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_244.
Proof.
 intros [g243 [b243 H243]].
 unfold joint_update_expr_244.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_245 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_245 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_245.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_245.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_246 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; true; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 245))).
Lemma joint_update_ready_246 old :
 (exists ground bits, VM.find 245 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_246.
Proof.
 intros [g245 [b245 H245]].
 unfold joint_update_expr_246.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_247 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_247 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_247.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_247.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_248 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::false; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 247))).
Lemma joint_update_ready_248 old :
 (exists ground bits, VM.find 247 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_248.
Proof.
 intros [g247 [b247 H247]].
 unfold joint_update_expr_248.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_249 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_249 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_249.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_249.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_250 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::true; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 249))).
Lemma joint_update_ready_250 old :
 (exists ground bits, VM.find 249 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_250.
Proof.
 intros [g249 [b249 H249]].
 unfold joint_update_expr_250.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_251 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_251 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_251.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_251.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_252 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 251))).
Lemma joint_update_ready_252 old :
 (exists ground bits, VM.find 251 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_252.
Proof.
 intros [g251 [b251 H251]].
 unfold joint_update_expr_252.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_253 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 252)) (@Eref VarOrder.T (@Eid VarOrder.T 166)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_253 old :
 (exists ground bits, VM.find 166 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 252 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_253.
Proof.
 intros [g166 [b166 H166]].
 intros [g252 [b252 H252]].
 unfold joint_update_expr_253.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_254 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 250)) (@Eref VarOrder.T (@Eid VarOrder.T 193)) (@Eref VarOrder.T (@Eid VarOrder.T 253))).
Lemma joint_update_ready_254 old :
 (exists ground bits, VM.find 193 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 250 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 253 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_254.
Proof.
 intros [g193 [b193 H193]].
 intros [g250 [b250 H250]].
 intros [g253 [b253 H253]].
 unfold joint_update_expr_254.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_255 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 248)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 254))).
Lemma joint_update_ready_255 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 248 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 254 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_255.
Proof.
 intros [g192 [b192 H192]].
 intros [g248 [b248 H248]].
 intros [g254 [b254 H254]].
 unfold joint_update_expr_255.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_256 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 246)) (@Eref VarOrder.T (@Eid VarOrder.T 178)) (@Eref VarOrder.T (@Eid VarOrder.T 255))).
Lemma joint_update_ready_256 old :
 (exists ground bits, VM.find 178 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 246 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 255 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_256.
Proof.
 intros [g178 [b178 H178]].
 intros [g246 [b246 H246]].
 intros [g255 [b255 H255]].
 unfold joint_update_expr_256.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_257 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 244)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 256))).
Lemma joint_update_ready_257 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 244 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 256 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_257.
Proof.
 intros [g191 [b191 H191]].
 intros [g244 [b244 H244]].
 intros [g256 [b256 H256]].
 unfold joint_update_expr_257.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_258 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 242)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 257))).
Lemma joint_update_ready_258 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 242 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 257 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_258.
Proof.
 intros [g190 [b190 H190]].
 intros [g242 [b242 H242]].
 intros [g257 [b257 H257]].
 unfold joint_update_expr_258.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_259 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 240)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 258))).
Lemma joint_update_ready_259 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 240 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 258 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_259.
Proof.
 intros [g189 [b189 H189]].
 intros [g240 [b240 H240]].
 intros [g258 [b258 H258]].
 unfold joint_update_expr_259.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_260 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 238)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 259))).
Lemma joint_update_ready_260 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 238 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 259 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_260.
Proof.
 intros [g188 [b188 H188]].
 intros [g238 [b238 H238]].
 intros [g259 [b259 H259]].
 unfold joint_update_expr_260.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_261 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 236)) (@Eref VarOrder.T (@Eid VarOrder.T 143)) (@Eref VarOrder.T (@Eid VarOrder.T 260))).
Lemma joint_update_ready_261 old :
 (exists ground bits, VM.find 143 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 236 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 260 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_261.
Proof.
 intros [g143 [b143 H143]].
 intros [g236 [b236 H236]].
 intros [g260 [b260 H260]].
 unfold joint_update_expr_261.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_262 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 234)) (@Eref VarOrder.T (@Eid VarOrder.T 142)) (@Eref VarOrder.T (@Eid VarOrder.T 261))).
Lemma joint_update_ready_262 old :
 (exists ground bits, VM.find 142 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 234 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 261 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_262.
Proof.
 intros [g142 [b142 H142]].
 intros [g234 [b234 H234]].
 intros [g261 [b261 H261]].
 unfold joint_update_expr_262.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_263 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 232)) (@Eref VarOrder.T (@Eid VarOrder.T 187)) (@Eref VarOrder.T (@Eid VarOrder.T 262))).
Lemma joint_update_ready_263 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 232 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 262 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_263.
Proof.
 intros [g187 [b187 H187]].
 intros [g232 [b232 H232]].
 intros [g262 [b262 H262]].
 unfold joint_update_expr_263.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_264 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 230)) (@Eref VarOrder.T (@Eid VarOrder.T 186)) (@Eref VarOrder.T (@Eid VarOrder.T 263))).
Lemma joint_update_ready_264 old :
 (exists ground bits, VM.find 186 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 230 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 263 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_264.
Proof.
 intros [g186 [b186 H186]].
 intros [g230 [b230 H230]].
 intros [g263 [b263 H263]].
 unfold joint_update_expr_264.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_265 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 228)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 264))).
Lemma joint_update_ready_265 old :
 (exists ground bits, VM.find 228 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 264 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_265.
Proof.
 intros [g228 [b228 H228]].
 intros [g264 [b264 H264]].
 unfold joint_update_expr_265.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_266 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 226)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 265))).
Lemma joint_update_ready_266 old :
 (exists ground bits, VM.find 226 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 265 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_266.
Proof.
 intros [g226 [b226 H226]].
 intros [g265 [b265 H265]].
 unfold joint_update_expr_266.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_267 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 224)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 266))).
Lemma joint_update_ready_267 old :
 (exists ground bits, VM.find 224 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 266 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_267.
Proof.
 intros [g224 [b224 H224]].
 intros [g266 [b266 H266]].
 unfold joint_update_expr_267.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_268 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 222)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 267))).
Lemma joint_update_ready_268 old :
 (exists ground bits, VM.find 222 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 267 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_268.
Proof.
 intros [g222 [b222 H222]].
 intros [g267 [b267 H267]].
 unfold joint_update_expr_268.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_269 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 220)) (@Eref VarOrder.T (@Eid VarOrder.T 149)) (@Eref VarOrder.T (@Eid VarOrder.T 268))).
Lemma joint_update_ready_269 old :
 (exists ground bits, VM.find 149 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 220 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 268 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_269.
Proof.
 intros [g149 [b149 H149]].
 intros [g220 [b220 H220]].
 intros [g268 [b268 H268]].
 unfold joint_update_expr_269.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_270 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 218)) (@Eref VarOrder.T (@Eid VarOrder.T 147)) (@Eref VarOrder.T (@Eid VarOrder.T 269))).
Lemma joint_update_ready_270 old :
 (exists ground bits, VM.find 147 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 218 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 269 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_270.
Proof.
 intros [g147 [b147 H147]].
 intros [g218 [b218 H218]].
 intros [g269 [b269 H269]].
 unfold joint_update_expr_270.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_271 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 216)) (@Eref VarOrder.T (@Eid VarOrder.T 143)) (@Eref VarOrder.T (@Eid VarOrder.T 270))).
Lemma joint_update_ready_271 old :
 (exists ground bits, VM.find 143 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 216 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 270 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_271.
Proof.
 intros [g143 [b143 H143]].
 intros [g216 [b216 H216]].
 intros [g270 [b270 H270]].
 unfold joint_update_expr_271.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_272 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 214)) (@Eref VarOrder.T (@Eid VarOrder.T 145)) (@Eref VarOrder.T (@Eid VarOrder.T 271))).
Lemma joint_update_ready_272 old :
 (exists ground bits, VM.find 145 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 214 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 271 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_272.
Proof.
 intros [g145 [b145 H145]].
 intros [g214 [b214 H214]].
 intros [g271 [b271 H271]].
 unfold joint_update_expr_272.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_273 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 212)) (@Eref VarOrder.T (@Eid VarOrder.T 146)) (@Eref VarOrder.T (@Eid VarOrder.T 272))).
Lemma joint_update_ready_273 old :
 (exists ground bits, VM.find 146 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 212 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 272 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_273.
Proof.
 intros [g146 [b146 H146]].
 intros [g212 [b212 H212]].
 intros [g272 [b272 H272]].
 unfold joint_update_expr_273.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_274 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 210)) (@Eref VarOrder.T (@Eid VarOrder.T 142)) (@Eref VarOrder.T (@Eid VarOrder.T 273))).
Lemma joint_update_ready_274 old :
 (exists ground bits, VM.find 142 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 210 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 273 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_274.
Proof.
 intros [g142 [b142 H142]].
 intros [g210 [b210 H210]].
 intros [g273 [b273 H273]].
 unfold joint_update_expr_274.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_275 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 208)) (@Eref VarOrder.T (@Eid VarOrder.T 144)) (@Eref VarOrder.T (@Eid VarOrder.T 274))).
Lemma joint_update_ready_275 old :
 (exists ground bits, VM.find 144 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 208 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 274 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_275.
Proof.
 intros [g144 [b144 H144]].
 intros [g208 [b208 H208]].
 intros [g274 [b274 H274]].
 unfold joint_update_expr_275.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_276 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 206)) (@Eref VarOrder.T (@Eid VarOrder.T 147)) (@Eref VarOrder.T (@Eid VarOrder.T 275))).
Lemma joint_update_ready_276 old :
 (exists ground bits, VM.find 147 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 206 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 275 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_276.
Proof.
 intros [g147 [b147 H147]].
 intros [g206 [b206 H206]].
 intros [g275 [b275 H275]].
 unfold joint_update_expr_276.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_277 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 204)) (@Eref VarOrder.T (@Eid VarOrder.T 143)) (@Eref VarOrder.T (@Eid VarOrder.T 276))).
Lemma joint_update_ready_277 old :
 (exists ground bits, VM.find 143 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 204 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 276 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_277.
Proof.
 intros [g143 [b143 H143]].
 intros [g204 [b204 H204]].
 intros [g276 [b276 H276]].
 unfold joint_update_expr_277.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_278 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 202)) (@Eref VarOrder.T (@Eid VarOrder.T 145)) (@Eref VarOrder.T (@Eid VarOrder.T 277))).
Lemma joint_update_ready_278 old :
 (exists ground bits, VM.find 145 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 202 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 277 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_278.
Proof.
 intros [g145 [b145 H145]].
 intros [g202 [b202 H202]].
 intros [g277 [b277 H277]].
 unfold joint_update_expr_278.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_279 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 200)) (@Eref VarOrder.T (@Eid VarOrder.T 146)) (@Eref VarOrder.T (@Eid VarOrder.T 278))).
Lemma joint_update_ready_279 old :
 (exists ground bits, VM.find 146 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 200 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 278 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_279.
Proof.
 intros [g146 [b146 H146]].
 intros [g200 [b200 H200]].
 intros [g278 [b278 H278]].
 unfold joint_update_expr_279.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_280 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 198)) (@Eref VarOrder.T (@Eid VarOrder.T 142)) (@Eref VarOrder.T (@Eid VarOrder.T 279))).
Lemma joint_update_ready_280 old :
 (exists ground bits, VM.find 142 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 198 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 279 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_280.
Proof.
 intros [g142 [b142 H142]].
 intros [g198 [b198 H198]].
 intros [g279 [b279 H279]].
 unfold joint_update_expr_280.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_281 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 196)) (@Eref VarOrder.T (@Eid VarOrder.T 144)) (@Eref VarOrder.T (@Eid VarOrder.T 280))).
Lemma joint_update_ready_281 old :
 (exists ground bits, VM.find 144 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 196 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 280 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_281.
Proof.
 intros [g144 [b144 H144]].
 intros [g196 [b196 H196]].
 intros [g280 [b280 H280]].
 unfold joint_update_expr_281.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_282 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 9 8) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma joint_update_ready_282 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_282.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_282.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_283 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Bleq) (@Eref VarOrder.T (@Eid VarOrder.T 282)) (@Eref VarOrder.T (@Eid VarOrder.T 150))).
Lemma joint_update_ready_283 old :
 (exists ground bits, VM.find 150 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 282 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_283.
Proof.
 intros [g150 [b150 H150]].
 intros [g282 [b282 H282]].
 unfold joint_update_expr_283.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_284 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 118)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Lemma joint_update_ready_284 old :
 (exists ground bits, VM.find 118 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_284.
Proof.
 intros [g118 [b118 H118]].
 unfold joint_update_expr_284.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_285 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma joint_update_ready_285 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_285.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_285.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_286 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 285)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_286 old :
 (exists ground bits, VM.find 285 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_286.
Proof.
 intros [g285 [b285 H285]].
 unfold joint_update_expr_286.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_287 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 284)) (@Eref VarOrder.T (@Eid VarOrder.T 286))).
Lemma joint_update_ready_287 old :
 (exists ground bits, VM.find 284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 286 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_287.
Proof.
 intros [g284 [b284 H284]].
 intros [g286 [b286 H286]].
 unfold joint_update_expr_287.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_288 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma joint_update_ready_288 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_288.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_288.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_289 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 288)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_289 old :
 (exists ground bits, VM.find 288 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_289.
Proof.
 intros [g288 [b288 H288]].
 unfold joint_update_expr_289.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_290 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 287)) (@Eref VarOrder.T (@Eid VarOrder.T 289))).
Lemma joint_update_ready_290 old :
 (exists ground bits, VM.find 287 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 289 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_290.
Proof.
 intros [g287 [b287 H287]].
 intros [g289 [b289 H289]].
 unfold joint_update_expr_290.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_291 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma joint_update_ready_291 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_291.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_291.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_292 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 284)) (@Eref VarOrder.T (@Eid VarOrder.T 291))).
Lemma joint_update_ready_292 old :
 (exists ground bits, VM.find 284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 291 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_292.
Proof.
 intros [g284 [b284 H284]].
 intros [g291 [b291 H291]].
 unfold joint_update_expr_292.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_293 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma joint_update_ready_293 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_293.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_293.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_294 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 293)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_294 old :
 (exists ground bits, VM.find 293 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_294.
Proof.
 intros [g293 [b293 H293]].
 unfold joint_update_expr_294.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_295 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 292)) (@Eref VarOrder.T (@Eid VarOrder.T 294))).
Lemma joint_update_ready_295 old :
 (exists ground bits, VM.find 292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 294 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_295.
Proof.
 intros [g292 [b292 H292]].
 intros [g294 [b294 H294]].
 unfold joint_update_expr_295.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_296 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma joint_update_ready_296 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_296.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_296.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_297 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 296)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_297 old :
 (exists ground bits, VM.find 296 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_297.
Proof.
 intros [g296 [b296 H296]].
 unfold joint_update_expr_297.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_298 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 284)) (@Eref VarOrder.T (@Eid VarOrder.T 297))).
Lemma joint_update_ready_298 old :
 (exists ground bits, VM.find 284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 297 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_298.
Proof.
 intros [g284 [b284 H284]].
 intros [g297 [b297 H297]].
 unfold joint_update_expr_298.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_299 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma joint_update_ready_299 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_299.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_299.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_300 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 298)) (@Eref VarOrder.T (@Eid VarOrder.T 299))).
Lemma joint_update_ready_300 old :
 (exists ground bits, VM.find 298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 299 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_300.
Proof.
 intros [g298 [b298 H298]].
 intros [g299 [b299 H299]].
 unfold joint_update_expr_300.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_301 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_301 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_301.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_301.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_302 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 301))).
Lemma joint_update_ready_302 old :
 (exists ground bits, VM.find 301 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_302.
Proof.
 intros [g301 [b301 H301]].
 unfold joint_update_expr_302.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_303 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_303 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_303.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_303.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_304 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 303))).
Lemma joint_update_ready_304 old :
 (exists ground bits, VM.find 303 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_304.
Proof.
 intros [g303 [b303 H303]].
 unfold joint_update_expr_304.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_305 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_305 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_305.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_305.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_306 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 305))).
Lemma joint_update_ready_306 old :
 (exists ground bits, VM.find 305 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_306.
Proof.
 intros [g305 [b305 H305]].
 unfold joint_update_expr_306.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_307 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_307 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_307.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_307.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_308 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 307))).
Lemma joint_update_ready_308 old :
 (exists ground bits, VM.find 307 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_308.
Proof.
 intros [g307 [b307 H307]].
 unfold joint_update_expr_308.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_309 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_309 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_309.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_309.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_310 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 309))).
Lemma joint_update_ready_310 old :
 (exists ground bits, VM.find 309 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_310.
Proof.
 intros [g309 [b309 H309]].
 unfold joint_update_expr_310.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_311 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_311 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_311.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_311.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_312 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 311))).
Lemma joint_update_ready_312 old :
 (exists ground bits, VM.find 311 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_312.
Proof.
 intros [g311 [b311 H311]].
 unfold joint_update_expr_312.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_313 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_313 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_313.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_313.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_314 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 313))).
Lemma joint_update_ready_314 old :
 (exists ground bits, VM.find 313 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_314.
Proof.
 intros [g313 [b313 H313]].
 unfold joint_update_expr_314.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_315 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_315 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_315.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_315.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_316 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 315))).
Lemma joint_update_ready_316 old :
 (exists ground bits, VM.find 315 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_316.
Proof.
 intros [g315 [b315 H315]].
 unfold joint_update_expr_316.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_317 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_317 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_317.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_317.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_318 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 317))).
Lemma joint_update_ready_318 old :
 (exists ground bits, VM.find 317 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_318.
Proof.
 intros [g317 [b317 H317]].
 unfold joint_update_expr_318.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_319 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_319 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_319.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_319.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_320 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 319))).
Lemma joint_update_ready_320 old :
 (exists ground bits, VM.find 319 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_320.
Proof.
 intros [g319 [b319 H319]].
 unfold joint_update_expr_320.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_321 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_321 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_321.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_321.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_322 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 321))).
Lemma joint_update_ready_322 old :
 (exists ground bits, VM.find 321 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_322.
Proof.
 intros [g321 [b321 H321]].
 unfold joint_update_expr_322.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_323 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_323 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_323.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_323.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_324 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 323))).
Lemma joint_update_ready_324 old :
 (exists ground bits, VM.find 323 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_324.
Proof.
 intros [g323 [b323 H323]].
 unfold joint_update_expr_324.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_325 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_325 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_325.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_325.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_326 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 325))).
Lemma joint_update_ready_326 old :
 (exists ground bits, VM.find 325 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_326.
Proof.
 intros [g325 [b325 H325]].
 unfold joint_update_expr_326.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_327 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_327 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_327.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_327.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_328 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 327))).
Lemma joint_update_ready_328 old :
 (exists ground bits, VM.find 327 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_328.
Proof.
 intros [g327 [b327 H327]].
 unfold joint_update_expr_328.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_329 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_329 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_329.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_329.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_330 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; true; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 329))).
Lemma joint_update_ready_330 old :
 (exists ground bits, VM.find 329 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_330.
Proof.
 intros [g329 [b329 H329]].
 unfold joint_update_expr_330.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_331 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_331 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_331.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_331.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_332 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 331))).
Lemma joint_update_ready_332 old :
 (exists ground bits, VM.find 331 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_332.
Proof.
 intros [g331 [b331 H331]].
 unfold joint_update_expr_332.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_333 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_333 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_333.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_333.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_334 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; true; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 333))).
Lemma joint_update_ready_334 old :
 (exists ground bits, VM.find 333 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_334.
Proof.
 intros [g333 [b333 H333]].
 unfold joint_update_expr_334.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_335 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_335 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_335.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_335.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_336 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; true; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 335))).
Lemma joint_update_ready_336 old :
 (exists ground bits, VM.find 335 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_336.
Proof.
 intros [g335 [b335 H335]].
 unfold joint_update_expr_336.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_337 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_337 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_337.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_337.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_338 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 337))).
Lemma joint_update_ready_338 old :
 (exists ground bits, VM.find 337 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_338.
Proof.
 intros [g337 [b337 H337]].
 unfold joint_update_expr_338.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_339 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_339 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_339.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_339.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_340 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::true; false; false; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 339))).
Lemma joint_update_ready_340 old :
 (exists ground bits, VM.find 339 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_340.
Proof.
 intros [g339 [b339 H339]].
 unfold joint_update_expr_340.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_341 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_341 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_341.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_341.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_342 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::true; false; false; false; false; false; true; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 341))).
Lemma joint_update_ready_342 old :
 (exists ground bits, VM.find 341 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_342.
Proof.
 intros [g341 [b341 H341]].
 unfold joint_update_expr_342.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_343 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_343 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_343.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_343.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_344 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 343))).
Lemma joint_update_ready_344 old :
 (exists ground bits, VM.find 343 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_344.
Proof.
 intros [g343 [b343 H343]].
 unfold joint_update_expr_344.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_345 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_345 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_345.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_345.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_346 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; false; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 345))).
Lemma joint_update_ready_346 old :
 (exists ground bits, VM.find 345 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_346.
Proof.
 intros [g345 [b345 H345]].
 unfold joint_update_expr_346.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_347 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_347 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_347.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_347.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_348 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; true; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 347))).
Lemma joint_update_ready_348 old :
 (exists ground bits, VM.find 347 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_348.
Proof.
 intros [g347 [b347 H347]].
 unfold joint_update_expr_348.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_349 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_349 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_349.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_349.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_350 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; true; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 349))).
Lemma joint_update_ready_350 old :
 (exists ground bits, VM.find 349 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_350.
Proof.
 intros [g349 [b349 H349]].
 unfold joint_update_expr_350.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_351 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_351 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_351.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_351.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_352 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; true; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 351))).
Lemma joint_update_ready_352 old :
 (exists ground bits, VM.find 351 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_352.
Proof.
 intros [g351 [b351 H351]].
 unfold joint_update_expr_352.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_353 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_353 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_353.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_353.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_354 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::false; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 353))).
Lemma joint_update_ready_354 old :
 (exists ground bits, VM.find 353 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_354.
Proof.
 intros [g353 [b353 H353]].
 unfold joint_update_expr_354.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_355 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_355 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_355.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_355.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_356 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::true; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 355))).
Lemma joint_update_ready_356 old :
 (exists ground bits, VM.find 355 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_356.
Proof.
 intros [g355 [b355 H355]].
 unfold joint_update_expr_356.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_357 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_357 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_357.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_357.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_358 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 357))).
Lemma joint_update_ready_358 old :
 (exists ground bits, VM.find 357 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_358.
Proof.
 intros [g357 [b357 H357]].
 unfold joint_update_expr_358.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_359 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 302)) (@Eref VarOrder.T (@Eid VarOrder.T 304))).
Lemma joint_update_ready_359 old :
 (exists ground bits, VM.find 302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 304 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_359.
Proof.
 intros [g302 [b302 H302]].
 intros [g304 [b304 H304]].
 unfold joint_update_expr_359.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_360 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 359)) (@Eref VarOrder.T (@Eid VarOrder.T 306))).
Lemma joint_update_ready_360 old :
 (exists ground bits, VM.find 306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 359 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_360.
Proof.
 intros [g306 [b306 H306]].
 intros [g359 [b359 H359]].
 unfold joint_update_expr_360.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_361 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 360)) (@Eref VarOrder.T (@Eid VarOrder.T 308))).
Lemma joint_update_ready_361 old :
 (exists ground bits, VM.find 308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_361.
Proof.
 intros [g308 [b308 H308]].
 intros [g360 [b360 H360]].
 unfold joint_update_expr_361.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_362 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 361)) (@Eref VarOrder.T (@Eid VarOrder.T 310))).
Lemma joint_update_ready_362 old :
 (exists ground bits, VM.find 310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 361 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_362.
Proof.
 intros [g310 [b310 H310]].
 intros [g361 [b361 H361]].
 unfold joint_update_expr_362.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_363 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 362)) (@Eref VarOrder.T (@Eid VarOrder.T 312))).
Lemma joint_update_ready_363 old :
 (exists ground bits, VM.find 312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 362 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_363.
Proof.
 intros [g312 [b312 H312]].
 intros [g362 [b362 H362]].
 unfold joint_update_expr_363.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_364 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 363)) (@Eref VarOrder.T (@Eid VarOrder.T 314))).
Lemma joint_update_ready_364 old :
 (exists ground bits, VM.find 314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 363 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_364.
Proof.
 intros [g314 [b314 H314]].
 intros [g363 [b363 H363]].
 unfold joint_update_expr_364.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_365 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 364)) (@Eref VarOrder.T (@Eid VarOrder.T 316))).
Lemma joint_update_ready_365 old :
 (exists ground bits, VM.find 316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 364 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_365.
Proof.
 intros [g316 [b316 H316]].
 intros [g364 [b364 H364]].
 unfold joint_update_expr_365.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_366 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 365)) (@Eref VarOrder.T (@Eid VarOrder.T 318))).
Lemma joint_update_ready_366 old :
 (exists ground bits, VM.find 318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 365 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_366.
Proof.
 intros [g318 [b318 H318]].
 intros [g365 [b365 H365]].
 unfold joint_update_expr_366.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_367 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 366)) (@Eref VarOrder.T (@Eid VarOrder.T 320))).
Lemma joint_update_ready_367 old :
 (exists ground bits, VM.find 320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 366 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_367.
Proof.
 intros [g320 [b320 H320]].
 intros [g366 [b366 H366]].
 unfold joint_update_expr_367.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_368 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 367)) (@Eref VarOrder.T (@Eid VarOrder.T 322))).
Lemma joint_update_ready_368 old :
 (exists ground bits, VM.find 322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 367 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_368.
Proof.
 intros [g322 [b322 H322]].
 intros [g367 [b367 H367]].
 unfold joint_update_expr_368.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_369 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 368)) (@Eref VarOrder.T (@Eid VarOrder.T 324))).
Lemma joint_update_ready_369 old :
 (exists ground bits, VM.find 324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 368 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_369.
Proof.
 intros [g324 [b324 H324]].
 intros [g368 [b368 H368]].
 unfold joint_update_expr_369.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_370 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 369)) (@Eref VarOrder.T (@Eid VarOrder.T 326))).
Lemma joint_update_ready_370 old :
 (exists ground bits, VM.find 326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 369 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_370.
Proof.
 intros [g326 [b326 H326]].
 intros [g369 [b369 H369]].
 unfold joint_update_expr_370.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_371 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 370)) (@Eref VarOrder.T (@Eid VarOrder.T 328))).
Lemma joint_update_ready_371 old :
 (exists ground bits, VM.find 328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 370 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_371.
Proof.
 intros [g328 [b328 H328]].
 intros [g370 [b370 H370]].
 unfold joint_update_expr_371.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_372 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 371)) (@Eref VarOrder.T (@Eid VarOrder.T 330))).
Lemma joint_update_ready_372 old :
 (exists ground bits, VM.find 330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 371 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_372.
Proof.
 intros [g330 [b330 H330]].
 intros [g371 [b371 H371]].
 unfold joint_update_expr_372.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_373 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 372)) (@Eref VarOrder.T (@Eid VarOrder.T 332))).
Lemma joint_update_ready_373 old :
 (exists ground bits, VM.find 332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 372 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_373.
Proof.
 intros [g332 [b332 H332]].
 intros [g372 [b372 H372]].
 unfold joint_update_expr_373.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_374 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 373)) (@Eref VarOrder.T (@Eid VarOrder.T 334))).
Lemma joint_update_ready_374 old :
 (exists ground bits, VM.find 334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 373 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_374.
Proof.
 intros [g334 [b334 H334]].
 intros [g373 [b373 H373]].
 unfold joint_update_expr_374.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_375 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 374)) (@Eref VarOrder.T (@Eid VarOrder.T 336))).
Lemma joint_update_ready_375 old :
 (exists ground bits, VM.find 336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 374 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_375.
Proof.
 intros [g336 [b336 H336]].
 intros [g374 [b374 H374]].
 unfold joint_update_expr_375.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_376 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 375)) (@Eref VarOrder.T (@Eid VarOrder.T 338))).
Lemma joint_update_ready_376 old :
 (exists ground bits, VM.find 338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 375 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_376.
Proof.
 intros [g338 [b338 H338]].
 intros [g375 [b375 H375]].
 unfold joint_update_expr_376.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_377 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 376)) (@Eref VarOrder.T (@Eid VarOrder.T 340))).
Lemma joint_update_ready_377 old :
 (exists ground bits, VM.find 340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 376 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_377.
Proof.
 intros [g340 [b340 H340]].
 intros [g376 [b376 H376]].
 unfold joint_update_expr_377.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_378 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 377)) (@Eref VarOrder.T (@Eid VarOrder.T 342))).
Lemma joint_update_ready_378 old :
 (exists ground bits, VM.find 342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 377 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_378.
Proof.
 intros [g342 [b342 H342]].
 intros [g377 [b377 H377]].
 unfold joint_update_expr_378.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_379 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 378)) (@Eref VarOrder.T (@Eid VarOrder.T 344))).
Lemma joint_update_ready_379 old :
 (exists ground bits, VM.find 344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 378 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_379.
Proof.
 intros [g344 [b344 H344]].
 intros [g378 [b378 H378]].
 unfold joint_update_expr_379.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_380 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 379)) (@Eref VarOrder.T (@Eid VarOrder.T 346))).
Lemma joint_update_ready_380 old :
 (exists ground bits, VM.find 346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 379 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_380.
Proof.
 intros [g346 [b346 H346]].
 intros [g379 [b379 H379]].
 unfold joint_update_expr_380.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_381 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 380)) (@Eref VarOrder.T (@Eid VarOrder.T 348))).
Lemma joint_update_ready_381 old :
 (exists ground bits, VM.find 348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 380 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_381.
Proof.
 intros [g348 [b348 H348]].
 intros [g380 [b380 H380]].
 unfold joint_update_expr_381.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_382 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 381)) (@Eref VarOrder.T (@Eid VarOrder.T 350))).
Lemma joint_update_ready_382 old :
 (exists ground bits, VM.find 350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 381 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_382.
Proof.
 intros [g350 [b350 H350]].
 intros [g381 [b381 H381]].
 unfold joint_update_expr_382.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_383 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 382)) (@Eref VarOrder.T (@Eid VarOrder.T 352))).
Lemma joint_update_ready_383 old :
 (exists ground bits, VM.find 352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 382 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_383.
Proof.
 intros [g352 [b352 H352]].
 intros [g382 [b382 H382]].
 unfold joint_update_expr_383.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_384 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 383)) (@Eref VarOrder.T (@Eid VarOrder.T 354))).
Lemma joint_update_ready_384 old :
 (exists ground bits, VM.find 354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 383 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_384.
Proof.
 intros [g354 [b354 H354]].
 intros [g383 [b383 H383]].
 unfold joint_update_expr_384.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_385 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 384)) (@Eref VarOrder.T (@Eid VarOrder.T 356))).
Lemma joint_update_ready_385 old :
 (exists ground bits, VM.find 356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 384 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_385.
Proof.
 intros [g356 [b356 H356]].
 intros [g384 [b384 H384]].
 unfold joint_update_expr_385.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_386 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 385)) (@Eref VarOrder.T (@Eid VarOrder.T 358))).
Lemma joint_update_ready_386 old :
 (exists ground bits, VM.find 358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 385 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_386.
Proof.
 intros [g358 [b358 H358]].
 intros [g385 [b385 H385]].
 unfold joint_update_expr_386.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_387 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 10) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma joint_update_ready_387 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_387.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_387.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_388 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uandr (@Eref VarOrder.T (@Eid VarOrder.T 387))).
Lemma joint_update_ready_388 old :
 (exists ground bits, VM.find 387 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_388.
Proof.
 intros [g387 [b387 H387]].
 unfold joint_update_expr_388.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_389 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; true; false; false])).
Lemma joint_update_ready_389 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_389.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_389.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_390 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 388)) (@Eref VarOrder.T (@Eid VarOrder.T 389))).
Lemma joint_update_ready_390 old :
 (exists ground bits, VM.find 388 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 389 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_390.
Proof.
 intros [g388 [b388 H388]].
 intros [g389 [b389 H389]].
 unfold joint_update_expr_390.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_391 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; false; true; true; false; false])).
Lemma joint_update_ready_391 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_391.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_391.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_392 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 390)) (@Eref VarOrder.T (@Eid VarOrder.T 391))).
Lemma joint_update_ready_392 old :
 (exists ground bits, VM.find 390 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 391 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_392.
Proof.
 intros [g390 [b390 H390]].
 intros [g391 [b391 H391]].
 unfold joint_update_expr_392.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_393 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 118)) (@Econst VarOrder.T (Fuint 3) [::true; false; false])).
Lemma joint_update_ready_393 old :
 (exists ground bits, VM.find 118 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_393.
Proof.
 intros [g118 [b118 H118]].
 unfold joint_update_expr_393.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_394 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 118))).
Lemma joint_update_ready_394 old :
 (exists ground bits, VM.find 118 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_394.
Proof.
 intros [g118 [b118 H118]].
 unfold joint_update_expr_394.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_395 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 141))).
Lemma joint_update_ready_395 old :
 (exists ground bits, VM.find 141 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_395.
Proof.
 intros [g141 [b141 H141]].
 unfold joint_update_expr_395.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_396 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 394)) (@Eref VarOrder.T (@Eid VarOrder.T 395))).
Lemma joint_update_ready_396 old :
 (exists ground bits, VM.find 394 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 395 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_396.
Proof.
 intros [g394 [b394 H394]].
 intros [g395 [b395 H395]].
 unfold joint_update_expr_396.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_397 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 393)) (@Eref VarOrder.T (@Eid VarOrder.T 396))).
Lemma joint_update_ready_397 old :
 (exists ground bits, VM.find 393 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 396 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_397.
Proof.
 intros [g393 [b393 H393]].
 intros [g396 [b396 H396]].
 unfold joint_update_expr_397.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_398 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 120)) (@Eref VarOrder.T (@Eid VarOrder.T 119))).
Lemma joint_update_ready_398 old :
 (exists ground bits, VM.find 119 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 120 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_398.
Proof.
 intros [g119 [b119 H119]].
 intros [g120 [b120 H120]].
 unfold joint_update_expr_398.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_399 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 119))).
Lemma joint_update_ready_399 old :
 (exists ground bits, VM.find 119 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_399.
Proof.
 intros [g119 [b119 H119]].
 unfold joint_update_expr_399.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_400 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 120)) (@Eref VarOrder.T (@Eid VarOrder.T 399))).
Lemma joint_update_ready_400 old :
 (exists ground bits, VM.find 120 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 399 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_400.
Proof.
 intros [g120 [b120 H120]].
 intros [g399 [b399 H399]].
 unfold joint_update_expr_400.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_401 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 118))).
Lemma joint_update_ready_401 old :
 (exists ground bits, VM.find 118 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_401.
Proof.
 intros [g118 [b118 H118]].
 unfold joint_update_expr_401.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_402 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 401)) (@Eref VarOrder.T (@Eid VarOrder.T 119)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_402 old :
 (exists ground bits, VM.find 119 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 401 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_402.
Proof.
 intros [g119 [b119 H119]].
 intros [g401 [b401 H401]].
 unfold joint_update_expr_402.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_403 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 118))).
Lemma joint_update_ready_403 old :
 (exists ground bits, VM.find 118 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_403.
Proof.
 intros [g118 [b118 H118]].
 unfold joint_update_expr_403.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_404 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 403)) (@Eref VarOrder.T (@Eid VarOrder.T 398)) (@Eref VarOrder.T (@Eid VarOrder.T 402))).
Lemma joint_update_ready_404 old :
 (exists ground bits, VM.find 398 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 402 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 403 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_404.
Proof.
 intros [g398 [b398 H398]].
 intros [g402 [b402 H402]].
 intros [g403 [b403 H403]].
 unfold joint_update_expr_404.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_405 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 118))).
Lemma joint_update_ready_405 old :
 (exists ground bits, VM.find 118 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_405.
Proof.
 intros [g118 [b118 H118]].
 unfold joint_update_expr_405.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_406 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 405)) (@Eref VarOrder.T (@Eid VarOrder.T 400)) (@Eref VarOrder.T (@Eid VarOrder.T 404))).
Lemma joint_update_ready_406 old :
 (exists ground bits, VM.find 400 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 404 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 405 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_406.
Proof.
 intros [g400 [b400 H400]].
 intros [g404 [b404 H404]].
 intros [g405 [b405 H405]].
 unfold joint_update_expr_406.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_407 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma joint_update_ready_407 old :
 (exists ground bits, VM.find 122 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_407.
Proof.
 intros [g122 [b122 H122]].
 unfold joint_update_expr_407.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_408 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 127)) (@Eref VarOrder.T (@Eid VarOrder.T 407))).
Lemma joint_update_ready_408 old :
 (exists ground bits, VM.find 127 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 407 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_408.
Proof.
 intros [g127 [b127 H127]].
 intros [g407 [b407 H407]].
 unfold joint_update_expr_408.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_409 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma joint_update_ready_409 old :
 (exists ground bits, VM.find 122 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_409.
Proof.
 intros [g122 [b122 H122]].
 unfold joint_update_expr_409.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_410 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 409))).
Lemma joint_update_ready_410 old :
 (exists ground bits, VM.find 409 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_410.
Proof.
 intros [g409 [b409 H409]].
 unfold joint_update_expr_410.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_411 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma joint_update_ready_411 old :
 (exists ground bits, VM.find 122 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_411.
Proof.
 intros [g122 [b122 H122]].
 unfold joint_update_expr_411.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_412 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma joint_update_ready_412 old :
 (exists ground bits, VM.find 122 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_412.
Proof.
 intros [g122 [b122 H122]].
 unfold joint_update_expr_412.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_413 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 126))).
Lemma joint_update_ready_413 old :
 (exists ground bits, VM.find 126 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_413.
Proof.
 intros [g126 [b126 H126]].
 unfold joint_update_expr_413.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_414 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 413)) (@Eref VarOrder.T (@Eid VarOrder.T 410)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_414 old :
 (exists ground bits, VM.find 410 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 413 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_414.
Proof.
 intros [g410 [b410 H410]].
 intros [g413 [b413 H413]].
 unfold joint_update_expr_414.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_415 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 126))).
Lemma joint_update_ready_415 old :
 (exists ground bits, VM.find 126 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_415.
Proof.
 intros [g126 [b126 H126]].
 unfold joint_update_expr_415.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_416 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 415)) (@Eref VarOrder.T (@Eid VarOrder.T 411)) (@Eref VarOrder.T (@Eid VarOrder.T 414))).
Lemma joint_update_ready_416 old :
 (exists ground bits, VM.find 411 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 414 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 415 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_416.
Proof.
 intros [g411 [b411 H411]].
 intros [g414 [b414 H414]].
 intros [g415 [b415 H415]].
 unfold joint_update_expr_416.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_417 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 126))).
Lemma joint_update_ready_417 old :
 (exists ground bits, VM.find 126 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_417.
Proof.
 intros [g126 [b126 H126]].
 unfold joint_update_expr_417.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_418 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 417)) (@Eref VarOrder.T (@Eid VarOrder.T 412)) (@Eref VarOrder.T (@Eid VarOrder.T 416))).
Lemma joint_update_ready_418 old :
 (exists ground bits, VM.find 412 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 416 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 417 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_418.
Proof.
 intros [g412 [b412 H412]].
 intros [g416 [b416 H416]].
 intros [g417 [b417 H417]].
 unfold joint_update_expr_418.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_419 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma joint_update_ready_419 old :
 (exists ground bits, VM.find 122 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_419.
Proof.
 intros [g122 [b122 H122]].
 unfold joint_update_expr_419.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_420 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 419))).
Lemma joint_update_ready_420 old :
 (exists ground bits, VM.find 419 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_420.
Proof.
 intros [g419 [b419 H419]].
 unfold joint_update_expr_420.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_421 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma joint_update_ready_421 old :
 (exists ground bits, VM.find 122 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_421.
Proof.
 intros [g122 [b122 H122]].
 unfold joint_update_expr_421.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_422 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 125))).
Lemma joint_update_ready_422 old :
 (exists ground bits, VM.find 125 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_422.
Proof.
 intros [g125 [b125 H125]].
 unfold joint_update_expr_422.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_423 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 422)) (@Eref VarOrder.T (@Eid VarOrder.T 420)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_423 old :
 (exists ground bits, VM.find 420 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 422 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_423.
Proof.
 intros [g420 [b420 H420]].
 intros [g422 [b422 H422]].
 unfold joint_update_expr_423.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_424 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 125))).
Lemma joint_update_ready_424 old :
 (exists ground bits, VM.find 125 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_424.
Proof.
 intros [g125 [b125 H125]].
 unfold joint_update_expr_424.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_425 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 424)) (@Eref VarOrder.T (@Eid VarOrder.T 421)) (@Eref VarOrder.T (@Eid VarOrder.T 423))).
Lemma joint_update_ready_425 old :
 (exists ground bits, VM.find 421 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 423 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 424 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_425.
Proof.
 intros [g421 [b421 H421]].
 intros [g423 [b423 H423]].
 intros [g424 [b424 H424]].
 unfold joint_update_expr_425.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_426 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 124)) (@Eref VarOrder.T (@Eid VarOrder.T 408))).
Lemma joint_update_ready_426 old :
 (exists ground bits, VM.find 124 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 408 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_426.
Proof.
 intros [g124 [b124 H124]].
 intros [g408 [b408 H408]].
 unfold joint_update_expr_426.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_427 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 426)) (@Eref VarOrder.T (@Eid VarOrder.T 418))).
Lemma joint_update_ready_427 old :
 (exists ground bits, VM.find 418 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 426 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_427.
Proof.
 intros [g418 [b418 H418]].
 intros [g426 [b426 H426]].
 unfold joint_update_expr_427.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_428 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 427)) (@Eref VarOrder.T (@Eid VarOrder.T 425))).
Lemma joint_update_ready_428 old :
 (exists ground bits, VM.find 425 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 427 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_428.
Proof.
 intros [g425 [b425 H425]].
 intros [g427 [b427 H427]].
 unfold joint_update_expr_428.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_429 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 118))).
Lemma joint_update_ready_429 old :
 (exists ground bits, VM.find 118 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_429.
Proof.
 intros [g118 [b118 H118]].
 unfold joint_update_expr_429.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_430 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 429))).
Lemma joint_update_ready_430 old :
 (exists ground bits, VM.find 429 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_430.
Proof.
 intros [g429 [b429 H429]].
 unfold joint_update_expr_430.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_431 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 386)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_431 old :
 (exists ground bits, VM.find 386 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_431.
Proof.
 intros [g386 [b386 H386]].
 unfold joint_update_expr_431.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_432 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 283)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_432 old :
 (exists ground bits, VM.find 283 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_432.
Proof.
 intros [g283 [b283 H283]].
 unfold joint_update_expr_432.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_433 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 431)) (@Eref VarOrder.T (@Eid VarOrder.T 432))).
Lemma joint_update_ready_433 old :
 (exists ground bits, VM.find 431 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 432 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_433.
Proof.
 intros [g431 [b431 H431]].
 intros [g432 [b432 H432]].
 unfold joint_update_expr_433.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_434 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 430)) (@Eref VarOrder.T (@Eid VarOrder.T 433))).
Lemma joint_update_ready_434 old :
 (exists ground bits, VM.find 430 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 433 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_434.
Proof.
 intros [g430 [b430 H430]].
 intros [g433 [b433 H433]].
 unfold joint_update_expr_434.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_435 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 428)) (@Eref VarOrder.T (@Eid VarOrder.T 434))).
Lemma joint_update_ready_435 old :
 (exists ground bits, VM.find 428 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 434 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_435.
Proof.
 intros [g428 [b428 H428]].
 intros [g434 [b434 H434]].
 unfold joint_update_expr_435.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_436 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 392))).
Lemma joint_update_ready_436 old :
 (exists ground bits, VM.find 392 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_436.
Proof.
 intros [g392 [b392 H392]].
 intros [g397 [b397 H397]].
 unfold joint_update_expr_436.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_437 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 435)) (@Eref VarOrder.T (@Eid VarOrder.T 436))).
Lemma joint_update_ready_437 old :
 (exists ground bits, VM.find 435 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 436 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_437.
Proof.
 intros [g435 [b435 H435]].
 intros [g436 [b436 H436]].
 unfold joint_update_expr_437.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_438 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 283)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_438 old :
 (exists ground bits, VM.find 283 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_438.
Proof.
 intros [g283 [b283 H283]].
 unfold joint_update_expr_438.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_439 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 284)) (@Eref VarOrder.T (@Eid VarOrder.T 438))).
Lemma joint_update_ready_439 old :
 (exists ground bits, VM.find 284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 438 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_439.
Proof.
 intros [g284 [b284 H284]].
 intros [g438 [b438 H438]].
 unfold joint_update_expr_439.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_440 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 437)) (@Eref VarOrder.T (@Eid VarOrder.T 439))).
Lemma joint_update_ready_440 old :
 (exists ground bits, VM.find 437 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 439 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_440.
Proof.
 intros [g437 [b437 H437]].
 intros [g439 [b439 H439]].
 unfold joint_update_expr_440.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_441 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 440)) (@Eref VarOrder.T (@Eid VarOrder.T 290))).
Lemma joint_update_ready_441 old :
 (exists ground bits, VM.find 290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 440 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_441.
Proof.
 intros [g290 [b290 H290]].
 intros [g440 [b440 H440]].
 unfold joint_update_expr_441.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_442 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 441)) (@Eref VarOrder.T (@Eid VarOrder.T 295))).
Lemma joint_update_ready_442 old :
 (exists ground bits, VM.find 295 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 441 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_442.
Proof.
 intros [g295 [b295 H295]].
 intros [g441 [b441 H441]].
 unfold joint_update_expr_442.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_443 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 6) (@Eref VarOrder.T (@Eid VarOrder.T 150))).
Lemma joint_update_ready_443 old :
 (exists ground bits, VM.find 150 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_443.
Proof.
 intros [g150 [b150 H150]].
 unfold joint_update_expr_443.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_444 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 443))).
Lemma joint_update_ready_444 old :
 (exists ground bits, VM.find 443 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_444.
Proof.
 intros [g443 [b443 H443]].
 unfold joint_update_expr_444.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_445 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 444))).
Lemma joint_update_ready_445 old :
 (exists ground bits, VM.find 444 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_445.
Proof.
 intros [g444 [b444 H444]].
 unfold joint_update_expr_445.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_446 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 142)) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma joint_update_ready_446 old :
 (exists ground bits, VM.find 142 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_446.
Proof.
 intros [g142 [b142 H142]].
 unfold joint_update_expr_446.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_447 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 446))).
Lemma joint_update_ready_447 old :
 (exists ground bits, VM.find 446 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_447.
Proof.
 intros [g446 [b446 H446]].
 unfold joint_update_expr_447.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_448 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uandr (@Eref VarOrder.T (@Eid VarOrder.T 142))).
Lemma joint_update_ready_448 old :
 (exists ground bits, VM.find 142 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_448.
Proof.
 intros [g142 [b142 H142]].
 unfold joint_update_expr_448.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_449 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 143)) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma joint_update_ready_449 old :
 (exists ground bits, VM.find 143 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_449.
Proof.
 intros [g143 [b143 H143]].
 unfold joint_update_expr_449.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_450 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 449))).
Lemma joint_update_ready_450 old :
 (exists ground bits, VM.find 449 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_450.
Proof.
 intros [g449 [b449 H449]].
 unfold joint_update_expr_450.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_451 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 448)) (@Eref VarOrder.T (@Eid VarOrder.T 450)) (@Eref VarOrder.T (@Eid VarOrder.T 143))).
Lemma joint_update_ready_451 old :
 (exists ground bits, VM.find 143 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 448 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 450 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_451.
Proof.
 intros [g143 [b143 H143]].
 intros [g448 [b448 H448]].
 intros [g450 [b450 H450]].
 unfold joint_update_expr_451.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_452 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 144)) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma joint_update_ready_452 old :
 (exists ground bits, VM.find 144 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_452.
Proof.
 intros [g144 [b144 H144]].
 unfold joint_update_expr_452.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_453 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 452))).
Lemma joint_update_ready_453 old :
 (exists ground bits, VM.find 452 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_453.
Proof.
 intros [g452 [b452 H452]].
 unfold joint_update_expr_453.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_454 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uandr (@Eref VarOrder.T (@Eid VarOrder.T 144))).
Lemma joint_update_ready_454 old :
 (exists ground bits, VM.find 144 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_454.
Proof.
 intros [g144 [b144 H144]].
 unfold joint_update_expr_454.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_455 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 145)) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma joint_update_ready_455 old :
 (exists ground bits, VM.find 145 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_455.
Proof.
 intros [g145 [b145 H145]].
 unfold joint_update_expr_455.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_456 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 455))).
Lemma joint_update_ready_456 old :
 (exists ground bits, VM.find 455 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_456.
Proof.
 intros [g455 [b455 H455]].
 unfold joint_update_expr_456.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_457 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 454)) (@Eref VarOrder.T (@Eid VarOrder.T 456)) (@Eref VarOrder.T (@Eid VarOrder.T 145))).
Lemma joint_update_ready_457 old :
 (exists ground bits, VM.find 145 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 454 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 456 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_457.
Proof.
 intros [g145 [b145 H145]].
 intros [g454 [b454 H454]].
 intros [g456 [b456 H456]].
 unfold joint_update_expr_457.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_458 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Bneq) (@Eref VarOrder.T (@Eid VarOrder.T 123)) (@Econst VarOrder.T (Fuint 32) [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_458 old :
 (exists ground bits, VM.find 123 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_458.
Proof.
 intros [g123 [b123 H123]].
 unfold joint_update_expr_458.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_459 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_459 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_459.
Proof.
 intros [g128 [b128 H128]].
 unfold joint_update_expr_459.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_460 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 459)) (@Eref VarOrder.T (@Eid VarOrder.T 290))).
Lemma joint_update_ready_460 old :
 (exists ground bits, VM.find 290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 459 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_460.
Proof.
 intros [g290 [b290 H290]].
 intros [g459 [b459 H459]].
 unfold joint_update_expr_460.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_461 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 460)) (@Eref VarOrder.T (@Eid VarOrder.T 295))).
Lemma joint_update_ready_461 old :
 (exists ground bits, VM.find 295 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 460 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_461.
Proof.
 intros [g295 [b295 H295]].
 intros [g460 [b460 H460]].
 unfold joint_update_expr_461.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_462 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 458)) (@Eref VarOrder.T (@Eid VarOrder.T 461))).
Lemma joint_update_ready_462 old :
 (exists ground bits, VM.find 458 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 461 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_462.
Proof.
 intros [g458 [b458 H458]].
 intros [g461 [b461 H461]].
 unfold joint_update_expr_462.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_463 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 117)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_463 old :
 (exists ground bits, VM.find 117 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_463.
Proof.
 intros [g117 [b117 H117]].
 unfold joint_update_expr_463.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_464 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 462)) (@Eref VarOrder.T (@Eid VarOrder.T 463))).
Lemma joint_update_ready_464 old :
 (exists ground bits, VM.find 462 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 463 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_464.
Proof.
 intros [g462 [b462 H462]].
 intros [g463 [b463 H463]].
 unfold joint_update_expr_464.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_465 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 146)) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma joint_update_ready_465 old :
 (exists ground bits, VM.find 146 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_465.
Proof.
 intros [g146 [b146 H146]].
 unfold joint_update_expr_465.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_466 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 465))).
Lemma joint_update_ready_466 old :
 (exists ground bits, VM.find 465 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_466.
Proof.
 intros [g465 [b465 H465]].
 unfold joint_update_expr_466.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_467 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 464)) (@Eref VarOrder.T (@Eid VarOrder.T 466)) (@Eref VarOrder.T (@Eid VarOrder.T 146))).
Lemma joint_update_ready_467 old :
 (exists ground bits, VM.find 146 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 464 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 466 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_467.
Proof.
 intros [g146 [b146 H146]].
 intros [g464 [b464 H464]].
 intros [g466 [b466 H466]].
 unfold joint_update_expr_467.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_468 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uandr (@Eref VarOrder.T (@Eid VarOrder.T 146))).
Lemma joint_update_ready_468 old :
 (exists ground bits, VM.find 146 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_468.
Proof.
 intros [g146 [b146 H146]].
 unfold joint_update_expr_468.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_469 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 464)) (@Eref VarOrder.T (@Eid VarOrder.T 468))).
Lemma joint_update_ready_469 old :
 (exists ground bits, VM.find 464 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 468 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_469.
Proof.
 intros [g464 [b464 H464]].
 intros [g468 [b468 H468]].
 unfold joint_update_expr_469.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_470 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 147)) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma joint_update_ready_470 old :
 (exists ground bits, VM.find 147 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_470.
Proof.
 intros [g147 [b147 H147]].
 unfold joint_update_expr_470.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_471 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 470))).
Lemma joint_update_ready_471 old :
 (exists ground bits, VM.find 470 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_471.
Proof.
 intros [g470 [b470 H470]].
 unfold joint_update_expr_471.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_472 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 469)) (@Eref VarOrder.T (@Eid VarOrder.T 471)) (@Eref VarOrder.T (@Eid VarOrder.T 147))).
Lemma joint_update_ready_472 old :
 (exists ground bits, VM.find 147 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 469 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 471 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_472.
Proof.
 intros [g147 [b147 H147]].
 intros [g469 [b469 H469]].
 intros [g471 [b471 H471]].
 unfold joint_update_expr_472.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_473 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 150))).
Lemma joint_update_ready_473 old :
 (exists ground bits, VM.find 150 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_473.
Proof.
 intros [g150 [b150 H150]].
 unfold joint_update_expr_473.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_474 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 473))).
Lemma joint_update_ready_474 old :
 (exists ground bits, VM.find 473 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_474.
Proof.
 intros [g473 [b473 H473]].
 unfold joint_update_expr_474.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_475 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 295)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Econst VarOrder.T (Fuint 2) [::false; true])).
Lemma joint_update_ready_475 old :
 (exists ground bits, VM.find 295 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_475.
Proof.
 intros [g295 [b295 H295]].
 unfold joint_update_expr_475.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_476 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 290)) (@Eref VarOrder.T (@Eid VarOrder.T 474)) (@Eref VarOrder.T (@Eid VarOrder.T 475))).
Lemma joint_update_ready_476 old :
 (exists ground bits, VM.find 290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 474 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 475 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_476.
Proof.
 intros [g290 [b290 H290]].
 intros [g474 [b474 H474]].
 intros [g475 [b475 H475]].
 unfold joint_update_expr_476.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_477 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 425)) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 476))).
Lemma joint_update_ready_477 old :
 (exists ground bits, VM.find 425 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 476 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_477.
Proof.
 intros [g425 [b425 H425]].
 intros [g476 [b476 H476]].
 unfold joint_update_expr_477.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_478 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 418)) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 477))).
Lemma joint_update_ready_478 old :
 (exists ground bits, VM.find 418 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 477 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_478.
Proof.
 intros [g418 [b418 H418]].
 intros [g477 [b477 H477]].
 unfold joint_update_expr_478.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_479 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 408)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 478))).
Lemma joint_update_ready_479 old :
 (exists ground bits, VM.find 408 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 478 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_479.
Proof.
 intros [g408 [b408 H408]].
 intros [g478 [b478 H478]].
 unfold joint_update_expr_479.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_480 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 117)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_480 old :
 (exists ground bits, VM.find 117 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_480.
Proof.
 intros [g117 [b117 H117]].
 unfold joint_update_expr_480.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_483 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 2) (@Eref VarOrder.T (@Eid VarOrder.T 121))).
Lemma joint_update_ready_483 old :
 (exists ground bits, VM.find 121 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_483.
Proof.
 intros [g121 [b121 H121]].
 unfold joint_update_expr_483.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_484 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 2) (@Eref VarOrder.T (@Eid VarOrder.T 483))).
Lemma joint_update_ready_484 old :
 (exists ground bits, VM.find 483 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_484.
Proof.
 intros [g483 [b483 H483]].
 unfold joint_update_expr_484.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_485 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 408)) (@Eref VarOrder.T (@Eid VarOrder.T 418))).
Lemma joint_update_ready_485 old :
 (exists ground bits, VM.find 408 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 418 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_485.
Proof.
 intros [g408 [b408 H408]].
 intros [g418 [b418 H418]].
 unfold joint_update_expr_485.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_486 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 485)) (@Eref VarOrder.T (@Eid VarOrder.T 425))).
Lemma joint_update_ready_486 old :
 (exists ground bits, VM.find 425 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 485 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_486.
Proof.
 intros [g425 [b425 H425]].
 intros [g485 [b485 H485]].
 unfold joint_update_expr_486.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_487 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 486)) (@Eref VarOrder.T (@Eid VarOrder.T 122)) (@Eref VarOrder.T (@Eid VarOrder.T 191))).
Lemma joint_update_ready_487 old :
 (exists ground bits, VM.find 122 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 486 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_487.
Proof.
 intros [g122 [b122 H122]].
 intros [g191 [b191 H191]].
 intros [g486 [b486 H486]].
 unfold joint_update_expr_487.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_488 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; true; true; false; false])).
Lemma joint_update_ready_488 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_488.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_488.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_489 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 5 4) (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Lemma joint_update_ready_489 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_489.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_489.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_490 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Lemma joint_update_ready_490 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_490.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_490.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_491 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 2 1) (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Lemma joint_update_ready_491 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_491.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_491.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_492 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Lemma joint_update_ready_492 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_492.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_492.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_493 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; false; true; false; false; false; true; false; true; true; false; false])).
Lemma joint_update_ready_493 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_493.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_493.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_494 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 7) (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Lemma joint_update_ready_494 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_494.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_494.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_495 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Lemma joint_update_ready_495 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_495.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_495.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_496 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; false; true; false; false; false; false; false; true; true; false; false])).
Lemma joint_update_ready_496 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_496.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_496.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_497 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 7) (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Lemma joint_update_ready_497 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_497.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_497.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_498 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 406))).
Lemma joint_update_ready_498 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_498.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_498.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_499 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; true; true; false])).
Lemma joint_update_ready_499 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_499.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_499.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_500 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; true; false; true; true; true; false])).
Lemma joint_update_ready_500 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_500.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_500.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_501 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; true; false; false; true; true; false; false])).
Lemma joint_update_ready_501 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_501.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_501.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_502 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; true; false; true; true; false; false])).
Lemma joint_update_ready_502 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_502.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_502.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_503 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; true; false; true; true; false; false])).
Lemma joint_update_ready_503 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_503.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_503.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_504 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Econst VarOrder.T (Fuint 2) [::false; true])).
Lemma joint_update_ready_504 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_504.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_504.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_505 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 504)) (@Econst VarOrder.T (Fuint 2) [::false; true])).
Lemma joint_update_ready_505 old :
 (exists ground bits, VM.find 504 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_505.
Proof.
 intros [g504 [b504 H504]].
 unfold joint_update_expr_505.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_506 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; true; false; true; true; false; false])).
Lemma joint_update_ready_506 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_506.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_506.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_507 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true])).
Lemma joint_update_ready_507 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_507.
Proof.
 intros [g406 [b406 H406]].
 unfold joint_update_expr_507.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_508 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; false; false; false; false; true; false; true; true; false; false])).
Lemma joint_update_ready_508 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_508.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_508.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_509 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; true; true; true; true; false])).
Lemma joint_update_ready_509 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_509.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_509.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_510 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; true; true; true; true; false])).
Lemma joint_update_ready_510 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_510.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_510.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_511 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; true; false; false; true])).
Lemma joint_update_ready_511 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_511.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_511.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_512 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; false; false; true])).
Lemma joint_update_ready_512 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_512.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_512.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_513 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; false; true; false; false; true])).
Lemma joint_update_ready_513 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_513.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_513.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_514 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; true; true; false; false; true])).
Lemma joint_update_ready_514 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_514.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_514.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_515 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; true; true; false; false; true])).
Lemma joint_update_ready_515 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_515.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_515.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_516 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; true; true; false; false; true])).
Lemma joint_update_ready_516 old :
 (exists ground bits, VM.find 140 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_516.
Proof.
 intros [g140 [b140 H140]].
 unfold joint_update_expr_516.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_517 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 516)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 472))).
Lemma joint_update_ready_517 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 516 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_517.
Proof.
 intros [g406 [b406 H406]].
 intros [g472 [b472 H472]].
 intros [g516 [b516 H516]].
 unfold joint_update_expr_517.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_518 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 515)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 451))).
Lemma joint_update_ready_518 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 515 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_518.
Proof.
 intros [g406 [b406 H406]].
 intros [g451 [b451 H451]].
 intros [g515 [b515 H515]].
 unfold joint_update_expr_518.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_519 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 515)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 517))).
Lemma joint_update_ready_519 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 515 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 517 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_519.
Proof.
 intros [g472 [b472 H472]].
 intros [g515 [b515 H515]].
 intros [g517 [b517 H517]].
 unfold joint_update_expr_519.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_520 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 514)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 457))).
Lemma joint_update_ready_520 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 514 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_520.
Proof.
 intros [g406 [b406 H406]].
 intros [g457 [b457 H457]].
 intros [g514 [b514 H514]].
 unfold joint_update_expr_520.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_521 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 514)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 518))).
Lemma joint_update_ready_521 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 514 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 518 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_521.
Proof.
 intros [g451 [b451 H451]].
 intros [g514 [b514 H514]].
 intros [g518 [b518 H518]].
 unfold joint_update_expr_521.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_522 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 514)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 519))).
Lemma joint_update_ready_522 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 514 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 519 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_522.
Proof.
 intros [g472 [b472 H472]].
 intros [g514 [b514 H514]].
 intros [g519 [b519 H519]].
 unfold joint_update_expr_522.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_523 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 513)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 467))).
Lemma joint_update_ready_523 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 513 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_523.
Proof.
 intros [g406 [b406 H406]].
 intros [g467 [b467 H467]].
 intros [g513 [b513 H513]].
 unfold joint_update_expr_523.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_524 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 513)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 520))).
Lemma joint_update_ready_524 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 513 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 520 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_524.
Proof.
 intros [g457 [b457 H457]].
 intros [g513 [b513 H513]].
 intros [g520 [b520 H520]].
 unfold joint_update_expr_524.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_525 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 513)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 521))).
Lemma joint_update_ready_525 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 513 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 521 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_525.
Proof.
 intros [g451 [b451 H451]].
 intros [g513 [b513 H513]].
 intros [g521 [b521 H521]].
 unfold joint_update_expr_525.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_526 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 513)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 522))).
Lemma joint_update_ready_526 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 513 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 522 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_526.
Proof.
 intros [g472 [b472 H472]].
 intros [g513 [b513 H513]].
 intros [g522 [b522 H522]].
 unfold joint_update_expr_526.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_527 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 512)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 447))).
Lemma joint_update_ready_527 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 512 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_527.
Proof.
 intros [g406 [b406 H406]].
 intros [g447 [b447 H447]].
 intros [g512 [b512 H512]].
 unfold joint_update_expr_527.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_528 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 512)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 523))).
Lemma joint_update_ready_528 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 512 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 523 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_528.
Proof.
 intros [g467 [b467 H467]].
 intros [g512 [b512 H512]].
 intros [g523 [b523 H523]].
 unfold joint_update_expr_528.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_529 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 512)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 524))).
Lemma joint_update_ready_529 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 512 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 524 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_529.
Proof.
 intros [g457 [b457 H457]].
 intros [g512 [b512 H512]].
 intros [g524 [b524 H524]].
 unfold joint_update_expr_529.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_530 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 512)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 525))).
Lemma joint_update_ready_530 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 512 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 525 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_530.
Proof.
 intros [g451 [b451 H451]].
 intros [g512 [b512 H512]].
 intros [g525 [b525 H525]].
 unfold joint_update_expr_530.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_531 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 512)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 526))).
Lemma joint_update_ready_531 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 512 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 526 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_531.
Proof.
 intros [g472 [b472 H472]].
 intros [g512 [b512 H512]].
 intros [g526 [b526 H526]].
 unfold joint_update_expr_531.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_532 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 511)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 453))).
Lemma joint_update_ready_532 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 511 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_532.
Proof.
 intros [g406 [b406 H406]].
 intros [g453 [b453 H453]].
 intros [g511 [b511 H511]].
 unfold joint_update_expr_532.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_533 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 511)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 527))).
Lemma joint_update_ready_533 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 511 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 527 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_533.
Proof.
 intros [g447 [b447 H447]].
 intros [g511 [b511 H511]].
 intros [g527 [b527 H527]].
 unfold joint_update_expr_533.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_534 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 511)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 528))).
Lemma joint_update_ready_534 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 511 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 528 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_534.
Proof.
 intros [g467 [b467 H467]].
 intros [g511 [b511 H511]].
 intros [g528 [b528 H528]].
 unfold joint_update_expr_534.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_535 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 511)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 529))).
Lemma joint_update_ready_535 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 511 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 529 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_535.
Proof.
 intros [g457 [b457 H457]].
 intros [g511 [b511 H511]].
 intros [g529 [b529 H529]].
 unfold joint_update_expr_535.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_536 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 511)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 530))).
Lemma joint_update_ready_536 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 511 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 530 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_536.
Proof.
 intros [g451 [b451 H451]].
 intros [g511 [b511 H511]].
 intros [g530 [b530 H530]].
 unfold joint_update_expr_536.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_537 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 511)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 531))).
Lemma joint_update_ready_537 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 511 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 531 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_537.
Proof.
 intros [g472 [b472 H472]].
 intros [g511 [b511 H511]].
 intros [g531 [b531 H531]].
 unfold joint_update_expr_537.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_538 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 510)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 194))).
Lemma joint_update_ready_538 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 510 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_538.
Proof.
 intros [g194 [b194 H194]].
 intros [g406 [b406 H406]].
 intros [g510 [b510 H510]].
 unfold joint_update_expr_538.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_539 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 510)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 532))).
Lemma joint_update_ready_539 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 510 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 532 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_539.
Proof.
 intros [g453 [b453 H453]].
 intros [g510 [b510 H510]].
 intros [g532 [b532 H532]].
 unfold joint_update_expr_539.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_540 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 510)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 533))).
Lemma joint_update_ready_540 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 510 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 533 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_540.
Proof.
 intros [g447 [b447 H447]].
 intros [g510 [b510 H510]].
 intros [g533 [b533 H533]].
 unfold joint_update_expr_540.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_541 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 510)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 534))).
Lemma joint_update_ready_541 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 510 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 534 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_541.
Proof.
 intros [g467 [b467 H467]].
 intros [g510 [b510 H510]].
 intros [g534 [b534 H534]].
 unfold joint_update_expr_541.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_542 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 510)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 535))).
Lemma joint_update_ready_542 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 510 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 535 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_542.
Proof.
 intros [g457 [b457 H457]].
 intros [g510 [b510 H510]].
 intros [g535 [b535 H535]].
 unfold joint_update_expr_542.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_543 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 510)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 536))).
Lemma joint_update_ready_543 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 510 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 536 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_543.
Proof.
 intros [g451 [b451 H451]].
 intros [g510 [b510 H510]].
 intros [g536 [b536 H536]].
 unfold joint_update_expr_543.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_544 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 510)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 537))).
Lemma joint_update_ready_544 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 510 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 537 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_544.
Proof.
 intros [g472 [b472 H472]].
 intros [g510 [b510 H510]].
 intros [g537 [b537 H537]].
 unfold joint_update_expr_544.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_545 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 509)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 192))).
Lemma joint_update_ready_545 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 509 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_545.
Proof.
 intros [g192 [b192 H192]].
 intros [g406 [b406 H406]].
 intros [g509 [b509 H509]].
 unfold joint_update_expr_545.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_546 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 509)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 538))).
Lemma joint_update_ready_546 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 509 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 538 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_546.
Proof.
 intros [g194 [b194 H194]].
 intros [g509 [b509 H509]].
 intros [g538 [b538 H538]].
 unfold joint_update_expr_546.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_547 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 509)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 539))).
Lemma joint_update_ready_547 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 509 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 539 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_547.
Proof.
 intros [g453 [b453 H453]].
 intros [g509 [b509 H509]].
 intros [g539 [b539 H539]].
 unfold joint_update_expr_547.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_548 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 509)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 540))).
Lemma joint_update_ready_548 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 509 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 540 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_548.
Proof.
 intros [g447 [b447 H447]].
 intros [g509 [b509 H509]].
 intros [g540 [b540 H540]].
 unfold joint_update_expr_548.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_549 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 509)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 541))).
Lemma joint_update_ready_549 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 509 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 541 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_549.
Proof.
 intros [g467 [b467 H467]].
 intros [g509 [b509 H509]].
 intros [g541 [b541 H541]].
 unfold joint_update_expr_549.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_550 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 509)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 542))).
Lemma joint_update_ready_550 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 509 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 542 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_550.
Proof.
 intros [g457 [b457 H457]].
 intros [g509 [b509 H509]].
 intros [g542 [b542 H542]].
 unfold joint_update_expr_550.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_551 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 509)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 543))).
Lemma joint_update_ready_551 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 509 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 543 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_551.
Proof.
 intros [g451 [b451 H451]].
 intros [g509 [b509 H509]].
 intros [g543 [b543 H543]].
 unfold joint_update_expr_551.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_552 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 509)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 544))).
Lemma joint_update_ready_552 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 509 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 544 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_552.
Proof.
 intros [g472 [b472 H472]].
 intros [g509 [b509 H509]].
 intros [g544 [b544 H544]].
 unfold joint_update_expr_552.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_553 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 508)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 191))).
Lemma joint_update_ready_553 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 508 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_553.
Proof.
 intros [g191 [b191 H191]].
 intros [g406 [b406 H406]].
 intros [g508 [b508 H508]].
 unfold joint_update_expr_553.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_554 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 508)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 545))).
Lemma joint_update_ready_554 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 508 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 545 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_554.
Proof.
 intros [g192 [b192 H192]].
 intros [g508 [b508 H508]].
 intros [g545 [b545 H545]].
 unfold joint_update_expr_554.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_555 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 508)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 546))).
Lemma joint_update_ready_555 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 508 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 546 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_555.
Proof.
 intros [g194 [b194 H194]].
 intros [g508 [b508 H508]].
 intros [g546 [b546 H546]].
 unfold joint_update_expr_555.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_556 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 508)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 547))).
Lemma joint_update_ready_556 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 508 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 547 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_556.
Proof.
 intros [g453 [b453 H453]].
 intros [g508 [b508 H508]].
 intros [g547 [b547 H547]].
 unfold joint_update_expr_556.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_557 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 508)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 548))).
Lemma joint_update_ready_557 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 508 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 548 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_557.
Proof.
 intros [g447 [b447 H447]].
 intros [g508 [b508 H508]].
 intros [g548 [b548 H548]].
 unfold joint_update_expr_557.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_558 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 508)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 549))).
Lemma joint_update_ready_558 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 508 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 549 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_558.
Proof.
 intros [g467 [b467 H467]].
 intros [g508 [b508 H508]].
 intros [g549 [b549 H549]].
 unfold joint_update_expr_558.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_559 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 508)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 550))).
Lemma joint_update_ready_559 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 508 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 550 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_559.
Proof.
 intros [g457 [b457 H457]].
 intros [g508 [b508 H508]].
 intros [g550 [b550 H550]].
 unfold joint_update_expr_559.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_560 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 508)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 551))).
Lemma joint_update_ready_560 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 508 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 551 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_560.
Proof.
 intros [g451 [b451 H451]].
 intros [g508 [b508 H508]].
 intros [g551 [b551 H551]].
 unfold joint_update_expr_560.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_561 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 508)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 552))).
Lemma joint_update_ready_561 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 508 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 552 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_561.
Proof.
 intros [g472 [b472 H472]].
 intros [g508 [b508 H508]].
 intros [g552 [b552 H552]].
 unfold joint_update_expr_561.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_562 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 507)) (@Eref VarOrder.T (@Eid VarOrder.T 190))).
Lemma joint_update_ready_562 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 507 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_562.
Proof.
 intros [g190 [b190 H190]].
 intros [g506 [b506 H506]].
 intros [g507 [b507 H507]].
 unfold joint_update_expr_562.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_563 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 553))).
Lemma joint_update_ready_563 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 553 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_563.
Proof.
 intros [g191 [b191 H191]].
 intros [g506 [b506 H506]].
 intros [g553 [b553 H553]].
 unfold joint_update_expr_563.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_564 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 554))).
Lemma joint_update_ready_564 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 554 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_564.
Proof.
 intros [g192 [b192 H192]].
 intros [g506 [b506 H506]].
 intros [g554 [b554 H554]].
 unfold joint_update_expr_564.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_565 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 555))).
Lemma joint_update_ready_565 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 555 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_565.
Proof.
 intros [g194 [b194 H194]].
 intros [g506 [b506 H506]].
 intros [g555 [b555 H555]].
 unfold joint_update_expr_565.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_566 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 556))).
Lemma joint_update_ready_566 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 556 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_566.
Proof.
 intros [g453 [b453 H453]].
 intros [g506 [b506 H506]].
 intros [g556 [b556 H556]].
 unfold joint_update_expr_566.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_567 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 557))).
Lemma joint_update_ready_567 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 557 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_567.
Proof.
 intros [g447 [b447 H447]].
 intros [g506 [b506 H506]].
 intros [g557 [b557 H557]].
 unfold joint_update_expr_567.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_568 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 558))).
Lemma joint_update_ready_568 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 558 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_568.
Proof.
 intros [g467 [b467 H467]].
 intros [g506 [b506 H506]].
 intros [g558 [b558 H558]].
 unfold joint_update_expr_568.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_569 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 559))).
Lemma joint_update_ready_569 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 559 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_569.
Proof.
 intros [g457 [b457 H457]].
 intros [g506 [b506 H506]].
 intros [g559 [b559 H559]].
 unfold joint_update_expr_569.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_570 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 560))).
Lemma joint_update_ready_570 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 560 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_570.
Proof.
 intros [g451 [b451 H451]].
 intros [g506 [b506 H506]].
 intros [g560 [b560 H560]].
 unfold joint_update_expr_570.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_571 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 506)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 561))).
Lemma joint_update_ready_571 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 506 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 561 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_571.
Proof.
 intros [g472 [b472 H472]].
 intros [g506 [b506 H506]].
 intros [g561 [b561 H561]].
 unfold joint_update_expr_571.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_572 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 505)) (@Eref VarOrder.T (@Eid VarOrder.T 189))).
Lemma joint_update_ready_572 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 505 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_572.
Proof.
 intros [g189 [b189 H189]].
 intros [g503 [b503 H503]].
 intros [g505 [b505 H505]].
 unfold joint_update_expr_572.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_573 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 562))).
Lemma joint_update_ready_573 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 562 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_573.
Proof.
 intros [g190 [b190 H190]].
 intros [g503 [b503 H503]].
 intros [g562 [b562 H562]].
 unfold joint_update_expr_573.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_574 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 563))).
Lemma joint_update_ready_574 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 563 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_574.
Proof.
 intros [g191 [b191 H191]].
 intros [g503 [b503 H503]].
 intros [g563 [b563 H563]].
 unfold joint_update_expr_574.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_575 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 564))).
Lemma joint_update_ready_575 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 564 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_575.
Proof.
 intros [g192 [b192 H192]].
 intros [g503 [b503 H503]].
 intros [g564 [b564 H564]].
 unfold joint_update_expr_575.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_576 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 565))).
Lemma joint_update_ready_576 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 565 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_576.
Proof.
 intros [g194 [b194 H194]].
 intros [g503 [b503 H503]].
 intros [g565 [b565 H565]].
 unfold joint_update_expr_576.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_577 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 566))).
Lemma joint_update_ready_577 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 566 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_577.
Proof.
 intros [g453 [b453 H453]].
 intros [g503 [b503 H503]].
 intros [g566 [b566 H566]].
 unfold joint_update_expr_577.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_578 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 567))).
Lemma joint_update_ready_578 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 567 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_578.
Proof.
 intros [g447 [b447 H447]].
 intros [g503 [b503 H503]].
 intros [g567 [b567 H567]].
 unfold joint_update_expr_578.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_579 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 568))).
Lemma joint_update_ready_579 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 568 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_579.
Proof.
 intros [g467 [b467 H467]].
 intros [g503 [b503 H503]].
 intros [g568 [b568 H568]].
 unfold joint_update_expr_579.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_580 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 569))).
Lemma joint_update_ready_580 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 569 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_580.
Proof.
 intros [g457 [b457 H457]].
 intros [g503 [b503 H503]].
 intros [g569 [b569 H569]].
 unfold joint_update_expr_580.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_581 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 570))).
Lemma joint_update_ready_581 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 570 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_581.
Proof.
 intros [g451 [b451 H451]].
 intros [g503 [b503 H503]].
 intros [g570 [b570 H570]].
 unfold joint_update_expr_581.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_582 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 503)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 571))).
Lemma joint_update_ready_582 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 503 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 571 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_582.
Proof.
 intros [g472 [b472 H472]].
 intros [g503 [b503 H503]].
 intros [g571 [b571 H571]].
 unfold joint_update_expr_582.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_583 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 188))).
Lemma joint_update_ready_583 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_583.
Proof.
 intros [g188 [b188 H188]].
 intros [g406 [b406 H406]].
 intros [g502 [b502 H502]].
 unfold joint_update_expr_583.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_584 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 572))).
Lemma joint_update_ready_584 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 572 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_584.
Proof.
 intros [g189 [b189 H189]].
 intros [g502 [b502 H502]].
 intros [g572 [b572 H572]].
 unfold joint_update_expr_584.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_585 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 573))).
Lemma joint_update_ready_585 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 573 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_585.
Proof.
 intros [g190 [b190 H190]].
 intros [g502 [b502 H502]].
 intros [g573 [b573 H573]].
 unfold joint_update_expr_585.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_586 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 574))).
Lemma joint_update_ready_586 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 574 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_586.
Proof.
 intros [g191 [b191 H191]].
 intros [g502 [b502 H502]].
 intros [g574 [b574 H574]].
 unfold joint_update_expr_586.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_587 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 575))).
Lemma joint_update_ready_587 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 575 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_587.
Proof.
 intros [g192 [b192 H192]].
 intros [g502 [b502 H502]].
 intros [g575 [b575 H575]].
 unfold joint_update_expr_587.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_588 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 576))).
Lemma joint_update_ready_588 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 576 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_588.
Proof.
 intros [g194 [b194 H194]].
 intros [g502 [b502 H502]].
 intros [g576 [b576 H576]].
 unfold joint_update_expr_588.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_589 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 577))).
Lemma joint_update_ready_589 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 577 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_589.
Proof.
 intros [g453 [b453 H453]].
 intros [g502 [b502 H502]].
 intros [g577 [b577 H577]].
 unfold joint_update_expr_589.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_590 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 578))).
Lemma joint_update_ready_590 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 578 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_590.
Proof.
 intros [g447 [b447 H447]].
 intros [g502 [b502 H502]].
 intros [g578 [b578 H578]].
 unfold joint_update_expr_590.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_591 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 579))).
Lemma joint_update_ready_591 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 579 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_591.
Proof.
 intros [g467 [b467 H467]].
 intros [g502 [b502 H502]].
 intros [g579 [b579 H579]].
 unfold joint_update_expr_591.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_592 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 580))).
Lemma joint_update_ready_592 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 580 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_592.
Proof.
 intros [g457 [b457 H457]].
 intros [g502 [b502 H502]].
 intros [g580 [b580 H580]].
 unfold joint_update_expr_592.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_593 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 581))).
Lemma joint_update_ready_593 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 581 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_593.
Proof.
 intros [g451 [b451 H451]].
 intros [g502 [b502 H502]].
 intros [g581 [b581 H581]].
 unfold joint_update_expr_593.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_594 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 502)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 582))).
Lemma joint_update_ready_594 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 502 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 582 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_594.
Proof.
 intros [g472 [b472 H472]].
 intros [g502 [b502 H502]].
 intros [g582 [b582 H582]].
 unfold joint_update_expr_594.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_595 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 187))).
Lemma joint_update_ready_595 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_595.
Proof.
 intros [g187 [b187 H187]].
 intros [g406 [b406 H406]].
 intros [g501 [b501 H501]].
 unfold joint_update_expr_595.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_596 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 583))).
Lemma joint_update_ready_596 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 583 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_596.
Proof.
 intros [g188 [b188 H188]].
 intros [g501 [b501 H501]].
 intros [g583 [b583 H583]].
 unfold joint_update_expr_596.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_597 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 584))).
Lemma joint_update_ready_597 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 584 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_597.
Proof.
 intros [g189 [b189 H189]].
 intros [g501 [b501 H501]].
 intros [g584 [b584 H584]].
 unfold joint_update_expr_597.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_598 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 585))).
Lemma joint_update_ready_598 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 585 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_598.
Proof.
 intros [g190 [b190 H190]].
 intros [g501 [b501 H501]].
 intros [g585 [b585 H585]].
 unfold joint_update_expr_598.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_599 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 586))).
Lemma joint_update_ready_599 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 586 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_599.
Proof.
 intros [g191 [b191 H191]].
 intros [g501 [b501 H501]].
 intros [g586 [b586 H586]].
 unfold joint_update_expr_599.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_600 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 587))).
Lemma joint_update_ready_600 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 587 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_600.
Proof.
 intros [g192 [b192 H192]].
 intros [g501 [b501 H501]].
 intros [g587 [b587 H587]].
 unfold joint_update_expr_600.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_601 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 588))).
Lemma joint_update_ready_601 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 588 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_601.
Proof.
 intros [g194 [b194 H194]].
 intros [g501 [b501 H501]].
 intros [g588 [b588 H588]].
 unfold joint_update_expr_601.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_602 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 589))).
Lemma joint_update_ready_602 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 589 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_602.
Proof.
 intros [g453 [b453 H453]].
 intros [g501 [b501 H501]].
 intros [g589 [b589 H589]].
 unfold joint_update_expr_602.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_603 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 590))).
Lemma joint_update_ready_603 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 590 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_603.
Proof.
 intros [g447 [b447 H447]].
 intros [g501 [b501 H501]].
 intros [g590 [b590 H590]].
 unfold joint_update_expr_603.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_604 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 591))).
Lemma joint_update_ready_604 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 591 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_604.
Proof.
 intros [g467 [b467 H467]].
 intros [g501 [b501 H501]].
 intros [g591 [b591 H591]].
 unfold joint_update_expr_604.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_605 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 592))).
Lemma joint_update_ready_605 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 592 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_605.
Proof.
 intros [g457 [b457 H457]].
 intros [g501 [b501 H501]].
 intros [g592 [b592 H592]].
 unfold joint_update_expr_605.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_606 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 593))).
Lemma joint_update_ready_606 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 593 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_606.
Proof.
 intros [g451 [b451 H451]].
 intros [g501 [b501 H501]].
 intros [g593 [b593 H593]].
 unfold joint_update_expr_606.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_607 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 501)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 594))).
Lemma joint_update_ready_607 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 501 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 594 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_607.
Proof.
 intros [g472 [b472 H472]].
 intros [g501 [b501 H501]].
 intros [g594 [b594 H594]].
 unfold joint_update_expr_607.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_608 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 606))).
Lemma joint_update_ready_608 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 606 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_608.
Proof.
 intros [g406 [b406 H406]].
 intros [g500 [b500 H500]].
 intros [g606 [b606 H606]].
 unfold joint_update_expr_608.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_609 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 187)) (@Eref VarOrder.T (@Eid VarOrder.T 595))).
Lemma joint_update_ready_609 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 595 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_609.
Proof.
 intros [g187 [b187 H187]].
 intros [g500 [b500 H500]].
 intros [g595 [b595 H595]].
 unfold joint_update_expr_609.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_610 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 596))).
Lemma joint_update_ready_610 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 596 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_610.
Proof.
 intros [g188 [b188 H188]].
 intros [g500 [b500 H500]].
 intros [g596 [b596 H596]].
 unfold joint_update_expr_610.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_611 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 597))).
Lemma joint_update_ready_611 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 597 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_611.
Proof.
 intros [g189 [b189 H189]].
 intros [g500 [b500 H500]].
 intros [g597 [b597 H597]].
 unfold joint_update_expr_611.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_612 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 598))).
Lemma joint_update_ready_612 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 598 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_612.
Proof.
 intros [g190 [b190 H190]].
 intros [g500 [b500 H500]].
 intros [g598 [b598 H598]].
 unfold joint_update_expr_612.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_613 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 599))).
Lemma joint_update_ready_613 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 599 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_613.
Proof.
 intros [g191 [b191 H191]].
 intros [g500 [b500 H500]].
 intros [g599 [b599 H599]].
 unfold joint_update_expr_613.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_614 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 600))).
Lemma joint_update_ready_614 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 600 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_614.
Proof.
 intros [g192 [b192 H192]].
 intros [g500 [b500 H500]].
 intros [g600 [b600 H600]].
 unfold joint_update_expr_614.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_615 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 601))).
Lemma joint_update_ready_615 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 601 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_615.
Proof.
 intros [g194 [b194 H194]].
 intros [g500 [b500 H500]].
 intros [g601 [b601 H601]].
 unfold joint_update_expr_615.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_616 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 602))).
Lemma joint_update_ready_616 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 602 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_616.
Proof.
 intros [g453 [b453 H453]].
 intros [g500 [b500 H500]].
 intros [g602 [b602 H602]].
 unfold joint_update_expr_616.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_617 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 603))).
Lemma joint_update_ready_617 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 603 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_617.
Proof.
 intros [g447 [b447 H447]].
 intros [g500 [b500 H500]].
 intros [g603 [b603 H603]].
 unfold joint_update_expr_617.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_618 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 604))).
Lemma joint_update_ready_618 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 604 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_618.
Proof.
 intros [g467 [b467 H467]].
 intros [g500 [b500 H500]].
 intros [g604 [b604 H604]].
 unfold joint_update_expr_618.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_619 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 605))).
Lemma joint_update_ready_619 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 605 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_619.
Proof.
 intros [g457 [b457 H457]].
 intros [g500 [b500 H500]].
 intros [g605 [b605 H605]].
 unfold joint_update_expr_619.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_620 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 500)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 607))).
Lemma joint_update_ready_620 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 500 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 607 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_620.
Proof.
 intros [g472 [b472 H472]].
 intros [g500 [b500 H500]].
 intros [g607 [b607 H607]].
 unfold joint_update_expr_620.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_621 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 406)) (@Eref VarOrder.T (@Eid VarOrder.T 617))).
Lemma joint_update_ready_621 old :
 (exists ground bits, VM.find 406 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 617 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_621.
Proof.
 intros [g406 [b406 H406]].
 intros [g499 [b499 H499]].
 intros [g617 [b617 H617]].
 unfold joint_update_expr_621.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_622 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 608))).
Lemma joint_update_ready_622 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 608 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_622.
Proof.
 intros [g451 [b451 H451]].
 intros [g499 [b499 H499]].
 intros [g608 [b608 H608]].
 unfold joint_update_expr_622.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_623 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 187)) (@Eref VarOrder.T (@Eid VarOrder.T 609))).
Lemma joint_update_ready_623 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 609 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_623.
Proof.
 intros [g187 [b187 H187]].
 intros [g499 [b499 H499]].
 intros [g609 [b609 H609]].
 unfold joint_update_expr_623.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_624 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 610))).
Lemma joint_update_ready_624 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 610 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_624.
Proof.
 intros [g188 [b188 H188]].
 intros [g499 [b499 H499]].
 intros [g610 [b610 H610]].
 unfold joint_update_expr_624.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_625 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 611))).
Lemma joint_update_ready_625 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 611 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_625.
Proof.
 intros [g189 [b189 H189]].
 intros [g499 [b499 H499]].
 intros [g611 [b611 H611]].
 unfold joint_update_expr_625.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_626 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 612))).
Lemma joint_update_ready_626 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 612 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_626.
Proof.
 intros [g190 [b190 H190]].
 intros [g499 [b499 H499]].
 intros [g612 [b612 H612]].
 unfold joint_update_expr_626.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_627 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 613))).
Lemma joint_update_ready_627 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 613 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_627.
Proof.
 intros [g191 [b191 H191]].
 intros [g499 [b499 H499]].
 intros [g613 [b613 H613]].
 unfold joint_update_expr_627.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_628 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 614))).
Lemma joint_update_ready_628 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 614 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_628.
Proof.
 intros [g192 [b192 H192]].
 intros [g499 [b499 H499]].
 intros [g614 [b614 H614]].
 unfold joint_update_expr_628.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_629 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 615))).
Lemma joint_update_ready_629 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 615 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_629.
Proof.
 intros [g194 [b194 H194]].
 intros [g499 [b499 H499]].
 intros [g615 [b615 H615]].
 unfold joint_update_expr_629.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_630 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 616))).
Lemma joint_update_ready_630 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 616 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_630.
Proof.
 intros [g453 [b453 H453]].
 intros [g499 [b499 H499]].
 intros [g616 [b616 H616]].
 unfold joint_update_expr_630.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_631 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 618))).
Lemma joint_update_ready_631 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 618 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_631.
Proof.
 intros [g467 [b467 H467]].
 intros [g499 [b499 H499]].
 intros [g618 [b618 H618]].
 unfold joint_update_expr_631.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_632 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 619))).
Lemma joint_update_ready_632 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 619 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_632.
Proof.
 intros [g457 [b457 H457]].
 intros [g499 [b499 H499]].
 intros [g619 [b619 H619]].
 unfold joint_update_expr_632.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_633 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 499)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 620))).
Lemma joint_update_ready_633 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 499 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 620 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_633.
Proof.
 intros [g472 [b472 H472]].
 intros [g499 [b499 H499]].
 intros [g620 [b620 H620]].
 unfold joint_update_expr_633.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_634 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 497)) (@Eref VarOrder.T (@Eid VarOrder.T 168))).
Lemma joint_update_ready_634 old :
 (exists ground bits, VM.find 168 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 497 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_634.
Proof.
 intros [g168 [b168 H168]].
 intros [g496 [b496 H496]].
 intros [g497 [b497 H497]].
 unfold joint_update_expr_634.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_635 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 498)) (@Eref VarOrder.T (@Eid VarOrder.T 170))).
Lemma joint_update_ready_635 old :
 (exists ground bits, VM.find 170 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 498 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_635.
Proof.
 intros [g170 [b170 H170]].
 intros [g496 [b496 H496]].
 intros [g498 [b498 H498]].
 unfold joint_update_expr_635.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_636 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 621))).
Lemma joint_update_ready_636 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 621 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_636.
Proof.
 intros [g447 [b447 H447]].
 intros [g496 [b496 H496]].
 intros [g621 [b621 H621]].
 unfold joint_update_expr_636.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_637 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 622))).
Lemma joint_update_ready_637 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 622 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_637.
Proof.
 intros [g451 [b451 H451]].
 intros [g496 [b496 H496]].
 intros [g622 [b622 H622]].
 unfold joint_update_expr_637.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_638 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 187)) (@Eref VarOrder.T (@Eid VarOrder.T 623))).
Lemma joint_update_ready_638 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 623 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_638.
Proof.
 intros [g187 [b187 H187]].
 intros [g496 [b496 H496]].
 intros [g623 [b623 H623]].
 unfold joint_update_expr_638.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_639 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 624))).
Lemma joint_update_ready_639 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 624 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_639.
Proof.
 intros [g188 [b188 H188]].
 intros [g496 [b496 H496]].
 intros [g624 [b624 H624]].
 unfold joint_update_expr_639.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_640 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 625))).
Lemma joint_update_ready_640 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 625 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_640.
Proof.
 intros [g189 [b189 H189]].
 intros [g496 [b496 H496]].
 intros [g625 [b625 H625]].
 unfold joint_update_expr_640.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_641 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 626))).
Lemma joint_update_ready_641 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 626 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_641.
Proof.
 intros [g190 [b190 H190]].
 intros [g496 [b496 H496]].
 intros [g626 [b626 H626]].
 unfold joint_update_expr_641.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_642 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 627))).
Lemma joint_update_ready_642 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 627 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_642.
Proof.
 intros [g191 [b191 H191]].
 intros [g496 [b496 H496]].
 intros [g627 [b627 H627]].
 unfold joint_update_expr_642.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_643 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 628))).
Lemma joint_update_ready_643 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 628 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_643.
Proof.
 intros [g192 [b192 H192]].
 intros [g496 [b496 H496]].
 intros [g628 [b628 H628]].
 unfold joint_update_expr_643.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_644 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 629))).
Lemma joint_update_ready_644 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 629 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_644.
Proof.
 intros [g194 [b194 H194]].
 intros [g496 [b496 H496]].
 intros [g629 [b629 H629]].
 unfold joint_update_expr_644.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_645 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 630))).
Lemma joint_update_ready_645 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 630 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_645.
Proof.
 intros [g453 [b453 H453]].
 intros [g496 [b496 H496]].
 intros [g630 [b630 H630]].
 unfold joint_update_expr_645.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_646 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 631))).
Lemma joint_update_ready_646 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 631 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_646.
Proof.
 intros [g467 [b467 H467]].
 intros [g496 [b496 H496]].
 intros [g631 [b631 H631]].
 unfold joint_update_expr_646.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_647 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 632))).
Lemma joint_update_ready_647 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 632 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_647.
Proof.
 intros [g457 [b457 H457]].
 intros [g496 [b496 H496]].
 intros [g632 [b632 H632]].
 unfold joint_update_expr_647.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_648 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 496)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 633))).
Lemma joint_update_ready_648 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 496 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 633 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_648.
Proof.
 intros [g472 [b472 H472]].
 intros [g496 [b496 H496]].
 intros [g633 [b633 H633]].
 unfold joint_update_expr_648.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_649 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 494)) (@Eref VarOrder.T (@Eid VarOrder.T 167))).
Lemma joint_update_ready_649 old :
 (exists ground bits, VM.find 167 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 494 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_649.
Proof.
 intros [g167 [b167 H167]].
 intros [g493 [b493 H493]].
 intros [g494 [b494 H494]].
 unfold joint_update_expr_649.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_650 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 495)) (@Eref VarOrder.T (@Eid VarOrder.T 169))).
Lemma joint_update_ready_650 old :
 (exists ground bits, VM.find 169 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 495 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_650.
Proof.
 intros [g169 [b169 H169]].
 intros [g493 [b493 H493]].
 intros [g495 [b495 H495]].
 unfold joint_update_expr_650.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_651 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 168)) (@Eref VarOrder.T (@Eid VarOrder.T 634))).
Lemma joint_update_ready_651 old :
 (exists ground bits, VM.find 168 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 634 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_651.
Proof.
 intros [g168 [b168 H168]].
 intros [g493 [b493 H493]].
 intros [g634 [b634 H634]].
 unfold joint_update_expr_651.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_652 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 170)) (@Eref VarOrder.T (@Eid VarOrder.T 635))).
Lemma joint_update_ready_652 old :
 (exists ground bits, VM.find 170 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 635 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_652.
Proof.
 intros [g170 [b170 H170]].
 intros [g493 [b493 H493]].
 intros [g635 [b635 H635]].
 unfold joint_update_expr_652.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_653 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 636))).
Lemma joint_update_ready_653 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 636 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_653.
Proof.
 intros [g447 [b447 H447]].
 intros [g493 [b493 H493]].
 intros [g636 [b636 H636]].
 unfold joint_update_expr_653.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_654 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 637))).
Lemma joint_update_ready_654 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 637 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_654.
Proof.
 intros [g451 [b451 H451]].
 intros [g493 [b493 H493]].
 intros [g637 [b637 H637]].
 unfold joint_update_expr_654.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_655 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 187)) (@Eref VarOrder.T (@Eid VarOrder.T 638))).
Lemma joint_update_ready_655 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 638 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_655.
Proof.
 intros [g187 [b187 H187]].
 intros [g493 [b493 H493]].
 intros [g638 [b638 H638]].
 unfold joint_update_expr_655.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_656 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 639))).
Lemma joint_update_ready_656 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 639 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_656.
Proof.
 intros [g188 [b188 H188]].
 intros [g493 [b493 H493]].
 intros [g639 [b639 H639]].
 unfold joint_update_expr_656.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_657 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 640))).
Lemma joint_update_ready_657 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 640 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_657.
Proof.
 intros [g189 [b189 H189]].
 intros [g493 [b493 H493]].
 intros [g640 [b640 H640]].
 unfold joint_update_expr_657.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_658 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 641))).
Lemma joint_update_ready_658 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 641 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_658.
Proof.
 intros [g190 [b190 H190]].
 intros [g493 [b493 H493]].
 intros [g641 [b641 H641]].
 unfold joint_update_expr_658.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_659 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 642))).
Lemma joint_update_ready_659 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 642 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_659.
Proof.
 intros [g191 [b191 H191]].
 intros [g493 [b493 H493]].
 intros [g642 [b642 H642]].
 unfold joint_update_expr_659.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_660 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 643))).
Lemma joint_update_ready_660 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 643 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_660.
Proof.
 intros [g192 [b192 H192]].
 intros [g493 [b493 H493]].
 intros [g643 [b643 H643]].
 unfold joint_update_expr_660.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_661 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 644))).
Lemma joint_update_ready_661 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 644 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_661.
Proof.
 intros [g194 [b194 H194]].
 intros [g493 [b493 H493]].
 intros [g644 [b644 H644]].
 unfold joint_update_expr_661.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_662 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 645))).
Lemma joint_update_ready_662 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 645 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_662.
Proof.
 intros [g453 [b453 H453]].
 intros [g493 [b493 H493]].
 intros [g645 [b645 H645]].
 unfold joint_update_expr_662.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_663 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 646))).
Lemma joint_update_ready_663 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 646 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_663.
Proof.
 intros [g467 [b467 H467]].
 intros [g493 [b493 H493]].
 intros [g646 [b646 H646]].
 unfold joint_update_expr_663.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_664 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 647))).
Lemma joint_update_ready_664 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 647 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_664.
Proof.
 intros [g457 [b457 H457]].
 intros [g493 [b493 H493]].
 intros [g647 [b647 H647]].
 unfold joint_update_expr_664.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_665 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 493)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 648))).
Lemma joint_update_ready_665 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 493 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 648 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_665.
Proof.
 intros [g472 [b472 H472]].
 intros [g493 [b493 H493]].
 intros [g648 [b648 H648]].
 unfold joint_update_expr_665.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_666 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 489)) (@Eref VarOrder.T (@Eid VarOrder.T 151))).
Lemma joint_update_ready_666 old :
 (exists ground bits, VM.find 151 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 489 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_666.
Proof.
 intros [g151 [b151 H151]].
 intros [g488 [b488 H488]].
 intros [g489 [b489 H489]].
 unfold joint_update_expr_666.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_667 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 490)) (@Eref VarOrder.T (@Eid VarOrder.T 153))).
Lemma joint_update_ready_667 old :
 (exists ground bits, VM.find 153 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 490 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_667.
Proof.
 intros [g153 [b153 H153]].
 intros [g488 [b488 H488]].
 intros [g490 [b490 H490]].
 unfold joint_update_expr_667.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_668 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 491)) (@Eref VarOrder.T (@Eid VarOrder.T 150))).
Lemma joint_update_ready_668 old :
 (exists ground bits, VM.find 150 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 491 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_668.
Proof.
 intros [g150 [b150 H150]].
 intros [g488 [b488 H488]].
 intros [g491 [b491 H491]].
 unfold joint_update_expr_668.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_669 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 492)) (@Eref VarOrder.T (@Eid VarOrder.T 152))).
Lemma joint_update_ready_669 old :
 (exists ground bits, VM.find 152 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 492 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_669.
Proof.
 intros [g152 [b152 H152]].
 intros [g488 [b488 H488]].
 intros [g492 [b492 H492]].
 unfold joint_update_expr_669.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_670 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 167)) (@Eref VarOrder.T (@Eid VarOrder.T 649))).
Lemma joint_update_ready_670 old :
 (exists ground bits, VM.find 167 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 649 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_670.
Proof.
 intros [g167 [b167 H167]].
 intros [g488 [b488 H488]].
 intros [g649 [b649 H649]].
 unfold joint_update_expr_670.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_671 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 169)) (@Eref VarOrder.T (@Eid VarOrder.T 650))).
Lemma joint_update_ready_671 old :
 (exists ground bits, VM.find 169 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 650 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_671.
Proof.
 intros [g169 [b169 H169]].
 intros [g488 [b488 H488]].
 intros [g650 [b650 H650]].
 unfold joint_update_expr_671.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_672 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 168)) (@Eref VarOrder.T (@Eid VarOrder.T 651))).
Lemma joint_update_ready_672 old :
 (exists ground bits, VM.find 168 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 651 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_672.
Proof.
 intros [g168 [b168 H168]].
 intros [g488 [b488 H488]].
 intros [g651 [b651 H651]].
 unfold joint_update_expr_672.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_673 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 170)) (@Eref VarOrder.T (@Eid VarOrder.T 652))).
Lemma joint_update_ready_673 old :
 (exists ground bits, VM.find 170 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 652 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_673.
Proof.
 intros [g170 [b170 H170]].
 intros [g488 [b488 H488]].
 intros [g652 [b652 H652]].
 unfold joint_update_expr_673.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_674 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 653))).
Lemma joint_update_ready_674 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 653 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_674.
Proof.
 intros [g447 [b447 H447]].
 intros [g488 [b488 H488]].
 intros [g653 [b653 H653]].
 unfold joint_update_expr_674.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_675 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 654))).
Lemma joint_update_ready_675 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 654 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_675.
Proof.
 intros [g451 [b451 H451]].
 intros [g488 [b488 H488]].
 intros [g654 [b654 H654]].
 unfold joint_update_expr_675.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_676 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 187)) (@Eref VarOrder.T (@Eid VarOrder.T 655))).
Lemma joint_update_ready_676 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 655 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_676.
Proof.
 intros [g187 [b187 H187]].
 intros [g488 [b488 H488]].
 intros [g655 [b655 H655]].
 unfold joint_update_expr_676.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_677 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 656))).
Lemma joint_update_ready_677 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 656 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_677.
Proof.
 intros [g188 [b188 H188]].
 intros [g488 [b488 H488]].
 intros [g656 [b656 H656]].
 unfold joint_update_expr_677.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_678 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 657))).
Lemma joint_update_ready_678 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 657 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_678.
Proof.
 intros [g189 [b189 H189]].
 intros [g488 [b488 H488]].
 intros [g657 [b657 H657]].
 unfold joint_update_expr_678.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_679 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 658))).
Lemma joint_update_ready_679 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 658 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_679.
Proof.
 intros [g190 [b190 H190]].
 intros [g488 [b488 H488]].
 intros [g658 [b658 H658]].
 unfold joint_update_expr_679.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_680 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 659))).
Lemma joint_update_ready_680 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 659 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_680.
Proof.
 intros [g191 [b191 H191]].
 intros [g488 [b488 H488]].
 intros [g659 [b659 H659]].
 unfold joint_update_expr_680.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_681 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 660))).
Lemma joint_update_ready_681 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 660 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_681.
Proof.
 intros [g192 [b192 H192]].
 intros [g488 [b488 H488]].
 intros [g660 [b660 H660]].
 unfold joint_update_expr_681.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_682 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 661))).
Lemma joint_update_ready_682 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 661 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_682.
Proof.
 intros [g194 [b194 H194]].
 intros [g488 [b488 H488]].
 intros [g661 [b661 H661]].
 unfold joint_update_expr_682.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_683 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 662))).
Lemma joint_update_ready_683 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 662 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_683.
Proof.
 intros [g453 [b453 H453]].
 intros [g488 [b488 H488]].
 intros [g662 [b662 H662]].
 unfold joint_update_expr_683.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_684 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 663))).
Lemma joint_update_ready_684 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 663 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_684.
Proof.
 intros [g467 [b467 H467]].
 intros [g488 [b488 H488]].
 intros [g663 [b663 H663]].
 unfold joint_update_expr_684.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_685 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 664))).
Lemma joint_update_ready_685 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 664 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_685.
Proof.
 intros [g457 [b457 H457]].
 intros [g488 [b488 H488]].
 intros [g664 [b664 H664]].
 unfold joint_update_expr_685.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_686 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 488)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 665))).
Lemma joint_update_ready_686 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 488 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 665 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_686.
Proof.
 intros [g472 [b472 H472]].
 intros [g488 [b488 H488]].
 intros [g665 [b665 H665]].
 unfold joint_update_expr_686.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_687 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 666)) (@Eref VarOrder.T (@Eid VarOrder.T 151))).
Lemma joint_update_ready_687 old :
 (exists ground bits, VM.find 151 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 666 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_687.
Proof.
 intros [g151 [b151 H151]].
 intros [g397 [b397 H397]].
 intros [g666 [b666 H666]].
 unfold joint_update_expr_687.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_688 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 667)) (@Eref VarOrder.T (@Eid VarOrder.T 153))).
Lemma joint_update_ready_688 old :
 (exists ground bits, VM.find 153 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 667 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_688.
Proof.
 intros [g153 [b153 H153]].
 intros [g397 [b397 H397]].
 intros [g667 [b667 H667]].
 unfold joint_update_expr_688.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_689 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 668)) (@Eref VarOrder.T (@Eid VarOrder.T 150))).
Lemma joint_update_ready_689 old :
 (exists ground bits, VM.find 150 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 668 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_689.
Proof.
 intros [g150 [b150 H150]].
 intros [g397 [b397 H397]].
 intros [g668 [b668 H668]].
 unfold joint_update_expr_689.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_690 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 669)) (@Eref VarOrder.T (@Eid VarOrder.T 152))).
Lemma joint_update_ready_690 old :
 (exists ground bits, VM.find 152 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 669 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_690.
Proof.
 intros [g152 [b152 H152]].
 intros [g397 [b397 H397]].
 intros [g669 [b669 H669]].
 unfold joint_update_expr_690.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_691 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 670)) (@Eref VarOrder.T (@Eid VarOrder.T 167))).
Lemma joint_update_ready_691 old :
 (exists ground bits, VM.find 167 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 670 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_691.
Proof.
 intros [g167 [b167 H167]].
 intros [g397 [b397 H397]].
 intros [g670 [b670 H670]].
 unfold joint_update_expr_691.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_692 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 671)) (@Eref VarOrder.T (@Eid VarOrder.T 169))).
Lemma joint_update_ready_692 old :
 (exists ground bits, VM.find 169 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 671 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_692.
Proof.
 intros [g169 [b169 H169]].
 intros [g397 [b397 H397]].
 intros [g671 [b671 H671]].
 unfold joint_update_expr_692.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_693 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 672)) (@Eref VarOrder.T (@Eid VarOrder.T 168))).
Lemma joint_update_ready_693 old :
 (exists ground bits, VM.find 168 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 672 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_693.
Proof.
 intros [g168 [b168 H168]].
 intros [g397 [b397 H397]].
 intros [g672 [b672 H672]].
 unfold joint_update_expr_693.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_694 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 673)) (@Eref VarOrder.T (@Eid VarOrder.T 170))).
Lemma joint_update_ready_694 old :
 (exists ground bits, VM.find 170 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 673 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_694.
Proof.
 intros [g170 [b170 H170]].
 intros [g397 [b397 H397]].
 intros [g673 [b673 H673]].
 unfold joint_update_expr_694.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_695 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 674)) (@Eref VarOrder.T (@Eid VarOrder.T 447))).
Lemma joint_update_ready_695 old :
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 674 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_695.
Proof.
 intros [g397 [b397 H397]].
 intros [g447 [b447 H447]].
 intros [g674 [b674 H674]].
 unfold joint_update_expr_695.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_696 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 675)) (@Eref VarOrder.T (@Eid VarOrder.T 451))).
Lemma joint_update_ready_696 old :
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 675 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_696.
Proof.
 intros [g397 [b397 H397]].
 intros [g451 [b451 H451]].
 intros [g675 [b675 H675]].
 unfold joint_update_expr_696.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_697 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 676)) (@Eref VarOrder.T (@Eid VarOrder.T 187))).
Lemma joint_update_ready_697 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 676 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_697.
Proof.
 intros [g187 [b187 H187]].
 intros [g397 [b397 H397]].
 intros [g676 [b676 H676]].
 unfold joint_update_expr_697.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_698 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 677)) (@Eref VarOrder.T (@Eid VarOrder.T 188))).
Lemma joint_update_ready_698 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 677 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_698.
Proof.
 intros [g188 [b188 H188]].
 intros [g397 [b397 H397]].
 intros [g677 [b677 H677]].
 unfold joint_update_expr_698.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_699 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 678)) (@Eref VarOrder.T (@Eid VarOrder.T 189))).
Lemma joint_update_ready_699 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 678 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_699.
Proof.
 intros [g189 [b189 H189]].
 intros [g397 [b397 H397]].
 intros [g678 [b678 H678]].
 unfold joint_update_expr_699.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_700 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 679)) (@Eref VarOrder.T (@Eid VarOrder.T 190))).
Lemma joint_update_ready_700 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 679 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_700.
Proof.
 intros [g190 [b190 H190]].
 intros [g397 [b397 H397]].
 intros [g679 [b679 H679]].
 unfold joint_update_expr_700.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_701 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 680)) (@Eref VarOrder.T (@Eid VarOrder.T 191))).
Lemma joint_update_ready_701 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 680 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_701.
Proof.
 intros [g191 [b191 H191]].
 intros [g397 [b397 H397]].
 intros [g680 [b680 H680]].
 unfold joint_update_expr_701.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_702 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 681)) (@Eref VarOrder.T (@Eid VarOrder.T 192))).
Lemma joint_update_ready_702 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 681 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_702.
Proof.
 intros [g192 [b192 H192]].
 intros [g397 [b397 H397]].
 intros [g681 [b681 H681]].
 unfold joint_update_expr_702.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_703 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 682)) (@Eref VarOrder.T (@Eid VarOrder.T 194))).
Lemma joint_update_ready_703 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 682 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_703.
Proof.
 intros [g194 [b194 H194]].
 intros [g397 [b397 H397]].
 intros [g682 [b682 H682]].
 unfold joint_update_expr_703.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_704 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 683)) (@Eref VarOrder.T (@Eid VarOrder.T 453))).
Lemma joint_update_ready_704 old :
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 683 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_704.
Proof.
 intros [g397 [b397 H397]].
 intros [g453 [b453 H453]].
 intros [g683 [b683 H683]].
 unfold joint_update_expr_704.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_705 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 684)) (@Eref VarOrder.T (@Eid VarOrder.T 467))).
Lemma joint_update_ready_705 old :
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 684 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_705.
Proof.
 intros [g397 [b397 H397]].
 intros [g467 [b467 H467]].
 intros [g684 [b684 H684]].
 unfold joint_update_expr_705.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_706 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 685)) (@Eref VarOrder.T (@Eid VarOrder.T 457))).
Lemma joint_update_ready_706 old :
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 685 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_706.
Proof.
 intros [g397 [b397 H397]].
 intros [g457 [b457 H457]].
 intros [g685 [b685 H685]].
 unfold joint_update_expr_706.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_707 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 686)) (@Eref VarOrder.T (@Eid VarOrder.T 472))).
Lemma joint_update_ready_707 old :
 (exists ground bits, VM.find 397 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 686 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_707.
Proof.
 intros [g397 [b397 H397]].
 intros [g472 [b472 H472]].
 intros [g686 [b686 H686]].
 unfold joint_update_expr_707.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_708 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 151)) (@Eref VarOrder.T (@Eid VarOrder.T 689))).
Lemma joint_update_ready_708 old :
 (exists ground bits, VM.find 151 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 689 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_708.
Proof.
 intros [g151 [b151 H151]].
 intros [g300 [b300 H300]].
 intros [g689 [b689 H689]].
 unfold joint_update_expr_708.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_709 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 153)) (@Eref VarOrder.T (@Eid VarOrder.T 690))).
Lemma joint_update_ready_709 old :
 (exists ground bits, VM.find 153 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 690 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_709.
Proof.
 intros [g153 [b153 H153]].
 intros [g300 [b300 H300]].
 intros [g690 [b690 H690]].
 unfold joint_update_expr_709.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_710 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 687))).
Lemma joint_update_ready_710 old :
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 687 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_710.
Proof.
 intros [g300 [b300 H300]].
 intros [g687 [b687 H687]].
 unfold joint_update_expr_710.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_711 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 688))).
Lemma joint_update_ready_711 old :
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 688 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_711.
Proof.
 intros [g300 [b300 H300]].
 intros [g688 [b688 H688]].
 unfold joint_update_expr_711.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_712 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 167)) (@Eref VarOrder.T (@Eid VarOrder.T 691))).
Lemma joint_update_ready_712 old :
 (exists ground bits, VM.find 167 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 691 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_712.
Proof.
 intros [g167 [b167 H167]].
 intros [g300 [b300 H300]].
 intros [g691 [b691 H691]].
 unfold joint_update_expr_712.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_713 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 169)) (@Eref VarOrder.T (@Eid VarOrder.T 692))).
Lemma joint_update_ready_713 old :
 (exists ground bits, VM.find 169 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 692 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_713.
Proof.
 intros [g169 [b169 H169]].
 intros [g300 [b300 H300]].
 intros [g692 [b692 H692]].
 unfold joint_update_expr_713.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_714 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 168)) (@Eref VarOrder.T (@Eid VarOrder.T 693))).
Lemma joint_update_ready_714 old :
 (exists ground bits, VM.find 168 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 693 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_714.
Proof.
 intros [g168 [b168 H168]].
 intros [g300 [b300 H300]].
 intros [g693 [b693 H693]].
 unfold joint_update_expr_714.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_715 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 170)) (@Eref VarOrder.T (@Eid VarOrder.T 694))).
Lemma joint_update_ready_715 old :
 (exists ground bits, VM.find 170 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 694 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_715.
Proof.
 intros [g170 [b170 H170]].
 intros [g300 [b300 H300]].
 intros [g694 [b694 H694]].
 unfold joint_update_expr_715.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_716 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 695))).
Lemma joint_update_ready_716 old :
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 695 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_716.
Proof.
 intros [g300 [b300 H300]].
 intros [g447 [b447 H447]].
 intros [g695 [b695 H695]].
 unfold joint_update_expr_716.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_717 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 696))).
Lemma joint_update_ready_717 old :
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 696 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_717.
Proof.
 intros [g300 [b300 H300]].
 intros [g451 [b451 H451]].
 intros [g696 [b696 H696]].
 unfold joint_update_expr_717.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_718 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 187)) (@Eref VarOrder.T (@Eid VarOrder.T 697))).
Lemma joint_update_ready_718 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 697 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_718.
Proof.
 intros [g187 [b187 H187]].
 intros [g300 [b300 H300]].
 intros [g697 [b697 H697]].
 unfold joint_update_expr_718.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_719 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 698))).
Lemma joint_update_ready_719 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 698 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_719.
Proof.
 intros [g188 [b188 H188]].
 intros [g300 [b300 H300]].
 intros [g698 [b698 H698]].
 unfold joint_update_expr_719.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_720 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 189)) (@Eref VarOrder.T (@Eid VarOrder.T 699))).
Lemma joint_update_ready_720 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 699 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_720.
Proof.
 intros [g189 [b189 H189]].
 intros [g300 [b300 H300]].
 intros [g699 [b699 H699]].
 unfold joint_update_expr_720.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_721 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 190)) (@Eref VarOrder.T (@Eid VarOrder.T 700))).
Lemma joint_update_ready_721 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 700 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_721.
Proof.
 intros [g190 [b190 H190]].
 intros [g300 [b300 H300]].
 intros [g700 [b700 H700]].
 unfold joint_update_expr_721.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_722 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 191)) (@Eref VarOrder.T (@Eid VarOrder.T 701))).
Lemma joint_update_ready_722 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 701 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_722.
Proof.
 intros [g191 [b191 H191]].
 intros [g300 [b300 H300]].
 intros [g701 [b701 H701]].
 unfold joint_update_expr_722.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_723 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 702))).
Lemma joint_update_ready_723 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 702 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_723.
Proof.
 intros [g192 [b192 H192]].
 intros [g300 [b300 H300]].
 intros [g702 [b702 H702]].
 unfold joint_update_expr_723.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_724 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 703))).
Lemma joint_update_ready_724 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 703 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_724.
Proof.
 intros [g194 [b194 H194]].
 intros [g300 [b300 H300]].
 intros [g703 [b703 H703]].
 unfold joint_update_expr_724.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_725 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 704))).
Lemma joint_update_ready_725 old :
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 704 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_725.
Proof.
 intros [g300 [b300 H300]].
 intros [g453 [b453 H453]].
 intros [g704 [b704 H704]].
 unfold joint_update_expr_725.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_726 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 705))).
Lemma joint_update_ready_726 old :
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 705 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_726.
Proof.
 intros [g300 [b300 H300]].
 intros [g467 [b467 H467]].
 intros [g705 [b705 H705]].
 unfold joint_update_expr_726.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_727 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 706))).
Lemma joint_update_ready_727 old :
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 706 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_727.
Proof.
 intros [g300 [b300 H300]].
 intros [g457 [b457 H457]].
 intros [g706 [b706 H706]].
 unfold joint_update_expr_727.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_728 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 300)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 707))).
Lemma joint_update_ready_728 old :
 (exists ground bits, VM.find 300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 707 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_728.
Proof.
 intros [g300 [b300 H300]].
 intros [g472 [b472 H472]].
 intros [g707 [b707 H707]].
 unfold joint_update_expr_728.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_729 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 484)) (@Eref VarOrder.T (@Eid VarOrder.T 720))).
Lemma joint_update_ready_729 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 484 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 720 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_729.
Proof.
 intros [g128 [b128 H128]].
 intros [g484 [b484 H484]].
 intros [g720 [b720 H720]].
 unfold joint_update_expr_729.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_730 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 479)) (@Eref VarOrder.T (@Eid VarOrder.T 721))).
Lemma joint_update_ready_730 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 479 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 721 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_730.
Proof.
 intros [g128 [b128 H128]].
 intros [g479 [b479 H479]].
 intros [g721 [b721 H721]].
 unfold joint_update_expr_730.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_731 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 708))).
Lemma joint_update_ready_731 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 708 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_731.
Proof.
 intros [g128 [b128 H128]].
 intros [g708 [b708 H708]].
 unfold joint_update_expr_731.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_732 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 709))).
Lemma joint_update_ready_732 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 709 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_732.
Proof.
 intros [g128 [b128 H128]].
 intros [g709 [b709 H709]].
 unfold joint_update_expr_732.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_733 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 150)) (@Eref VarOrder.T (@Eid VarOrder.T 710))).
Lemma joint_update_ready_733 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 150 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 710 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_733.
Proof.
 intros [g128 [b128 H128]].
 intros [g150 [b150 H150]].
 intros [g710 [b710 H710]].
 unfold joint_update_expr_733.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_734 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 152)) (@Eref VarOrder.T (@Eid VarOrder.T 711))).
Lemma joint_update_ready_734 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 152 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 711 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_734.
Proof.
 intros [g128 [b128 H128]].
 intros [g152 [b152 H152]].
 intros [g711 [b711 H711]].
 unfold joint_update_expr_734.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_735 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 487)) (@Eref VarOrder.T (@Eid VarOrder.T 722))).
Lemma joint_update_ready_735 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 487 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 722 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_735.
Proof.
 intros [g128 [b128 H128]].
 intros [g487 [b487 H487]].
 intros [g722 [b722 H722]].
 unfold joint_update_expr_735.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_736 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 167)) (@Eref VarOrder.T (@Eid VarOrder.T 712))).
Lemma joint_update_ready_736 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 167 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 712 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_736.
Proof.
 intros [g128 [b128 H128]].
 intros [g167 [b167 H167]].
 intros [g712 [b712 H712]].
 unfold joint_update_expr_736.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_737 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 169)) (@Eref VarOrder.T (@Eid VarOrder.T 713))).
Lemma joint_update_ready_737 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 169 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 713 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_737.
Proof.
 intros [g128 [b128 H128]].
 intros [g169 [b169 H169]].
 intros [g713 [b713 H713]].
 unfold joint_update_expr_737.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_738 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 168)) (@Eref VarOrder.T (@Eid VarOrder.T 714))).
Lemma joint_update_ready_738 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 168 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 714 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_738.
Proof.
 intros [g128 [b128 H128]].
 intros [g168 [b168 H168]].
 intros [g714 [b714 H714]].
 unfold joint_update_expr_738.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_739 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 170)) (@Eref VarOrder.T (@Eid VarOrder.T 715))).
Lemma joint_update_ready_739 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 170 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 715 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_739.
Proof.
 intros [g128 [b128 H128]].
 intros [g170 [b170 H170]].
 intros [g715 [b715 H715]].
 unfold joint_update_expr_739.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_740 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 447)) (@Eref VarOrder.T (@Eid VarOrder.T 716))).
Lemma joint_update_ready_740 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 716 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_740.
Proof.
 intros [g128 [b128 H128]].
 intros [g447 [b447 H447]].
 intros [g716 [b716 H716]].
 unfold joint_update_expr_740.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_741 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 451)) (@Eref VarOrder.T (@Eid VarOrder.T 717))).
Lemma joint_update_ready_741 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 717 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_741.
Proof.
 intros [g128 [b128 H128]].
 intros [g451 [b451 H451]].
 intros [g717 [b717 H717]].
 unfold joint_update_expr_741.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_742 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 187)) (@Eref VarOrder.T (@Eid VarOrder.T 718))).
Lemma joint_update_ready_742 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 718 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_742.
Proof.
 intros [g128 [b128 H128]].
 intros [g187 [b187 H187]].
 intros [g718 [b718 H718]].
 unfold joint_update_expr_742.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_743 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 188)) (@Eref VarOrder.T (@Eid VarOrder.T 719))).
Lemma joint_update_ready_743 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 719 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_743.
Proof.
 intros [g128 [b128 H128]].
 intros [g188 [b188 H188]].
 intros [g719 [b719 H719]].
 unfold joint_update_expr_743.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_744 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 192)) (@Eref VarOrder.T (@Eid VarOrder.T 723))).
Lemma joint_update_ready_744 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 723 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_744.
Proof.
 intros [g128 [b128 H128]].
 intros [g192 [b192 H192]].
 intros [g723 [b723 H723]].
 unfold joint_update_expr_744.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_745 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 194)) (@Eref VarOrder.T (@Eid VarOrder.T 724))).
Lemma joint_update_ready_745 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 724 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_745.
Proof.
 intros [g128 [b128 H128]].
 intros [g194 [b194 H194]].
 intros [g724 [b724 H724]].
 unfold joint_update_expr_745.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_746 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 453)) (@Eref VarOrder.T (@Eid VarOrder.T 725))).
Lemma joint_update_ready_746 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 725 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_746.
Proof.
 intros [g128 [b128 H128]].
 intros [g453 [b453 H453]].
 intros [g725 [b725 H725]].
 unfold joint_update_expr_746.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_747 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 467)) (@Eref VarOrder.T (@Eid VarOrder.T 726))).
Lemma joint_update_ready_747 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 726 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_747.
Proof.
 intros [g128 [b128 H128]].
 intros [g467 [b467 H467]].
 intros [g726 [b726 H726]].
 unfold joint_update_expr_747.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_748 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 457)) (@Eref VarOrder.T (@Eid VarOrder.T 727))).
Lemma joint_update_ready_748 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 727 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_748.
Proof.
 intros [g128 [b128 H128]].
 intros [g457 [b457 H457]].
 intros [g727 [b727 H727]].
 unfold joint_update_expr_748.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_749 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 472)) (@Eref VarOrder.T (@Eid VarOrder.T 728))).
Lemma joint_update_ready_749 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 728 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_749.
Proof.
 intros [g128 [b128 H128]].
 intros [g472 [b472 H472]].
 intros [g728 [b728 H728]].
 unfold joint_update_expr_749.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_750 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 729)) (@Eref VarOrder.T (@Eid VarOrder.T 189))).
Lemma joint_update_ready_750 old :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 729 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_750.
Proof.
 intros [g189 [b189 H189]].
 intros [g480 [b480 H480]].
 intros [g729 [b729 H729]].
 unfold joint_update_expr_750.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_751 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 730)) (@Eref VarOrder.T (@Eid VarOrder.T 190))).
Lemma joint_update_ready_751 old :
 (exists ground bits, VM.find 190 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 730 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_751.
Proof.
 intros [g190 [b190 H190]].
 intros [g480 [b480 H480]].
 intros [g730 [b730 H730]].
 unfold joint_update_expr_751.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_752 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 731)) (@Eref VarOrder.T (@Eid VarOrder.T 150))).
Lemma joint_update_ready_752 old :
 (exists ground bits, VM.find 150 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 731 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_752.
Proof.
 intros [g150 [b150 H150]].
 intros [g480 [b480 H480]].
 intros [g731 [b731 H731]].
 unfold joint_update_expr_752.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_753 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 732)) (@Eref VarOrder.T (@Eid VarOrder.T 152))).
Lemma joint_update_ready_753 old :
 (exists ground bits, VM.find 152 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 732 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_753.
Proof.
 intros [g152 [b152 H152]].
 intros [g480 [b480 H480]].
 intros [g732 [b732 H732]].
 unfold joint_update_expr_753.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_754 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 733)) (@Eref VarOrder.T (@Eid VarOrder.T 151))).
Lemma joint_update_ready_754 old :
 (exists ground bits, VM.find 151 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 733 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_754.
Proof.
 intros [g151 [b151 H151]].
 intros [g480 [b480 H480]].
 intros [g733 [b733 H733]].
 unfold joint_update_expr_754.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_755 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 734)) (@Eref VarOrder.T (@Eid VarOrder.T 153))).
Lemma joint_update_ready_755 old :
 (exists ground bits, VM.find 153 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 734 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_755.
Proof.
 intros [g153 [b153 H153]].
 intros [g480 [b480 H480]].
 intros [g734 [b734 H734]].
 unfold joint_update_expr_755.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_756 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 735)) (@Eref VarOrder.T (@Eid VarOrder.T 191))).
Lemma joint_update_ready_756 old :
 (exists ground bits, VM.find 191 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 735 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_756.
Proof.
 intros [g191 [b191 H191]].
 intros [g480 [b480 H480]].
 intros [g735 [b735 H735]].
 unfold joint_update_expr_756.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_757 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 736)) (@Eref VarOrder.T (@Eid VarOrder.T 167))).
Lemma joint_update_ready_757 old :
 (exists ground bits, VM.find 167 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 736 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_757.
Proof.
 intros [g167 [b167 H167]].
 intros [g480 [b480 H480]].
 intros [g736 [b736 H736]].
 unfold joint_update_expr_757.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_758 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 737)) (@Eref VarOrder.T (@Eid VarOrder.T 169))).
Lemma joint_update_ready_758 old :
 (exists ground bits, VM.find 169 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 737 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_758.
Proof.
 intros [g169 [b169 H169]].
 intros [g480 [b480 H480]].
 intros [g737 [b737 H737]].
 unfold joint_update_expr_758.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_759 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 738)) (@Eref VarOrder.T (@Eid VarOrder.T 168))).
Lemma joint_update_ready_759 old :
 (exists ground bits, VM.find 168 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 738 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_759.
Proof.
 intros [g168 [b168 H168]].
 intros [g480 [b480 H480]].
 intros [g738 [b738 H738]].
 unfold joint_update_expr_759.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_760 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 739)) (@Eref VarOrder.T (@Eid VarOrder.T 170))).
Lemma joint_update_ready_760 old :
 (exists ground bits, VM.find 170 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 739 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_760.
Proof.
 intros [g170 [b170 H170]].
 intros [g480 [b480 H480]].
 intros [g739 [b739 H739]].
 unfold joint_update_expr_760.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_761 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 740)) (@Eref VarOrder.T (@Eid VarOrder.T 447))).
Lemma joint_update_ready_761 old :
 (exists ground bits, VM.find 447 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 740 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_761.
Proof.
 intros [g447 [b447 H447]].
 intros [g480 [b480 H480]].
 intros [g740 [b740 H740]].
 unfold joint_update_expr_761.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_762 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 741)) (@Eref VarOrder.T (@Eid VarOrder.T 451))).
Lemma joint_update_ready_762 old :
 (exists ground bits, VM.find 451 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 741 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_762.
Proof.
 intros [g451 [b451 H451]].
 intros [g480 [b480 H480]].
 intros [g741 [b741 H741]].
 unfold joint_update_expr_762.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_763 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 742)) (@Eref VarOrder.T (@Eid VarOrder.T 187))).
Lemma joint_update_ready_763 old :
 (exists ground bits, VM.find 187 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 742 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_763.
Proof.
 intros [g187 [b187 H187]].
 intros [g480 [b480 H480]].
 intros [g742 [b742 H742]].
 unfold joint_update_expr_763.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_764 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 743)) (@Eref VarOrder.T (@Eid VarOrder.T 188))).
Lemma joint_update_ready_764 old :
 (exists ground bits, VM.find 188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 743 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_764.
Proof.
 intros [g188 [b188 H188]].
 intros [g480 [b480 H480]].
 intros [g743 [b743 H743]].
 unfold joint_update_expr_764.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_765 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 744)) (@Eref VarOrder.T (@Eid VarOrder.T 192))).
Lemma joint_update_ready_765 old :
 (exists ground bits, VM.find 192 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 744 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_765.
Proof.
 intros [g192 [b192 H192]].
 intros [g480 [b480 H480]].
 intros [g744 [b744 H744]].
 unfold joint_update_expr_765.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_766 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 745)) (@Eref VarOrder.T (@Eid VarOrder.T 194))).
Lemma joint_update_ready_766 old :
 (exists ground bits, VM.find 194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 745 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_766.
Proof.
 intros [g194 [b194 H194]].
 intros [g480 [b480 H480]].
 intros [g745 [b745 H745]].
 unfold joint_update_expr_766.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_767 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 746)) (@Eref VarOrder.T (@Eid VarOrder.T 453))).
Lemma joint_update_ready_767 old :
 (exists ground bits, VM.find 453 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 746 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_767.
Proof.
 intros [g453 [b453 H453]].
 intros [g480 [b480 H480]].
 intros [g746 [b746 H746]].
 unfold joint_update_expr_767.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_768 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 747)) (@Eref VarOrder.T (@Eid VarOrder.T 467))).
Lemma joint_update_ready_768 old :
 (exists ground bits, VM.find 467 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 747 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_768.
Proof.
 intros [g467 [b467 H467]].
 intros [g480 [b480 H480]].
 intros [g747 [b747 H747]].
 unfold joint_update_expr_768.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_769 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 748)) (@Eref VarOrder.T (@Eid VarOrder.T 457))).
Lemma joint_update_ready_769 old :
 (exists ground bits, VM.find 457 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 748 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_769.
Proof.
 intros [g457 [b457 H457]].
 intros [g480 [b480 H480]].
 intros [g748 [b748 H748]].
 unfold joint_update_expr_769.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_770 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 480)) (@Eref VarOrder.T (@Eid VarOrder.T 749)) (@Eref VarOrder.T (@Eid VarOrder.T 472))).
Lemma joint_update_ready_770 old :
 (exists ground bits, VM.find 472 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 480 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 749 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_770.
Proof.
 intros [g472 [b472 H472]].
 intros [g480 [b480 H480]].
 intros [g749 [b749 H749]].
 unfold joint_update_expr_770.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_953 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 785))).
Lemma joint_update_ready_953 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_953.
Proof.
 intros [g785 [b785 H785]].
 unfold joint_update_expr_953.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_954 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 784)) (@Eref VarOrder.T (@Eid VarOrder.T 953))).
Lemma joint_update_ready_954 old :
 (exists ground bits, VM.find 784 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 953 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_954.
Proof.
 intros [g784 [b784 H784]].
 intros [g953 [b953 H953]].
 unfold joint_update_expr_954.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_955 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 786)).
Lemma joint_update_ready_955 old :
 (exists ground bits, VM.find 786 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_955.
Proof.
 intros [g786 [b786 H786]].
 unfold joint_update_expr_955.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_956 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 851))).
Lemma joint_update_ready_956 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 851 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_956.
Proof.
 intros [g785 [b785 H785]].
 intros [g851 [b851 H851]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_956.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_957 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 852))).
Lemma joint_update_ready_957 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_957.
Proof.
 intros [g785 [b785 H785]].
 intros [g852 [b852 H852]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_957.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_958 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 853))).
Lemma joint_update_ready_958 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 853 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_958.
Proof.
 intros [g785 [b785 H785]].
 intros [g853 [b853 H853]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_958.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_959 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 854))).
Lemma joint_update_ready_959 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 854 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_959.
Proof.
 intros [g785 [b785 H785]].
 intros [g854 [b854 H854]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_959.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_960 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 855))).
Lemma joint_update_ready_960 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 855 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_960.
Proof.
 intros [g785 [b785 H785]].
 intros [g855 [b855 H855]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_960.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_961 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 856))).
Lemma joint_update_ready_961 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 856 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_961.
Proof.
 intros [g785 [b785 H785]].
 intros [g856 [b856 H856]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_961.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_962 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 857))).
Lemma joint_update_ready_962 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 857 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_962.
Proof.
 intros [g785 [b785 H785]].
 intros [g857 [b857 H857]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_962.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_963 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 858))).
Lemma joint_update_ready_963 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 858 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_963.
Proof.
 intros [g785 [b785 H785]].
 intros [g858 [b858 H858]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_963.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_964 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 859))).
Lemma joint_update_ready_964 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 859 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_964.
Proof.
 intros [g785 [b785 H785]].
 intros [g859 [b859 H859]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_964.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_965 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 860))).
Lemma joint_update_ready_965 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 860 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_965.
Proof.
 intros [g785 [b785 H785]].
 intros [g860 [b860 H860]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_965.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_966 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 861))).
Lemma joint_update_ready_966 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 861 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_966.
Proof.
 intros [g785 [b785 H785]].
 intros [g861 [b861 H861]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_966.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_967 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::true; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 862))).
Lemma joint_update_ready_967 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 862 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_967.
Proof.
 intros [g785 [b785 H785]].
 intros [g862 [b862 H862]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_967.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_968 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 863))).
Lemma joint_update_ready_968 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 863 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_968.
Proof.
 intros [g785 [b785 H785]].
 intros [g863 [b863 H863]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_968.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_969 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 864))).
Lemma joint_update_ready_969 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 864 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_969.
Proof.
 intros [g785 [b785 H785]].
 intros [g864 [b864 H864]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_969.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_970 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 865))).
Lemma joint_update_ready_970 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 865 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_970.
Proof.
 intros [g785 [b785 H785]].
 intros [g865 [b865 H865]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_970.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_971 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 866))).
Lemma joint_update_ready_971 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 866 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_971.
Proof.
 intros [g785 [b785 H785]].
 intros [g866 [b866 H866]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_971.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_972 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 867))).
Lemma joint_update_ready_972 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 867 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_972.
Proof.
 intros [g785 [b785 H785]].
 intros [g867 [b867 H867]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_972.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_973 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 868))).
Lemma joint_update_ready_973 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 868 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_973.
Proof.
 intros [g785 [b785 H785]].
 intros [g868 [b868 H868]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_973.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_974 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 869))).
Lemma joint_update_ready_974 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 869 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_974.
Proof.
 intros [g785 [b785 H785]].
 intros [g869 [b869 H869]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_974.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_975 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 870))).
Lemma joint_update_ready_975 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 870 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_975.
Proof.
 intros [g785 [b785 H785]].
 intros [g870 [b870 H870]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_975.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_976 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 871))).
Lemma joint_update_ready_976 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 871 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_976.
Proof.
 intros [g785 [b785 H785]].
 intros [g871 [b871 H871]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_976.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_977 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 872))).
Lemma joint_update_ready_977 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 872 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_977.
Proof.
 intros [g785 [b785 H785]].
 intros [g872 [b872 H872]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_977.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_978 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; true; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 873))).
Lemma joint_update_ready_978 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 873 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_978.
Proof.
 intros [g785 [b785 H785]].
 intros [g873 [b873 H873]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_978.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_979 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 874))).
Lemma joint_update_ready_979 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 874 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_979.
Proof.
 intros [g785 [b785 H785]].
 intros [g874 [b874 H874]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_979.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_980 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 875))).
Lemma joint_update_ready_980 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 875 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_980.
Proof.
 intros [g785 [b785 H785]].
 intros [g875 [b875 H875]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_980.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_981 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 876))).
Lemma joint_update_ready_981 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 876 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_981.
Proof.
 intros [g785 [b785 H785]].
 intros [g876 [b876 H876]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_981.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_982 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 877))).
Lemma joint_update_ready_982 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 877 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_982.
Proof.
 intros [g785 [b785 H785]].
 intros [g877 [b877 H877]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_982.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_983 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 878))).
Lemma joint_update_ready_983 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 878 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_983.
Proof.
 intros [g785 [b785 H785]].
 intros [g878 [b878 H878]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_983.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_984 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 879))).
Lemma joint_update_ready_984 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 879 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_984.
Proof.
 intros [g785 [b785 H785]].
 intros [g879 [b879 H879]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_984.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_985 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 880))).
Lemma joint_update_ready_985 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 880 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_985.
Proof.
 intros [g785 [b785 H785]].
 intros [g880 [b880 H880]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_985.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_986 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 881))).
Lemma joint_update_ready_986 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 881 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_986.
Proof.
 intros [g785 [b785 H785]].
 intros [g881 [b881 H881]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_986.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_987 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 785))) (@Eref VarOrder.T (@Eid VarOrder.T 955)) (@Eref VarOrder.T (@Eid VarOrder.T 882))).
Lemma joint_update_ready_987 old :
 (exists ground bits, VM.find 785 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 882 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_987.
Proof.
 intros [g785 [b785 H785]].
 intros [g882 [b882 H882]].
 intros [g955 [b955 H955]].
 unfold joint_update_expr_987.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1021 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 956)) (@Eref VarOrder.T (@Eid VarOrder.T 851))).
Lemma joint_update_ready_1021 old :
 (exists ground bits, VM.find 851 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 956 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1021.
Proof.
 intros [g851 [b851 H851]].
 intros [g954 [b954 H954]].
 intros [g956 [b956 H956]].
 unfold joint_update_expr_1021.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1022 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 957)) (@Eref VarOrder.T (@Eid VarOrder.T 852))).
Lemma joint_update_ready_1022 old :
 (exists ground bits, VM.find 852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 957 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1022.
Proof.
 intros [g852 [b852 H852]].
 intros [g954 [b954 H954]].
 intros [g957 [b957 H957]].
 unfold joint_update_expr_1022.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1023 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 958)) (@Eref VarOrder.T (@Eid VarOrder.T 853))).
Lemma joint_update_ready_1023 old :
 (exists ground bits, VM.find 853 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 958 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1023.
Proof.
 intros [g853 [b853 H853]].
 intros [g954 [b954 H954]].
 intros [g958 [b958 H958]].
 unfold joint_update_expr_1023.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1024 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 959)) (@Eref VarOrder.T (@Eid VarOrder.T 854))).
Lemma joint_update_ready_1024 old :
 (exists ground bits, VM.find 854 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 959 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1024.
Proof.
 intros [g854 [b854 H854]].
 intros [g954 [b954 H954]].
 intros [g959 [b959 H959]].
 unfold joint_update_expr_1024.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1025 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 960)) (@Eref VarOrder.T (@Eid VarOrder.T 855))).
Lemma joint_update_ready_1025 old :
 (exists ground bits, VM.find 855 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 960 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1025.
Proof.
 intros [g855 [b855 H855]].
 intros [g954 [b954 H954]].
 intros [g960 [b960 H960]].
 unfold joint_update_expr_1025.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1026 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 961)) (@Eref VarOrder.T (@Eid VarOrder.T 856))).
Lemma joint_update_ready_1026 old :
 (exists ground bits, VM.find 856 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 961 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1026.
Proof.
 intros [g856 [b856 H856]].
 intros [g954 [b954 H954]].
 intros [g961 [b961 H961]].
 unfold joint_update_expr_1026.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1027 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 962)) (@Eref VarOrder.T (@Eid VarOrder.T 857))).
Lemma joint_update_ready_1027 old :
 (exists ground bits, VM.find 857 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 962 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1027.
Proof.
 intros [g857 [b857 H857]].
 intros [g954 [b954 H954]].
 intros [g962 [b962 H962]].
 unfold joint_update_expr_1027.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1028 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 963)) (@Eref VarOrder.T (@Eid VarOrder.T 858))).
Lemma joint_update_ready_1028 old :
 (exists ground bits, VM.find 858 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 963 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1028.
Proof.
 intros [g858 [b858 H858]].
 intros [g954 [b954 H954]].
 intros [g963 [b963 H963]].
 unfold joint_update_expr_1028.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1029 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 964)) (@Eref VarOrder.T (@Eid VarOrder.T 859))).
Lemma joint_update_ready_1029 old :
 (exists ground bits, VM.find 859 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 964 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1029.
Proof.
 intros [g859 [b859 H859]].
 intros [g954 [b954 H954]].
 intros [g964 [b964 H964]].
 unfold joint_update_expr_1029.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1030 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 965)) (@Eref VarOrder.T (@Eid VarOrder.T 860))).
Lemma joint_update_ready_1030 old :
 (exists ground bits, VM.find 860 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 965 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1030.
Proof.
 intros [g860 [b860 H860]].
 intros [g954 [b954 H954]].
 intros [g965 [b965 H965]].
 unfold joint_update_expr_1030.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1031 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 966)) (@Eref VarOrder.T (@Eid VarOrder.T 861))).
Lemma joint_update_ready_1031 old :
 (exists ground bits, VM.find 861 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 966 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1031.
Proof.
 intros [g861 [b861 H861]].
 intros [g954 [b954 H954]].
 intros [g966 [b966 H966]].
 unfold joint_update_expr_1031.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1032 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 967)) (@Eref VarOrder.T (@Eid VarOrder.T 862))).
Lemma joint_update_ready_1032 old :
 (exists ground bits, VM.find 862 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 967 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1032.
Proof.
 intros [g862 [b862 H862]].
 intros [g954 [b954 H954]].
 intros [g967 [b967 H967]].
 unfold joint_update_expr_1032.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1033 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 968)) (@Eref VarOrder.T (@Eid VarOrder.T 863))).
Lemma joint_update_ready_1033 old :
 (exists ground bits, VM.find 863 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 968 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1033.
Proof.
 intros [g863 [b863 H863]].
 intros [g954 [b954 H954]].
 intros [g968 [b968 H968]].
 unfold joint_update_expr_1033.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1034 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 969)) (@Eref VarOrder.T (@Eid VarOrder.T 864))).
Lemma joint_update_ready_1034 old :
 (exists ground bits, VM.find 864 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 969 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1034.
Proof.
 intros [g864 [b864 H864]].
 intros [g954 [b954 H954]].
 intros [g969 [b969 H969]].
 unfold joint_update_expr_1034.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1035 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 970)) (@Eref VarOrder.T (@Eid VarOrder.T 865))).
Lemma joint_update_ready_1035 old :
 (exists ground bits, VM.find 865 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 970 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1035.
Proof.
 intros [g865 [b865 H865]].
 intros [g954 [b954 H954]].
 intros [g970 [b970 H970]].
 unfold joint_update_expr_1035.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1036 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 971)) (@Eref VarOrder.T (@Eid VarOrder.T 866))).
Lemma joint_update_ready_1036 old :
 (exists ground bits, VM.find 866 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 971 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1036.
Proof.
 intros [g866 [b866 H866]].
 intros [g954 [b954 H954]].
 intros [g971 [b971 H971]].
 unfold joint_update_expr_1036.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1037 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 972)) (@Eref VarOrder.T (@Eid VarOrder.T 867))).
Lemma joint_update_ready_1037 old :
 (exists ground bits, VM.find 867 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 972 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1037.
Proof.
 intros [g867 [b867 H867]].
 intros [g954 [b954 H954]].
 intros [g972 [b972 H972]].
 unfold joint_update_expr_1037.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1038 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 973)) (@Eref VarOrder.T (@Eid VarOrder.T 868))).
Lemma joint_update_ready_1038 old :
 (exists ground bits, VM.find 868 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 973 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1038.
Proof.
 intros [g868 [b868 H868]].
 intros [g954 [b954 H954]].
 intros [g973 [b973 H973]].
 unfold joint_update_expr_1038.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1039 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 974)) (@Eref VarOrder.T (@Eid VarOrder.T 869))).
Lemma joint_update_ready_1039 old :
 (exists ground bits, VM.find 869 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 974 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1039.
Proof.
 intros [g869 [b869 H869]].
 intros [g954 [b954 H954]].
 intros [g974 [b974 H974]].
 unfold joint_update_expr_1039.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1040 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 975)) (@Eref VarOrder.T (@Eid VarOrder.T 870))).
Lemma joint_update_ready_1040 old :
 (exists ground bits, VM.find 870 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 975 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1040.
Proof.
 intros [g870 [b870 H870]].
 intros [g954 [b954 H954]].
 intros [g975 [b975 H975]].
 unfold joint_update_expr_1040.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1041 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 976)) (@Eref VarOrder.T (@Eid VarOrder.T 871))).
Lemma joint_update_ready_1041 old :
 (exists ground bits, VM.find 871 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 976 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1041.
Proof.
 intros [g871 [b871 H871]].
 intros [g954 [b954 H954]].
 intros [g976 [b976 H976]].
 unfold joint_update_expr_1041.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1042 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 977)) (@Eref VarOrder.T (@Eid VarOrder.T 872))).
Lemma joint_update_ready_1042 old :
 (exists ground bits, VM.find 872 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 977 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1042.
Proof.
 intros [g872 [b872 H872]].
 intros [g954 [b954 H954]].
 intros [g977 [b977 H977]].
 unfold joint_update_expr_1042.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1043 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 978)) (@Eref VarOrder.T (@Eid VarOrder.T 873))).
Lemma joint_update_ready_1043 old :
 (exists ground bits, VM.find 873 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 978 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1043.
Proof.
 intros [g873 [b873 H873]].
 intros [g954 [b954 H954]].
 intros [g978 [b978 H978]].
 unfold joint_update_expr_1043.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1044 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 979)) (@Eref VarOrder.T (@Eid VarOrder.T 874))).
Lemma joint_update_ready_1044 old :
 (exists ground bits, VM.find 874 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 979 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1044.
Proof.
 intros [g874 [b874 H874]].
 intros [g954 [b954 H954]].
 intros [g979 [b979 H979]].
 unfold joint_update_expr_1044.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1045 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 980)) (@Eref VarOrder.T (@Eid VarOrder.T 875))).
Lemma joint_update_ready_1045 old :
 (exists ground bits, VM.find 875 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 980 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1045.
Proof.
 intros [g875 [b875 H875]].
 intros [g954 [b954 H954]].
 intros [g980 [b980 H980]].
 unfold joint_update_expr_1045.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1046 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 981)) (@Eref VarOrder.T (@Eid VarOrder.T 876))).
Lemma joint_update_ready_1046 old :
 (exists ground bits, VM.find 876 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 981 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1046.
Proof.
 intros [g876 [b876 H876]].
 intros [g954 [b954 H954]].
 intros [g981 [b981 H981]].
 unfold joint_update_expr_1046.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1047 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 982)) (@Eref VarOrder.T (@Eid VarOrder.T 877))).
Lemma joint_update_ready_1047 old :
 (exists ground bits, VM.find 877 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 982 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1047.
Proof.
 intros [g877 [b877 H877]].
 intros [g954 [b954 H954]].
 intros [g982 [b982 H982]].
 unfold joint_update_expr_1047.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1048 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 983)) (@Eref VarOrder.T (@Eid VarOrder.T 878))).
Lemma joint_update_ready_1048 old :
 (exists ground bits, VM.find 878 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 983 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1048.
Proof.
 intros [g878 [b878 H878]].
 intros [g954 [b954 H954]].
 intros [g983 [b983 H983]].
 unfold joint_update_expr_1048.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1049 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 984)) (@Eref VarOrder.T (@Eid VarOrder.T 879))).
Lemma joint_update_ready_1049 old :
 (exists ground bits, VM.find 879 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 984 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1049.
Proof.
 intros [g879 [b879 H879]].
 intros [g954 [b954 H954]].
 intros [g984 [b984 H984]].
 unfold joint_update_expr_1049.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1050 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 985)) (@Eref VarOrder.T (@Eid VarOrder.T 880))).
Lemma joint_update_ready_1050 old :
 (exists ground bits, VM.find 880 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 985 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1050.
Proof.
 intros [g880 [b880 H880]].
 intros [g954 [b954 H954]].
 intros [g985 [b985 H985]].
 unfold joint_update_expr_1050.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1051 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 986)) (@Eref VarOrder.T (@Eid VarOrder.T 881))).
Lemma joint_update_ready_1051 old :
 (exists ground bits, VM.find 881 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 986 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1051.
Proof.
 intros [g881 [b881 H881]].
 intros [g954 [b954 H954]].
 intros [g986 [b986 H986]].
 unfold joint_update_expr_1051.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1052 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 954)) (@Eref VarOrder.T (@Eid VarOrder.T 987)) (@Eref VarOrder.T (@Eid VarOrder.T 882))).
Lemma joint_update_ready_1052 old :
 (exists ground bits, VM.find 882 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 954 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 987 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1052.
Proof.
 intros [g882 [b882 H882]].
 intros [g954 [b954 H954]].
 intros [g987 [b987 H987]].
 unfold joint_update_expr_1052.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1085 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 787)).
Lemma joint_update_ready_1085 old :
 (exists ground bits, VM.find 787 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1085.
Proof.
 intros [g787 [b787 H787]].
 unfold joint_update_expr_1085.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1086 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 788)).
Lemma joint_update_ready_1086 old :
 (exists ground bits, VM.find 788 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1086.
Proof.
 intros [g788 [b788 H788]].
 unfold joint_update_expr_1086.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1087 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 789)).
Lemma joint_update_ready_1087 old :
 (exists ground bits, VM.find 789 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1087.
Proof.
 intros [g789 [b789 H789]].
 unfold joint_update_expr_1087.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1088 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 790)).
Lemma joint_update_ready_1088 old :
 (exists ground bits, VM.find 790 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1088.
Proof.
 intros [g790 [b790 H790]].
 unfold joint_update_expr_1088.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1089 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 791)).
Lemma joint_update_ready_1089 old :
 (exists ground bits, VM.find 791 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1089.
Proof.
 intros [g791 [b791 H791]].
 unfold joint_update_expr_1089.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1090 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 792)).
Lemma joint_update_ready_1090 old :
 (exists ground bits, VM.find 792 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1090.
Proof.
 intros [g792 [b792 H792]].
 unfold joint_update_expr_1090.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1091 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 793)).
Lemma joint_update_ready_1091 old :
 (exists ground bits, VM.find 793 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1091.
Proof.
 intros [g793 [b793 H793]].
 unfold joint_update_expr_1091.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1092 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 794)).
Lemma joint_update_ready_1092 old :
 (exists ground bits, VM.find 794 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1092.
Proof.
 intros [g794 [b794 H794]].
 unfold joint_update_expr_1092.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1093 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 795)).
Lemma joint_update_ready_1093 old :
 (exists ground bits, VM.find 795 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1093.
Proof.
 intros [g795 [b795 H795]].
 unfold joint_update_expr_1093.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1094 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 796)).
Lemma joint_update_ready_1094 old :
 (exists ground bits, VM.find 796 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1094.
Proof.
 intros [g796 [b796 H796]].
 unfold joint_update_expr_1094.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1095 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 797)).
Lemma joint_update_ready_1095 old :
 (exists ground bits, VM.find 797 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1095.
Proof.
 intros [g797 [b797 H797]].
 unfold joint_update_expr_1095.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1096 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 798)).
Lemma joint_update_ready_1096 old :
 (exists ground bits, VM.find 798 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1096.
Proof.
 intros [g798 [b798 H798]].
 unfold joint_update_expr_1096.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1097 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 799)).
Lemma joint_update_ready_1097 old :
 (exists ground bits, VM.find 799 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1097.
Proof.
 intros [g799 [b799 H799]].
 unfold joint_update_expr_1097.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1098 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 800)).
Lemma joint_update_ready_1098 old :
 (exists ground bits, VM.find 800 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1098.
Proof.
 intros [g800 [b800 H800]].
 unfold joint_update_expr_1098.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1099 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 801)).
Lemma joint_update_ready_1099 old :
 (exists ground bits, VM.find 801 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1099.
Proof.
 intros [g801 [b801 H801]].
 unfold joint_update_expr_1099.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1100 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 802)).
Lemma joint_update_ready_1100 old :
 (exists ground bits, VM.find 802 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1100.
Proof.
 intros [g802 [b802 H802]].
 unfold joint_update_expr_1100.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1101 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 803)).
Lemma joint_update_ready_1101 old :
 (exists ground bits, VM.find 803 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1101.
Proof.
 intros [g803 [b803 H803]].
 unfold joint_update_expr_1101.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1102 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 804)).
Lemma joint_update_ready_1102 old :
 (exists ground bits, VM.find 804 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1102.
Proof.
 intros [g804 [b804 H804]].
 unfold joint_update_expr_1102.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1103 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 805)).
Lemma joint_update_ready_1103 old :
 (exists ground bits, VM.find 805 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1103.
Proof.
 intros [g805 [b805 H805]].
 unfold joint_update_expr_1103.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1104 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 806)).
Lemma joint_update_ready_1104 old :
 (exists ground bits, VM.find 806 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1104.
Proof.
 intros [g806 [b806 H806]].
 unfold joint_update_expr_1104.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1105 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 807)).
Lemma joint_update_ready_1105 old :
 (exists ground bits, VM.find 807 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1105.
Proof.
 intros [g807 [b807 H807]].
 unfold joint_update_expr_1105.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1106 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 808)).
Lemma joint_update_ready_1106 old :
 (exists ground bits, VM.find 808 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1106.
Proof.
 intros [g808 [b808 H808]].
 unfold joint_update_expr_1106.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1107 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 809)).
Lemma joint_update_ready_1107 old :
 (exists ground bits, VM.find 809 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1107.
Proof.
 intros [g809 [b809 H809]].
 unfold joint_update_expr_1107.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1108 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 810)).
Lemma joint_update_ready_1108 old :
 (exists ground bits, VM.find 810 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1108.
Proof.
 intros [g810 [b810 H810]].
 unfold joint_update_expr_1108.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1109 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 811)).
Lemma joint_update_ready_1109 old :
 (exists ground bits, VM.find 811 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1109.
Proof.
 intros [g811 [b811 H811]].
 unfold joint_update_expr_1109.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1110 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 812)).
Lemma joint_update_ready_1110 old :
 (exists ground bits, VM.find 812 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1110.
Proof.
 intros [g812 [b812 H812]].
 unfold joint_update_expr_1110.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1111 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 813)).
Lemma joint_update_ready_1111 old :
 (exists ground bits, VM.find 813 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1111.
Proof.
 intros [g813 [b813 H813]].
 unfold joint_update_expr_1111.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1112 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 814)).
Lemma joint_update_ready_1112 old :
 (exists ground bits, VM.find 814 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1112.
Proof.
 intros [g814 [b814 H814]].
 unfold joint_update_expr_1112.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1113 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 815)).
Lemma joint_update_ready_1113 old :
 (exists ground bits, VM.find 815 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1113.
Proof.
 intros [g815 [b815 H815]].
 unfold joint_update_expr_1113.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1114 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 816)).
Lemma joint_update_ready_1114 old :
 (exists ground bits, VM.find 816 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1114.
Proof.
 intros [g816 [b816 H816]].
 unfold joint_update_expr_1114.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1115 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 817)).
Lemma joint_update_ready_1115 old :
 (exists ground bits, VM.find 817 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1115.
Proof.
 intros [g817 [b817 H817]].
 unfold joint_update_expr_1115.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1116 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 818)).
Lemma joint_update_ready_1116 old :
 (exists ground bits, VM.find 818 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1116.
Proof.
 intros [g818 [b818 H818]].
 unfold joint_update_expr_1116.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1162 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1151))).
Lemma joint_update_ready_1162 old :
 (exists ground bits, VM.find 1151 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1162.
Proof.
 intros [g1151 [b1151 H1151]].
 unfold joint_update_expr_1162.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1163 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Lemma joint_update_ready_1163 old :
 (exists ground bits, VM.find 1152 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1163.
Proof.
 intros [g1152 [b1152 H1152]].
 unfold joint_update_expr_1163.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1164 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1162)) (@Eref VarOrder.T (@Eid VarOrder.T 1163))).
Lemma joint_update_ready_1164 old :
 (exists ground bits, VM.find 1162 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1163 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1164.
Proof.
 intros [g1162 [b1162 H1162]].
 intros [g1163 [b1163 H1163]].
 unfold joint_update_expr_1164.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1165 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1161))).
Lemma joint_update_ready_1165 old :
 (exists ground bits, VM.find 1161 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1165.
Proof.
 intros [g1161 [b1161 H1161]].
 unfold joint_update_expr_1165.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1166 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 1153))).
Lemma joint_update_ready_1166 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1166.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1166.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1167 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Lemma joint_update_ready_1167 old :
 (exists ground bits, VM.find 1152 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1167.
Proof.
 intros [g1152 [b1152 H1152]].
 unfold joint_update_expr_1167.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1168 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1151))).
Lemma joint_update_ready_1168 old :
 (exists ground bits, VM.find 1151 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1168.
Proof.
 intros [g1151 [b1151 H1151]].
 unfold joint_update_expr_1168.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1169 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1166)) (@Eref VarOrder.T (@Eid VarOrder.T 1167)) (@Eref VarOrder.T (@Eid VarOrder.T 1168))).
Lemma joint_update_ready_1169 old :
 (exists ground bits, VM.find 1166 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1167 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1168 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1169.
Proof.
 intros [g1166 [b1166 H1166]].
 intros [g1167 [b1167 H1167]].
 intros [g1168 [b1168 H1168]].
 unfold joint_update_expr_1169.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1170 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1164)) (@Eref VarOrder.T (@Eid VarOrder.T 1165)) (@Eref VarOrder.T (@Eid VarOrder.T 1169))).
Lemma joint_update_ready_1170 old :
 (exists ground bits, VM.find 1164 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1165 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1169 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1170.
Proof.
 intros [g1164 [b1164 H1164]].
 intros [g1165 [b1165 H1165]].
 intros [g1169 [b1169 H1169]].
 unfold joint_update_expr_1170.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1171 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 4 0) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Lemma joint_update_ready_1171 old :
 (exists ground bits, VM.find 1152 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1171.
Proof.
 intros [g1152 [b1152 H1152]].
 unfold joint_update_expr_1171.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1172 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 1153))).
Lemma joint_update_ready_1172 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1172.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1172.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1173 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 16) (@Econst VarOrder.T (Fuint 16) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_1173 old :
 concrete_expression_ready old joint_update_expr_1173.
Proof.
 unfold joint_update_expr_1173.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1174 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1173))).
Lemma joint_update_ready_1174 old :
 (exists ground bits, VM.find 1173 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1174.
Proof.
 intros [g1173 [b1173 H1173]].
 unfold joint_update_expr_1174.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1175 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 16) (@Eref VarOrder.T (@Eid VarOrder.T 1151))).
Lemma joint_update_ready_1175 old :
 (exists ground bits, VM.find 1151 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1175.
Proof.
 intros [g1151 [b1151 H1151]].
 unfold joint_update_expr_1175.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1176 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1175)) (@Eref VarOrder.T (@Eid VarOrder.T 1174))).
Lemma joint_update_ready_1176 old :
 (exists ground bits, VM.find 1174 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1175 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1176.
Proof.
 intros [g1174 [b1174 H1174]].
 intros [g1175 [b1175 H1175]].
 unfold joint_update_expr_1176.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1177 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 1151))).
Lemma joint_update_ready_1177 old :
 (exists ground bits, VM.find 1151 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1177.
Proof.
 intros [g1151 [b1151 H1151]].
 unfold joint_update_expr_1177.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1178 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 16) (@Eref VarOrder.T (@Eid VarOrder.T 1177))).
Lemma joint_update_ready_1178 old :
 (exists ground bits, VM.find 1177 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1178.
Proof.
 intros [g1177 [b1177 H1177]].
 unfold joint_update_expr_1178.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1179 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1174))).
Lemma joint_update_ready_1179 old :
 (exists ground bits, VM.find 1174 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1179.
Proof.
 intros [g1174 [b1174 H1174]].
 unfold joint_update_expr_1179.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1180 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1178)) (@Eref VarOrder.T (@Eid VarOrder.T 1179))).
Lemma joint_update_ready_1180 old :
 (exists ground bits, VM.find 1178 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1179 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1180.
Proof.
 intros [g1178 [b1178 H1178]].
 intros [g1179 [b1179 H1179]].
 unfold joint_update_expr_1180.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1181 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1176)) (@Eref VarOrder.T (@Eid VarOrder.T 1180))).
Lemma joint_update_ready_1181 old :
 (exists ground bits, VM.find 1176 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1180 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1181.
Proof.
 intros [g1176 [b1176 H1176]].
 intros [g1180 [b1180 H1180]].
 unfold joint_update_expr_1181.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1182 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 23 0) (@Eref VarOrder.T (@Eid VarOrder.T 1174))).
Lemma joint_update_ready_1182 old :
 (exists ground bits, VM.find 1174 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1182.
Proof.
 intros [g1174 [b1174 H1174]].
 unfold joint_update_expr_1182.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1183 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 8) (@Eref VarOrder.T (@Eid VarOrder.T 1182))).
Lemma joint_update_ready_1183 old :
 (exists ground bits, VM.find 1182 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1183.
Proof.
 intros [g1182 [b1182 H1182]].
 unfold joint_update_expr_1183.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1184 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1174)) (@Eref VarOrder.T (@Eid VarOrder.T 1183))).
Lemma joint_update_ready_1184 old :
 (exists ground bits, VM.find 1174 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1183 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1184.
Proof.
 intros [g1174 [b1174 H1174]].
 intros [g1183 [b1183 H1183]].
 unfold joint_update_expr_1184.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1185 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 8) (@Eref VarOrder.T (@Eid VarOrder.T 1181))).
Lemma joint_update_ready_1185 old :
 (exists ground bits, VM.find 1181 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1185.
Proof.
 intros [g1181 [b1181 H1181]].
 unfold joint_update_expr_1185.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1186 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1185)) (@Eref VarOrder.T (@Eid VarOrder.T 1184))).
Lemma joint_update_ready_1186 old :
 (exists ground bits, VM.find 1184 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1185 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1186.
Proof.
 intros [g1184 [b1184 H1184]].
 intros [g1185 [b1185 H1185]].
 unfold joint_update_expr_1186.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1187 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 23 0) (@Eref VarOrder.T (@Eid VarOrder.T 1181))).
Lemma joint_update_ready_1187 old :
 (exists ground bits, VM.find 1181 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1187.
Proof.
 intros [g1181 [b1181 H1181]].
 unfold joint_update_expr_1187.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1188 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 8) (@Eref VarOrder.T (@Eid VarOrder.T 1187))).
Lemma joint_update_ready_1188 old :
 (exists ground bits, VM.find 1187 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1188.
Proof.
 intros [g1187 [b1187 H1187]].
 unfold joint_update_expr_1188.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1189 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1184))).
Lemma joint_update_ready_1189 old :
 (exists ground bits, VM.find 1184 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1189.
Proof.
 intros [g1184 [b1184 H1184]].
 unfold joint_update_expr_1189.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1190 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1188)) (@Eref VarOrder.T (@Eid VarOrder.T 1189))).
Lemma joint_update_ready_1190 old :
 (exists ground bits, VM.find 1188 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1189 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1190.
Proof.
 intros [g1188 [b1188 H1188]].
 intros [g1189 [b1189 H1189]].
 unfold joint_update_expr_1190.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1191 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1186)) (@Eref VarOrder.T (@Eid VarOrder.T 1190))).
Lemma joint_update_ready_1191 old :
 (exists ground bits, VM.find 1186 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1190 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1191.
Proof.
 intros [g1186 [b1186 H1186]].
 intros [g1190 [b1190 H1190]].
 unfold joint_update_expr_1191.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1192 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 27 0) (@Eref VarOrder.T (@Eid VarOrder.T 1184))).
Lemma joint_update_ready_1192 old :
 (exists ground bits, VM.find 1184 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1192.
Proof.
 intros [g1184 [b1184 H1184]].
 unfold joint_update_expr_1192.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1193 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 4) (@Eref VarOrder.T (@Eid VarOrder.T 1192))).
Lemma joint_update_ready_1193 old :
 (exists ground bits, VM.find 1192 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1193.
Proof.
 intros [g1192 [b1192 H1192]].
 unfold joint_update_expr_1193.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1194 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1184)) (@Eref VarOrder.T (@Eid VarOrder.T 1193))).
Lemma joint_update_ready_1194 old :
 (exists ground bits, VM.find 1184 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1193 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1194.
Proof.
 intros [g1184 [b1184 H1184]].
 intros [g1193 [b1193 H1193]].
 unfold joint_update_expr_1194.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1195 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 4) (@Eref VarOrder.T (@Eid VarOrder.T 1191))).
Lemma joint_update_ready_1195 old :
 (exists ground bits, VM.find 1191 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1195.
Proof.
 intros [g1191 [b1191 H1191]].
 unfold joint_update_expr_1195.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1196 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1195)) (@Eref VarOrder.T (@Eid VarOrder.T 1194))).
Lemma joint_update_ready_1196 old :
 (exists ground bits, VM.find 1194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1195 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1196.
Proof.
 intros [g1194 [b1194 H1194]].
 intros [g1195 [b1195 H1195]].
 unfold joint_update_expr_1196.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1197 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 27 0) (@Eref VarOrder.T (@Eid VarOrder.T 1191))).
Lemma joint_update_ready_1197 old :
 (exists ground bits, VM.find 1191 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1197.
Proof.
 intros [g1191 [b1191 H1191]].
 unfold joint_update_expr_1197.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1198 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 4) (@Eref VarOrder.T (@Eid VarOrder.T 1197))).
Lemma joint_update_ready_1198 old :
 (exists ground bits, VM.find 1197 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1198.
Proof.
 intros [g1197 [b1197 H1197]].
 unfold joint_update_expr_1198.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1199 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1194))).
Lemma joint_update_ready_1199 old :
 (exists ground bits, VM.find 1194 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1199.
Proof.
 intros [g1194 [b1194 H1194]].
 unfold joint_update_expr_1199.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1200 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1198)) (@Eref VarOrder.T (@Eid VarOrder.T 1199))).
Lemma joint_update_ready_1200 old :
 (exists ground bits, VM.find 1198 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1199 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1200.
Proof.
 intros [g1198 [b1198 H1198]].
 intros [g1199 [b1199 H1199]].
 unfold joint_update_expr_1200.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1201 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1196)) (@Eref VarOrder.T (@Eid VarOrder.T 1200))).
Lemma joint_update_ready_1201 old :
 (exists ground bits, VM.find 1196 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1200 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1201.
Proof.
 intros [g1196 [b1196 H1196]].
 intros [g1200 [b1200 H1200]].
 unfold joint_update_expr_1201.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1202 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 29 0) (@Eref VarOrder.T (@Eid VarOrder.T 1194))).
Lemma joint_update_ready_1202 old :
 (exists ground bits, VM.find 1194 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1202.
Proof.
 intros [g1194 [b1194 H1194]].
 unfold joint_update_expr_1202.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1203 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 2) (@Eref VarOrder.T (@Eid VarOrder.T 1202))).
Lemma joint_update_ready_1203 old :
 (exists ground bits, VM.find 1202 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1203.
Proof.
 intros [g1202 [b1202 H1202]].
 unfold joint_update_expr_1203.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1204 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1194)) (@Eref VarOrder.T (@Eid VarOrder.T 1203))).
Lemma joint_update_ready_1204 old :
 (exists ground bits, VM.find 1194 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1203 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1204.
Proof.
 intros [g1194 [b1194 H1194]].
 intros [g1203 [b1203 H1203]].
 unfold joint_update_expr_1204.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1205 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 2) (@Eref VarOrder.T (@Eid VarOrder.T 1201))).
Lemma joint_update_ready_1205 old :
 (exists ground bits, VM.find 1201 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1205.
Proof.
 intros [g1201 [b1201 H1201]].
 unfold joint_update_expr_1205.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1206 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1205)) (@Eref VarOrder.T (@Eid VarOrder.T 1204))).
Lemma joint_update_ready_1206 old :
 (exists ground bits, VM.find 1204 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1205 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1206.
Proof.
 intros [g1204 [b1204 H1204]].
 intros [g1205 [b1205 H1205]].
 unfold joint_update_expr_1206.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1207 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 29 0) (@Eref VarOrder.T (@Eid VarOrder.T 1201))).
Lemma joint_update_ready_1207 old :
 (exists ground bits, VM.find 1201 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1207.
Proof.
 intros [g1201 [b1201 H1201]].
 unfold joint_update_expr_1207.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1208 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 2) (@Eref VarOrder.T (@Eid VarOrder.T 1207))).
Lemma joint_update_ready_1208 old :
 (exists ground bits, VM.find 1207 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1208.
Proof.
 intros [g1207 [b1207 H1207]].
 unfold joint_update_expr_1208.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1209 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1204))).
Lemma joint_update_ready_1209 old :
 (exists ground bits, VM.find 1204 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1209.
Proof.
 intros [g1204 [b1204 H1204]].
 unfold joint_update_expr_1209.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1210 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1208)) (@Eref VarOrder.T (@Eid VarOrder.T 1209))).
Lemma joint_update_ready_1210 old :
 (exists ground bits, VM.find 1208 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1209 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1210.
Proof.
 intros [g1208 [b1208 H1208]].
 intros [g1209 [b1209 H1209]].
 unfold joint_update_expr_1210.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1211 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1206)) (@Eref VarOrder.T (@Eid VarOrder.T 1210))).
Lemma joint_update_ready_1211 old :
 (exists ground bits, VM.find 1206 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1210 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1211.
Proof.
 intros [g1206 [b1206 H1206]].
 intros [g1210 [b1210 H1210]].
 unfold joint_update_expr_1211.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1212 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 30 0) (@Eref VarOrder.T (@Eid VarOrder.T 1204))).
Lemma joint_update_ready_1212 old :
 (exists ground bits, VM.find 1204 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1212.
Proof.
 intros [g1204 [b1204 H1204]].
 unfold joint_update_expr_1212.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1213 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 1) (@Eref VarOrder.T (@Eid VarOrder.T 1212))).
Lemma joint_update_ready_1213 old :
 (exists ground bits, VM.find 1212 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1213.
Proof.
 intros [g1212 [b1212 H1212]].
 unfold joint_update_expr_1213.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1214 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1204)) (@Eref VarOrder.T (@Eid VarOrder.T 1213))).
Lemma joint_update_ready_1214 old :
 (exists ground bits, VM.find 1204 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1213 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1214.
Proof.
 intros [g1204 [b1204 H1204]].
 intros [g1213 [b1213 H1213]].
 unfold joint_update_expr_1214.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1215 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 1) (@Eref VarOrder.T (@Eid VarOrder.T 1211))).
Lemma joint_update_ready_1215 old :
 (exists ground bits, VM.find 1211 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1215.
Proof.
 intros [g1211 [b1211 H1211]].
 unfold joint_update_expr_1215.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1216 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1215)) (@Eref VarOrder.T (@Eid VarOrder.T 1214))).
Lemma joint_update_ready_1216 old :
 (exists ground bits, VM.find 1214 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1215 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1216.
Proof.
 intros [g1214 [b1214 H1214]].
 intros [g1215 [b1215 H1215]].
 unfold joint_update_expr_1216.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1217 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 30 0) (@Eref VarOrder.T (@Eid VarOrder.T 1211))).
Lemma joint_update_ready_1217 old :
 (exists ground bits, VM.find 1211 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1217.
Proof.
 intros [g1211 [b1211 H1211]].
 unfold joint_update_expr_1217.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1218 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 1) (@Eref VarOrder.T (@Eid VarOrder.T 1217))).
Lemma joint_update_ready_1218 old :
 (exists ground bits, VM.find 1217 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1218.
Proof.
 intros [g1217 [b1217 H1217]].
 unfold joint_update_expr_1218.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1219 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1214))).
Lemma joint_update_ready_1219 old :
 (exists ground bits, VM.find 1214 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1219.
Proof.
 intros [g1214 [b1214 H1214]].
 unfold joint_update_expr_1219.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1220 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1218)) (@Eref VarOrder.T (@Eid VarOrder.T 1219))).
Lemma joint_update_ready_1220 old :
 (exists ground bits, VM.find 1218 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1219 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1220.
Proof.
 intros [g1218 [b1218 H1218]].
 intros [g1219 [b1219 H1219]].
 unfold joint_update_expr_1220.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1221 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1216)) (@Eref VarOrder.T (@Eid VarOrder.T 1220))).
Lemma joint_update_ready_1221 old :
 (exists ground bits, VM.find 1216 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1220 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1221.
Proof.
 intros [g1216 [b1216 H1216]].
 intros [g1220 [b1220 H1220]].
 unfold joint_update_expr_1221.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1222 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1172)) (@Eref VarOrder.T (@Eid VarOrder.T 1151)) (@Eref VarOrder.T (@Eid VarOrder.T 1221))).
Lemma joint_update_ready_1222 old :
 (exists ground bits, VM.find 1151 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1172 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1221 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1222.
Proof.
 intros [g1151 [b1151 H1151]].
 intros [g1172 [b1172 H1172]].
 intros [g1221 [b1221 H1221]].
 unfold joint_update_expr_1222.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1223 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1153))).
Lemma joint_update_ready_1223 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1223.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1223.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1224 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1222))).
Lemma joint_update_ready_1224 old :
 (exists ground bits, VM.find 1222 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1224.
Proof.
 intros [g1222 [b1222 H1222]].
 unfold joint_update_expr_1224.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1225 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1223)) (@Eref VarOrder.T (@Eid VarOrder.T 1224))).
Lemma joint_update_ready_1225 old :
 (exists ground bits, VM.find 1223 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1224 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1225.
Proof.
 intros [g1223 [b1223 H1223]].
 intros [g1224 [b1224 H1224]].
 unfold joint_update_expr_1225.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1226 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 1225)) (@Eref VarOrder.T (@Eid VarOrder.T 1222))).
Lemma joint_update_ready_1226 old :
 (exists ground bits, VM.find 1222 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1225 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1226.
Proof.
 intros [g1222 [b1222 H1222]].
 intros [g1225 [b1225 H1225]].
 unfold joint_update_expr_1226.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1227 : hfexpr VarOrder.T := (@Ecast VarOrder.T AsSInt (@Eref VarOrder.T (@Eid VarOrder.T 1226))).
Lemma joint_update_ready_1227 old :
 (exists ground bits, VM.find 1226 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1227.
Proof.
 intros [g1226 [b1226 H1226]].
 unfold joint_update_expr_1227.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1228 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 1227)) (@Eref VarOrder.T (@Eid VarOrder.T 1171))).
Lemma joint_update_ready_1228 old :
 (exists ground bits, VM.find 1171 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1227 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1228.
Proof.
 intros [g1171 [b1171 H1171]].
 intros [g1227 [b1227 H1227]].
 unfold joint_update_expr_1228.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1229 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 1228))).
Lemma joint_update_ready_1229 old :
 (exists ground bits, VM.find 1228 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1229.
Proof.
 intros [g1228 [b1228 H1228]].
 unfold joint_update_expr_1229.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1230 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 16) (@Econst VarOrder.T (Fuint 16) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma joint_update_ready_1230 old :
 concrete_expression_ready old joint_update_expr_1230.
Proof.
 unfold joint_update_expr_1230.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1231 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Econst VarOrder.T (Fuint 32) [::true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 1230))).
Lemma joint_update_ready_1231 old :
 (exists ground bits, VM.find 1230 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1231.
Proof.
 intros [g1230 [b1230 H1230]].
 unfold joint_update_expr_1231.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1232 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 16) (@Eref VarOrder.T (@Eid VarOrder.T 1229))).
Lemma joint_update_ready_1232 old :
 (exists ground bits, VM.find 1229 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1232.
Proof.
 intros [g1229 [b1229 H1229]].
 unfold joint_update_expr_1232.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1233 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1232)) (@Eref VarOrder.T (@Eid VarOrder.T 1231))).
Lemma joint_update_ready_1233 old :
 (exists ground bits, VM.find 1231 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1232 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1233.
Proof.
 intros [g1231 [b1231 H1231]].
 intros [g1232 [b1232 H1232]].
 unfold joint_update_expr_1233.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1234 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 1229))).
Lemma joint_update_ready_1234 old :
 (exists ground bits, VM.find 1229 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1234.
Proof.
 intros [g1229 [b1229 H1229]].
 unfold joint_update_expr_1234.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1235 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 16) (@Eref VarOrder.T (@Eid VarOrder.T 1234))).
Lemma joint_update_ready_1235 old :
 (exists ground bits, VM.find 1234 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1235.
Proof.
 intros [g1234 [b1234 H1234]].
 unfold joint_update_expr_1235.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1236 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1231))).
Lemma joint_update_ready_1236 old :
 (exists ground bits, VM.find 1231 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1236.
Proof.
 intros [g1231 [b1231 H1231]].
 unfold joint_update_expr_1236.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1237 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1235)) (@Eref VarOrder.T (@Eid VarOrder.T 1236))).
Lemma joint_update_ready_1237 old :
 (exists ground bits, VM.find 1235 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1236 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1237.
Proof.
 intros [g1235 [b1235 H1235]].
 intros [g1236 [b1236 H1236]].
 unfold joint_update_expr_1237.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1238 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1233)) (@Eref VarOrder.T (@Eid VarOrder.T 1237))).
Lemma joint_update_ready_1238 old :
 (exists ground bits, VM.find 1233 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1237 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1238.
Proof.
 intros [g1233 [b1233 H1233]].
 intros [g1237 [b1237 H1237]].
 unfold joint_update_expr_1238.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1239 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 23 0) (@Eref VarOrder.T (@Eid VarOrder.T 1231))).
Lemma joint_update_ready_1239 old :
 (exists ground bits, VM.find 1231 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1239.
Proof.
 intros [g1231 [b1231 H1231]].
 unfold joint_update_expr_1239.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1240 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 8) (@Eref VarOrder.T (@Eid VarOrder.T 1239))).
Lemma joint_update_ready_1240 old :
 (exists ground bits, VM.find 1239 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1240.
Proof.
 intros [g1239 [b1239 H1239]].
 unfold joint_update_expr_1240.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1241 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1231)) (@Eref VarOrder.T (@Eid VarOrder.T 1240))).
Lemma joint_update_ready_1241 old :
 (exists ground bits, VM.find 1231 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1240 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1241.
Proof.
 intros [g1231 [b1231 H1231]].
 intros [g1240 [b1240 H1240]].
 unfold joint_update_expr_1241.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1242 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 8) (@Eref VarOrder.T (@Eid VarOrder.T 1238))).
Lemma joint_update_ready_1242 old :
 (exists ground bits, VM.find 1238 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1242.
Proof.
 intros [g1238 [b1238 H1238]].
 unfold joint_update_expr_1242.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1243 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1242)) (@Eref VarOrder.T (@Eid VarOrder.T 1241))).
Lemma joint_update_ready_1243 old :
 (exists ground bits, VM.find 1241 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1242 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1243.
Proof.
 intros [g1241 [b1241 H1241]].
 intros [g1242 [b1242 H1242]].
 unfold joint_update_expr_1243.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1244 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 23 0) (@Eref VarOrder.T (@Eid VarOrder.T 1238))).
Lemma joint_update_ready_1244 old :
 (exists ground bits, VM.find 1238 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1244.
Proof.
 intros [g1238 [b1238 H1238]].
 unfold joint_update_expr_1244.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1245 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 8) (@Eref VarOrder.T (@Eid VarOrder.T 1244))).
Lemma joint_update_ready_1245 old :
 (exists ground bits, VM.find 1244 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1245.
Proof.
 intros [g1244 [b1244 H1244]].
 unfold joint_update_expr_1245.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1246 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1241))).
Lemma joint_update_ready_1246 old :
 (exists ground bits, VM.find 1241 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1246.
Proof.
 intros [g1241 [b1241 H1241]].
 unfold joint_update_expr_1246.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1247 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1245)) (@Eref VarOrder.T (@Eid VarOrder.T 1246))).
Lemma joint_update_ready_1247 old :
 (exists ground bits, VM.find 1245 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1246 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1247.
Proof.
 intros [g1245 [b1245 H1245]].
 intros [g1246 [b1246 H1246]].
 unfold joint_update_expr_1247.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1248 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1243)) (@Eref VarOrder.T (@Eid VarOrder.T 1247))).
Lemma joint_update_ready_1248 old :
 (exists ground bits, VM.find 1243 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1247 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1248.
Proof.
 intros [g1243 [b1243 H1243]].
 intros [g1247 [b1247 H1247]].
 unfold joint_update_expr_1248.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1249 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 27 0) (@Eref VarOrder.T (@Eid VarOrder.T 1241))).
Lemma joint_update_ready_1249 old :
 (exists ground bits, VM.find 1241 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1249.
Proof.
 intros [g1241 [b1241 H1241]].
 unfold joint_update_expr_1249.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1250 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 4) (@Eref VarOrder.T (@Eid VarOrder.T 1249))).
Lemma joint_update_ready_1250 old :
 (exists ground bits, VM.find 1249 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1250.
Proof.
 intros [g1249 [b1249 H1249]].
 unfold joint_update_expr_1250.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1251 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1241)) (@Eref VarOrder.T (@Eid VarOrder.T 1250))).
Lemma joint_update_ready_1251 old :
 (exists ground bits, VM.find 1241 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1250 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1251.
Proof.
 intros [g1241 [b1241 H1241]].
 intros [g1250 [b1250 H1250]].
 unfold joint_update_expr_1251.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1252 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 4) (@Eref VarOrder.T (@Eid VarOrder.T 1248))).
Lemma joint_update_ready_1252 old :
 (exists ground bits, VM.find 1248 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1252.
Proof.
 intros [g1248 [b1248 H1248]].
 unfold joint_update_expr_1252.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1253 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1252)) (@Eref VarOrder.T (@Eid VarOrder.T 1251))).
Lemma joint_update_ready_1253 old :
 (exists ground bits, VM.find 1251 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1252 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1253.
Proof.
 intros [g1251 [b1251 H1251]].
 intros [g1252 [b1252 H1252]].
 unfold joint_update_expr_1253.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1254 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 27 0) (@Eref VarOrder.T (@Eid VarOrder.T 1248))).
Lemma joint_update_ready_1254 old :
 (exists ground bits, VM.find 1248 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1254.
Proof.
 intros [g1248 [b1248 H1248]].
 unfold joint_update_expr_1254.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1255 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 4) (@Eref VarOrder.T (@Eid VarOrder.T 1254))).
Lemma joint_update_ready_1255 old :
 (exists ground bits, VM.find 1254 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1255.
Proof.
 intros [g1254 [b1254 H1254]].
 unfold joint_update_expr_1255.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1256 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1251))).
Lemma joint_update_ready_1256 old :
 (exists ground bits, VM.find 1251 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1256.
Proof.
 intros [g1251 [b1251 H1251]].
 unfold joint_update_expr_1256.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1257 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1255)) (@Eref VarOrder.T (@Eid VarOrder.T 1256))).
Lemma joint_update_ready_1257 old :
 (exists ground bits, VM.find 1255 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1256 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1257.
Proof.
 intros [g1255 [b1255 H1255]].
 intros [g1256 [b1256 H1256]].
 unfold joint_update_expr_1257.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1258 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1253)) (@Eref VarOrder.T (@Eid VarOrder.T 1257))).
Lemma joint_update_ready_1258 old :
 (exists ground bits, VM.find 1253 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1257 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1258.
Proof.
 intros [g1253 [b1253 H1253]].
 intros [g1257 [b1257 H1257]].
 unfold joint_update_expr_1258.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1259 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 29 0) (@Eref VarOrder.T (@Eid VarOrder.T 1251))).
Lemma joint_update_ready_1259 old :
 (exists ground bits, VM.find 1251 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1259.
Proof.
 intros [g1251 [b1251 H1251]].
 unfold joint_update_expr_1259.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1260 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 2) (@Eref VarOrder.T (@Eid VarOrder.T 1259))).
Lemma joint_update_ready_1260 old :
 (exists ground bits, VM.find 1259 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1260.
Proof.
 intros [g1259 [b1259 H1259]].
 unfold joint_update_expr_1260.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1261 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1251)) (@Eref VarOrder.T (@Eid VarOrder.T 1260))).
Lemma joint_update_ready_1261 old :
 (exists ground bits, VM.find 1251 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1260 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1261.
Proof.
 intros [g1251 [b1251 H1251]].
 intros [g1260 [b1260 H1260]].
 unfold joint_update_expr_1261.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1262 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 2) (@Eref VarOrder.T (@Eid VarOrder.T 1258))).
Lemma joint_update_ready_1262 old :
 (exists ground bits, VM.find 1258 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1262.
Proof.
 intros [g1258 [b1258 H1258]].
 unfold joint_update_expr_1262.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1263 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1262)) (@Eref VarOrder.T (@Eid VarOrder.T 1261))).
Lemma joint_update_ready_1263 old :
 (exists ground bits, VM.find 1261 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1262 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1263.
Proof.
 intros [g1261 [b1261 H1261]].
 intros [g1262 [b1262 H1262]].
 unfold joint_update_expr_1263.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1264 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 29 0) (@Eref VarOrder.T (@Eid VarOrder.T 1258))).
Lemma joint_update_ready_1264 old :
 (exists ground bits, VM.find 1258 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1264.
Proof.
 intros [g1258 [b1258 H1258]].
 unfold joint_update_expr_1264.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1265 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 2) (@Eref VarOrder.T (@Eid VarOrder.T 1264))).
Lemma joint_update_ready_1265 old :
 (exists ground bits, VM.find 1264 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1265.
Proof.
 intros [g1264 [b1264 H1264]].
 unfold joint_update_expr_1265.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1266 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1261))).
Lemma joint_update_ready_1266 old :
 (exists ground bits, VM.find 1261 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1266.
Proof.
 intros [g1261 [b1261 H1261]].
 unfold joint_update_expr_1266.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1267 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1265)) (@Eref VarOrder.T (@Eid VarOrder.T 1266))).
Lemma joint_update_ready_1267 old :
 (exists ground bits, VM.find 1265 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1266 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1267.
Proof.
 intros [g1265 [b1265 H1265]].
 intros [g1266 [b1266 H1266]].
 unfold joint_update_expr_1267.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1268 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1263)) (@Eref VarOrder.T (@Eid VarOrder.T 1267))).
Lemma joint_update_ready_1268 old :
 (exists ground bits, VM.find 1263 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1267 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1268.
Proof.
 intros [g1263 [b1263 H1263]].
 intros [g1267 [b1267 H1267]].
 unfold joint_update_expr_1268.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1269 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 30 0) (@Eref VarOrder.T (@Eid VarOrder.T 1261))).
Lemma joint_update_ready_1269 old :
 (exists ground bits, VM.find 1261 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1269.
Proof.
 intros [g1261 [b1261 H1261]].
 unfold joint_update_expr_1269.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1270 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 1) (@Eref VarOrder.T (@Eid VarOrder.T 1269))).
Lemma joint_update_ready_1270 old :
 (exists ground bits, VM.find 1269 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1270.
Proof.
 intros [g1269 [b1269 H1269]].
 unfold joint_update_expr_1270.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1271 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1261)) (@Eref VarOrder.T (@Eid VarOrder.T 1270))).
Lemma joint_update_ready_1271 old :
 (exists ground bits, VM.find 1261 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1270 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1271.
Proof.
 intros [g1261 [b1261 H1261]].
 intros [g1270 [b1270 H1270]].
 unfold joint_update_expr_1271.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1272 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushr 1) (@Eref VarOrder.T (@Eid VarOrder.T 1268))).
Lemma joint_update_ready_1272 old :
 (exists ground bits, VM.find 1268 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1272.
Proof.
 intros [g1268 [b1268 H1268]].
 unfold joint_update_expr_1272.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1273 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1272)) (@Eref VarOrder.T (@Eid VarOrder.T 1271))).
Lemma joint_update_ready_1273 old :
 (exists ground bits, VM.find 1271 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1272 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1273.
Proof.
 intros [g1271 [b1271 H1271]].
 intros [g1272 [b1272 H1272]].
 unfold joint_update_expr_1273.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1274 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 30 0) (@Eref VarOrder.T (@Eid VarOrder.T 1268))).
Lemma joint_update_ready_1274 old :
 (exists ground bits, VM.find 1268 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1274.
Proof.
 intros [g1268 [b1268 H1268]].
 unfold joint_update_expr_1274.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1275 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Ushl 1) (@Eref VarOrder.T (@Eid VarOrder.T 1274))).
Lemma joint_update_ready_1275 old :
 (exists ground bits, VM.find 1274 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1275.
Proof.
 intros [g1274 [b1274 H1274]].
 unfold joint_update_expr_1275.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1276 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Unot (@Eref VarOrder.T (@Eid VarOrder.T 1271))).
Lemma joint_update_ready_1276 old :
 (exists ground bits, VM.find 1271 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1276.
Proof.
 intros [g1271 [b1271 H1271]].
 unfold joint_update_expr_1276.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1277 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1275)) (@Eref VarOrder.T (@Eid VarOrder.T 1276))).
Lemma joint_update_ready_1277 old :
 (exists ground bits, VM.find 1275 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1276 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1277.
Proof.
 intros [g1275 [b1275 H1275]].
 intros [g1276 [b1276 H1276]].
 unfold joint_update_expr_1277.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1278 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1273)) (@Eref VarOrder.T (@Eid VarOrder.T 1277))).
Lemma joint_update_ready_1278 old :
 (exists ground bits, VM.find 1273 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1277 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1278.
Proof.
 intros [g1273 [b1273 H1273]].
 intros [g1277 [b1277 H1277]].
 unfold joint_update_expr_1278.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1279 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; false])).
Lemma joint_update_ready_1279 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1279.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1279.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1280 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::true; false; false; false])).
Lemma joint_update_ready_1280 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1280.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1280.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1281 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1279)) (@Eref VarOrder.T (@Eid VarOrder.T 1280))).
Lemma joint_update_ready_1281 old :
 (exists ground bits, VM.find 1279 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1280 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1281.
Proof.
 intros [g1279 [b1279 H1279]].
 intros [g1280 [b1280 H1280]].
 unfold joint_update_expr_1281.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1282 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::true; false; true; false])).
Lemma joint_update_ready_1282 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1282.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1282.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1283 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::true; true; true; false])).
Lemma joint_update_ready_1283 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1283.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1283.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1284 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1282)) (@Eref VarOrder.T (@Eid VarOrder.T 1283))).
Lemma joint_update_ready_1284 old :
 (exists ground bits, VM.find 1282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1283 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1284.
Proof.
 intros [g1282 [b1282 H1282]].
 intros [g1283 [b1283 H1283]].
 unfold joint_update_expr_1284.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1285 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::true; false; false; true])).
Lemma joint_update_ready_1285 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1285.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1285.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1286 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true])).
Lemma joint_update_ready_1286 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1286.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1286.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1287 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1285)) (@Eref VarOrder.T (@Eid VarOrder.T 1286))).
Lemma joint_update_ready_1287 old :
 (exists ground bits, VM.find 1285 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1286 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1287.
Proof.
 intros [g1285 [b1285 H1285]].
 intros [g1286 [b1286 H1286]].
 unfold joint_update_expr_1287.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1288 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::false; true; true; false])).
Lemma joint_update_ready_1288 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1288.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1288.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1289 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::false; true; false; false])).
Lemma joint_update_ready_1289 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1289.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1289.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1290 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1151)) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Lemma joint_update_ready_1290 old :
 (exists ground bits, VM.find 1151 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1152 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1290.
Proof.
 intros [g1151 [b1151 H1151]].
 intros [g1152 [b1152 H1152]].
 unfold joint_update_expr_1290.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1291 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::true; true; false; false])).
Lemma joint_update_ready_1291 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1291.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1291.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1292 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1151)) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Lemma joint_update_ready_1292 old :
 (exists ground bits, VM.find 1151 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1152 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1292.
Proof.
 intros [g1151 [b1151 H1151]].
 intros [g1152 [b1152 H1152]].
 unfold joint_update_expr_1292.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1293 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::false; false; true; false])).
Lemma joint_update_ready_1293 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1293.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1293.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1294 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1151)) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Lemma joint_update_ready_1294 old :
 (exists ground bits, VM.find 1151 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1152 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1294.
Proof.
 intros [g1151 [b1151 H1151]].
 intros [g1152 [b1152 H1152]].
 unfold joint_update_expr_1294.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1295 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1153)) (@Econst VarOrder.T (Fuint 4) [::false; true; false; true])).
Lemma joint_update_ready_1295 old :
 (exists ground bits, VM.find 1153 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1295.
Proof.
 intros [g1153 [b1153 H1153]].
 unfold joint_update_expr_1295.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1296 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1295)) (@Eref VarOrder.T (@Eid VarOrder.T 1151)) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Lemma joint_update_ready_1296 old :
 (exists ground bits, VM.find 1151 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1152 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1295 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1296.
Proof.
 intros [g1151 [b1151 H1151]].
 intros [g1152 [b1152 H1152]].
 intros [g1295 [b1295 H1295]].
 unfold joint_update_expr_1296.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1297 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1293)) (@Eref VarOrder.T (@Eid VarOrder.T 1294)) (@Eref VarOrder.T (@Eid VarOrder.T 1296))).
Lemma joint_update_ready_1297 old :
 (exists ground bits, VM.find 1293 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1296 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1297.
Proof.
 intros [g1293 [b1293 H1293]].
 intros [g1294 [b1294 H1294]].
 intros [g1296 [b1296 H1296]].
 unfold joint_update_expr_1297.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1298 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1291)) (@Eref VarOrder.T (@Eid VarOrder.T 1292)) (@Eref VarOrder.T (@Eid VarOrder.T 1297))).
Lemma joint_update_ready_1298 old :
 (exists ground bits, VM.find 1291 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1297 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1298.
Proof.
 intros [g1291 [b1291 H1291]].
 intros [g1292 [b1292 H1292]].
 intros [g1297 [b1297 H1297]].
 unfold joint_update_expr_1298.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1299 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1289)) (@Eref VarOrder.T (@Eid VarOrder.T 1290)) (@Eref VarOrder.T (@Eid VarOrder.T 1298))).
Lemma joint_update_ready_1299 old :
 (exists ground bits, VM.find 1289 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1298 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1299.
Proof.
 intros [g1289 [b1289 H1289]].
 intros [g1290 [b1290 H1290]].
 intros [g1298 [b1298 H1298]].
 unfold joint_update_expr_1299.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1300 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1288)) (@Eref VarOrder.T (@Eid VarOrder.T 1278)) (@Eref VarOrder.T (@Eid VarOrder.T 1299))).
Lemma joint_update_ready_1300 old :
 (exists ground bits, VM.find 1278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1299 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1300.
Proof.
 intros [g1278 [b1278 H1278]].
 intros [g1288 [b1288 H1288]].
 intros [g1299 [b1299 H1299]].
 unfold joint_update_expr_1300.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1301 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1287)) (@Eref VarOrder.T (@Eid VarOrder.T 1229)) (@Eref VarOrder.T (@Eid VarOrder.T 1300))).
Lemma joint_update_ready_1301 old :
 (exists ground bits, VM.find 1229 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1287 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1300 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1301.
Proof.
 intros [g1229 [b1229 H1229]].
 intros [g1287 [b1287 H1287]].
 intros [g1300 [b1300 H1300]].
 unfold joint_update_expr_1301.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1302 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1284)) (@Eref VarOrder.T (@Eid VarOrder.T 1170)) (@Eref VarOrder.T (@Eid VarOrder.T 1301))).
Lemma joint_update_ready_1302 old :
 (exists ground bits, VM.find 1170 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1301 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1302.
Proof.
 intros [g1170 [b1170 H1170]].
 intros [g1284 [b1284 H1284]].
 intros [g1301 [b1301 H1301]].
 unfold joint_update_expr_1302.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1303 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1281)) (@Eref VarOrder.T (@Eid VarOrder.T 1161)) (@Eref VarOrder.T (@Eid VarOrder.T 1302))).
Lemma joint_update_ready_1303 old :
 (exists ground bits, VM.find 1161 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1281 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1302 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1303.
Proof.
 intros [g1161 [b1161 H1161]].
 intros [g1281 [b1281 H1281]].
 intros [g1302 [b1302 H1302]].
 unfold joint_update_expr_1303.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1361 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bsub (@Eref VarOrder.T (@Eid VarOrder.T 1357)) (@Eref VarOrder.T (@Eid VarOrder.T 1358))).
Lemma joint_update_ready_1361 old :
 (exists ground bits, VM.find 1357 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1358 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1361.
Proof.
 intros [g1357 [b1357 H1357]].
 intros [g1358 [b1358 H1358]].
 unfold joint_update_expr_1361.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1362 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 1361))).
Lemma joint_update_ready_1362 old :
 (exists ground bits, VM.find 1361 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1362.
Proof.
 intros [g1361 [b1361 H1361]].
 unfold joint_update_expr_1362.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1363 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 1362))).
Lemma joint_update_ready_1363 old :
 (exists ground bits, VM.find 1362 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1363.
Proof.
 intros [g1362 [b1362 H1362]].
 unfold joint_update_expr_1363.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1364 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1363)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_1364 old :
 (exists ground bits, VM.find 1363 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1364.
Proof.
 intros [g1363 [b1363 H1363]].
 unfold joint_update_expr_1364.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1365 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1357))).
Lemma joint_update_ready_1365 old :
 (exists ground bits, VM.find 1357 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1365.
Proof.
 intros [g1357 [b1357 H1357]].
 unfold joint_update_expr_1365.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1366 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1358))).
Lemma joint_update_ready_1366 old :
 (exists ground bits, VM.find 1358 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1366.
Proof.
 intros [g1358 [b1358 H1358]].
 unfold joint_update_expr_1366.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1367 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1365)) (@Eref VarOrder.T (@Eid VarOrder.T 1366))).
Lemma joint_update_ready_1367 old :
 (exists ground bits, VM.find 1365 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1366 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1367.
Proof.
 intros [g1365 [b1365 H1365]].
 intros [g1366 [b1366 H1366]].
 unfold joint_update_expr_1367.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1368 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1362))).
Lemma joint_update_ready_1368 old :
 (exists ground bits, VM.find 1362 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1368.
Proof.
 intros [g1362 [b1362 H1362]].
 unfold joint_update_expr_1368.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1369 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1357))).
Lemma joint_update_ready_1369 old :
 (exists ground bits, VM.find 1357 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1369.
Proof.
 intros [g1357 [b1357 H1357]].
 unfold joint_update_expr_1369.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1370 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1367)) (@Eref VarOrder.T (@Eid VarOrder.T 1368)) (@Eref VarOrder.T (@Eid VarOrder.T 1369))).
Lemma joint_update_ready_1370 old :
 (exists ground bits, VM.find 1367 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1368 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1369 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1370.
Proof.
 intros [g1367 [b1367 H1367]].
 intros [g1368 [b1368 H1368]].
 intros [g1369 [b1369 H1369]].
 unfold joint_update_expr_1370.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1371 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1362))).
Lemma joint_update_ready_1371 old :
 (exists ground bits, VM.find 1362 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1371.
Proof.
 intros [g1362 [b1362 H1362]].
 unfold joint_update_expr_1371.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1372 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 31) (@Eref VarOrder.T (@Eid VarOrder.T 1358))).
Lemma joint_update_ready_1372 old :
 (exists ground bits, VM.find 1358 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1372.
Proof.
 intros [g1358 [b1358 H1358]].
 unfold joint_update_expr_1372.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1373 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1367)) (@Eref VarOrder.T (@Eid VarOrder.T 1371)) (@Eref VarOrder.T (@Eid VarOrder.T 1372))).
Lemma joint_update_ready_1373 old :
 (exists ground bits, VM.find 1367 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1371 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1372 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1373.
Proof.
 intros [g1367 [b1367 H1367]].
 intros [g1371 [b1371 H1371]].
 intros [g1372 [b1372 H1372]].
 unfold joint_update_expr_1373.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1374 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1370)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_1374 old :
 (exists ground bits, VM.find 1370 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1374.
Proof.
 intros [g1370 [b1370 H1370]].
 unfold joint_update_expr_1374.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1375 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1373)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_1375 old :
 (exists ground bits, VM.find 1373 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1375.
Proof.
 intros [g1373 [b1373 H1373]].
 unfold joint_update_expr_1375.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1376 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1359)) (@Econst VarOrder.T (Fuint 3) [::true; true; false])).
Lemma joint_update_ready_1376 old :
 (exists ground bits, VM.find 1359 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1376.
Proof.
 intros [g1359 [b1359 H1359]].
 unfold joint_update_expr_1376.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1377 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1376)) (@Eref VarOrder.T (@Eid VarOrder.T 1364))).
Lemma joint_update_ready_1377 old :
 (exists ground bits, VM.find 1364 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1376 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1377.
Proof.
 intros [g1364 [b1364 H1364]].
 intros [g1376 [b1376 H1376]].
 unfold joint_update_expr_1377.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1378 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1359)) (@Econst VarOrder.T (Fuint 3) [::false; true; true])).
Lemma joint_update_ready_1378 old :
 (exists ground bits, VM.find 1359 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1378.
Proof.
 intros [g1359 [b1359 H1359]].
 unfold joint_update_expr_1378.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1379 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1378)) (@Eref VarOrder.T (@Eid VarOrder.T 1363))).
Lemma joint_update_ready_1379 old :
 (exists ground bits, VM.find 1363 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1378 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1379.
Proof.
 intros [g1363 [b1363 H1363]].
 intros [g1378 [b1378 H1378]].
 unfold joint_update_expr_1379.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1380 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1377)) (@Eref VarOrder.T (@Eid VarOrder.T 1379))).
Lemma joint_update_ready_1380 old :
 (exists ground bits, VM.find 1377 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1379 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1380.
Proof.
 intros [g1377 [b1377 H1377]].
 intros [g1379 [b1379 H1379]].
 unfold joint_update_expr_1380.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1381 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1359)) (@Econst VarOrder.T (Fuint 3) [::false; true; false])).
Lemma joint_update_ready_1381 old :
 (exists ground bits, VM.find 1359 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1381.
Proof.
 intros [g1359 [b1359 H1359]].
 unfold joint_update_expr_1381.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1382 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1381)) (@Eref VarOrder.T (@Eid VarOrder.T 1370))).
Lemma joint_update_ready_1382 old :
 (exists ground bits, VM.find 1370 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1381 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1382.
Proof.
 intros [g1370 [b1370 H1370]].
 intros [g1381 [b1381 H1381]].
 unfold joint_update_expr_1382.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1383 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1380)) (@Eref VarOrder.T (@Eid VarOrder.T 1382))).
Lemma joint_update_ready_1383 old :
 (exists ground bits, VM.find 1380 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1382 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1383.
Proof.
 intros [g1380 [b1380 H1380]].
 intros [g1382 [b1382 H1382]].
 unfold joint_update_expr_1383.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1384 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1359)) (@Econst VarOrder.T (Fuint 3) [::true; false; true])).
Lemma joint_update_ready_1384 old :
 (exists ground bits, VM.find 1359 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1384.
Proof.
 intros [g1359 [b1359 H1359]].
 unfold joint_update_expr_1384.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1385 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1384)) (@Eref VarOrder.T (@Eid VarOrder.T 1374))).
Lemma joint_update_ready_1385 old :
 (exists ground bits, VM.find 1374 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1384 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1385.
Proof.
 intros [g1374 [b1374 H1374]].
 intros [g1384 [b1384 H1384]].
 unfold joint_update_expr_1385.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1386 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1383)) (@Eref VarOrder.T (@Eid VarOrder.T 1385))).
Lemma joint_update_ready_1386 old :
 (exists ground bits, VM.find 1383 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1385 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1386.
Proof.
 intros [g1383 [b1383 H1383]].
 intros [g1385 [b1385 H1385]].
 unfold joint_update_expr_1386.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1387 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1359)) (@Econst VarOrder.T (Fuint 3) [::true; false; false])).
Lemma joint_update_ready_1387 old :
 (exists ground bits, VM.find 1359 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1387.
Proof.
 intros [g1359 [b1359 H1359]].
 unfold joint_update_expr_1387.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1388 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1387)) (@Eref VarOrder.T (@Eid VarOrder.T 1373))).
Lemma joint_update_ready_1388 old :
 (exists ground bits, VM.find 1373 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1387 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1388.
Proof.
 intros [g1373 [b1373 H1373]].
 intros [g1387 [b1387 H1387]].
 unfold joint_update_expr_1388.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1389 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1386)) (@Eref VarOrder.T (@Eid VarOrder.T 1388))).
Lemma joint_update_ready_1389 old :
 (exists ground bits, VM.find 1386 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1388 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1389.
Proof.
 intros [g1386 [b1386 H1386]].
 intros [g1388 [b1388 H1388]].
 unfold joint_update_expr_1389.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1390 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1359)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Lemma joint_update_ready_1390 old :
 (exists ground bits, VM.find 1359 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1390.
Proof.
 intros [g1359 [b1359 H1359]].
 unfold joint_update_expr_1390.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1391 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1390)) (@Eref VarOrder.T (@Eid VarOrder.T 1375))).
Lemma joint_update_ready_1391 old :
 (exists ground bits, VM.find 1375 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1390 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1391.
Proof.
 intros [g1375 [b1375 H1375]].
 intros [g1390 [b1390 H1390]].
 unfold joint_update_expr_1391.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_1392 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1389)) (@Eref VarOrder.T (@Eid VarOrder.T 1391))).
Lemma joint_update_ready_1392 old :
 (exists ground bits, VM.find 1389 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1391 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_1392.
Proof.
 intros [g1389 [b1389 H1389]].
 intros [g1391 [b1391 H1391]].
 unfold joint_update_expr_1392.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7761 : hfexpr VarOrder.T := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 65))).
Lemma joint_update_ready_7761 old :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7761.
Proof.
 intros [g65 [b65 H65]].
 unfold joint_update_expr_7761.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7766 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bsub (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Econst VarOrder.T (Fuint 32) [::false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_7766 old :
 concrete_expression_ready old joint_update_expr_7766.
Proof.
 unfold joint_update_expr_7766.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7767 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 7766))).
Lemma joint_update_ready_7767 old :
 (exists ground bits, VM.find 7766 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7767.
Proof.
 intros [g7766 [b7766 H7766]].
 unfold joint_update_expr_7767.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7769 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 7768)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Lemma joint_update_ready_7769 old :
 (exists ground bits, VM.find 7768 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7769.
Proof.
 intros [g7768 [b7768 H7768]].
 unfold joint_update_expr_7769.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7770 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 7769))).
Lemma joint_update_ready_7770 old :
 (exists ground bits, VM.find 7769 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7770.
Proof.
 intros [g7769 [b7769 H7769]].
 unfold joint_update_expr_7770.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7771 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 84)) (@Econst VarOrder.T (Fuint 2) [::true; true])).
Lemma joint_update_ready_7771 old :
 (exists ground bits, VM.find 84 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7771.
Proof.
 intros [g84 [b84 H84]].
 unfold joint_update_expr_7771.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7772 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 84)) (@Econst VarOrder.T (Fuint 2) [::true; false])).
Lemma joint_update_ready_7772 old :
 (exists ground bits, VM.find 84 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7772.
Proof.
 intros [g84 [b84 H84]].
 unfold joint_update_expr_7772.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7773 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7772)) (@Eref VarOrder.T (@Eid VarOrder.T 1360))).
Lemma joint_update_ready_7773 old :
 (exists ground bits, VM.find 1360 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7772 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7773.
Proof.
 intros [g1360 [b1360 H1360]].
 intros [g7772 [b7772 H7772]].
 unfold joint_update_expr_7773.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7774 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 1155)) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma joint_update_ready_7774 old :
 (exists ground bits, VM.find 1155 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7774.
Proof.
 intros [g1155 [b1155 H1155]].
 unfold joint_update_expr_7774.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7775 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7774)) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma joint_update_ready_7775 old :
 (exists ground bits, VM.find 7774 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7775.
Proof.
 intros [g7774 [b7774 H7774]].
 unfold joint_update_expr_7775.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7776 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 84)) (@Econst VarOrder.T (Fuint 2) [::false; true])).
Lemma joint_update_ready_7776 old :
 (exists ground bits, VM.find 84 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7776.
Proof.
 intros [g84 [b84 H84]].
 unfold joint_update_expr_7776.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7777 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7776)) (@Eref VarOrder.T (@Eid VarOrder.T 7768)) (@Eref VarOrder.T (@Eid VarOrder.T 7770))).
Lemma joint_update_ready_7777 old :
 (exists ground bits, VM.find 7768 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7770 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7776 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7777.
Proof.
 intros [g7768 [b7768 H7768]].
 intros [g7770 [b7770 H7770]].
 intros [g7776 [b7776 H7776]].
 unfold joint_update_expr_7777.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7778 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7773)) (@Eref VarOrder.T (@Eid VarOrder.T 7775)) (@Eref VarOrder.T (@Eid VarOrder.T 7777))).
Lemma joint_update_ready_7778 old :
 (exists ground bits, VM.find 7773 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7775 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7777 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7778.
Proof.
 intros [g7773 [b7773 H7773]].
 intros [g7775 [b7775 H7775]].
 intros [g7777 [b7777 H7777]].
 unfold joint_update_expr_7778.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7779 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7771)) (@Eref VarOrder.T (@Eid VarOrder.T 130)) (@Eref VarOrder.T (@Eid VarOrder.T 7778))).
Lemma joint_update_ready_7779 old :
 (exists ground bits, VM.find 130 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7771 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7778 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7779.
Proof.
 intros [g130 [b130 H130]].
 intros [g7771 [b7771 H7771]].
 intros [g7778 [b7778 H7778]].
 unfold joint_update_expr_7779.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7780 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Eref VarOrder.T (@Eid VarOrder.T 129)) (@Eref VarOrder.T (@Eid VarOrder.T 7779))).
Lemma joint_update_ready_7780 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 129 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7779 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7780.
Proof.
 intros [g128 [b128 H128]].
 intros [g129 [b129 H129]].
 intros [g7779 [b7779 H7779]].
 unfold joint_update_expr_7780.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7781 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Eref VarOrder.T (@Eid VarOrder.T 7768)) (@Eref VarOrder.T (@Eid VarOrder.T 7780))).
Lemma joint_update_ready_7781 old :
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7768 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7780 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7781.
Proof.
 intros [g7765 [b7765 H7765]].
 intros [g7768 [b7768 H7768]].
 intros [g7780 [b7780 H7780]].
 unfold joint_update_expr_7781.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7794 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7762)) (@Eref VarOrder.T (@Eid VarOrder.T 85))).
Lemma joint_update_ready_7794 old :
 (exists ground bits, VM.find 85 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7762 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7794.
Proof.
 intros [g85 [b85 H85]].
 intros [g7762 [b7762 H7762]].
 unfold joint_update_expr_7794.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7795 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7794)) (@Eref VarOrder.T (@Eid VarOrder.T 1360))).
Lemma joint_update_ready_7795 old :
 (exists ground bits, VM.find 1360 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7794 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7795.
Proof.
 intros [g1360 [b1360 H1360]].
 intros [g7794 [b7794 H7794]].
 unfold joint_update_expr_7795.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7796 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7795)) (@Eref VarOrder.T (@Eid VarOrder.T 128))).
Lemma joint_update_ready_7796 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7795 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7796.
Proof.
 intros [g128 [b128 H128]].
 intros [g7795 [b7795 H7795]].
 unfold joint_update_expr_7796.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7797 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7796)) (@Econst VarOrder.T (Fuint 32) [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 75))).
Lemma joint_update_ready_7797 old :
 (exists ground bits, VM.find 75 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7796 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7797.
Proof.
 intros [g75 [b75 H75]].
 intros [g7796 [b7796 H7796]].
 unfold joint_update_expr_7797.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7799 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_7799 old :
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7799.
Proof.
 intros [g7765 [b7765 H7765]].
 unfold joint_update_expr_7799.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7800 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7799)) (@Eref VarOrder.T (@Eid VarOrder.T 7768)) (@Eref VarOrder.T (@Eid VarOrder.T 7749))).
Lemma joint_update_ready_7800 old :
 (exists ground bits, VM.find 7749 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7768 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7799 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7800.
Proof.
 intros [g7749 [b7749 H7749]].
 intros [g7768 [b7768 H7768]].
 intros [g7799 [b7799 H7799]].
 unfold joint_update_expr_7800.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7801 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7799)) (@Eref VarOrder.T (@Eid VarOrder.T 7797)) (@Eref VarOrder.T (@Eid VarOrder.T 7748))).
Lemma joint_update_ready_7801 old :
 (exists ground bits, VM.find 7748 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7797 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7799 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7801.
Proof.
 intros [g7748 [b7748 H7748]].
 intros [g7797 [b7797 H7797]].
 intros [g7799 [b7799 H7799]].
 unfold joint_update_expr_7801.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7849 : hfexpr VarOrder.T := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 65))).
Lemma joint_update_ready_7849 old :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7849.
Proof.
 intros [g65 [b65 H65]].
 unfold joint_update_expr_7849.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7850 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_7850 old :
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7850.
Proof.
 intros [g7765 [b7765 H7765]].
 unfold joint_update_expr_7850.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7851 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7850)) (@Eref VarOrder.T (@Eid VarOrder.T 128))).
Lemma joint_update_ready_7851 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7850 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7851.
Proof.
 intros [g128 [b128 H128]].
 intros [g7850 [b7850 H7850]].
 unfold joint_update_expr_7851.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7852 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7849)) (@Eref VarOrder.T (@Eid VarOrder.T 7851))).
Lemma joint_update_ready_7852 old :
 (exists ground bits, VM.find 7849 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7851 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7852.
Proof.
 intros [g7849 [b7849 H7849]].
 intros [g7851 [b7851 H7851]].
 unfold joint_update_expr_7852.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7853 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_7853 old :
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7853.
Proof.
 intros [g7765 [b7765 H7765]].
 unfold joint_update_expr_7853.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7854 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_7854 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7854.
Proof.
 intros [g128 [b128 H128]].
 unfold joint_update_expr_7854.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7855 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7853)) (@Eref VarOrder.T (@Eid VarOrder.T 7854))).
Lemma joint_update_ready_7855 old :
 (exists ground bits, VM.find 7853 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7854 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7855.
Proof.
 intros [g7853 [b7853 H7853]].
 intros [g7854 [b7854 H7854]].
 unfold joint_update_expr_7855.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7856 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 88)) (@Econst VarOrder.T (Fuint 3) [::false; true; true])).
Lemma joint_update_ready_7856 old :
 (exists ground bits, VM.find 88 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7856.
Proof.
 intros [g88 [b88 H88]].
 unfold joint_update_expr_7856.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7857 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7856)) (@Eref VarOrder.T (@Eid VarOrder.T 1308)) (@Eref VarOrder.T (@Eid VarOrder.T 7816))).
Lemma joint_update_ready_7857 old :
 (exists ground bits, VM.find 1308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7816 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7856 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7857.
Proof.
 intros [g1308 [b1308 H1308]].
 intros [g7816 [b7816 H7816]].
 intros [g7856 [b7856 H7856]].
 unfold joint_update_expr_7857.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7858 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 84)) (@Econst VarOrder.T (Fuint 2) [::true; false])).
Lemma joint_update_ready_7858 old :
 (exists ground bits, VM.find 84 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7858.
Proof.
 intros [g84 [b84 H84]].
 unfold joint_update_expr_7858.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7859 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7858)) (@Eref VarOrder.T (@Eid VarOrder.T 1360))).
Lemma joint_update_ready_7859 old :
 (exists ground bits, VM.find 1360 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7858 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7859.
Proof.
 intros [g1360 [b1360 H1360]].
 intros [g7858 [b7858 H7858]].
 unfold joint_update_expr_7859.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7860 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 7749)) (@Eref VarOrder.T (@Eid VarOrder.T 7751))).
Lemma joint_update_ready_7860 old :
 (exists ground bits, VM.find 7749 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7751 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7860.
Proof.
 intros [g7749 [b7749 H7749]].
 intros [g7751 [b7751 H7751]].
 intros [g7855 [b7855 H7855]].
 unfold joint_update_expr_7860.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7861 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 7748)) (@Eref VarOrder.T (@Eid VarOrder.T 7750))).
Lemma joint_update_ready_7861 old :
 (exists ground bits, VM.find 7748 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7750 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7861.
Proof.
 intros [g7748 [b7748 H7748]].
 intros [g7750 [b7750 H7750]].
 intros [g7855 [b7855 H7855]].
 unfold joint_update_expr_7861.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7862 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 1154)) (@Eref VarOrder.T (@Eid VarOrder.T 7752))).
Lemma joint_update_ready_7862 old :
 (exists ground bits, VM.find 1154 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7752 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7862.
Proof.
 intros [g1154 [b1154 H1154]].
 intros [g7752 [b7752 H7752]].
 intros [g7855 [b7855 H7855]].
 unfold joint_update_expr_7862.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7863 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 7857)) (@Eref VarOrder.T (@Eid VarOrder.T 7753))).
Lemma joint_update_ready_7863 old :
 (exists ground bits, VM.find 7753 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7857 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7863.
Proof.
 intros [g7753 [b7753 H7753]].
 intros [g7855 [b7855 H7855]].
 intros [g7857 [b7857 H7857]].
 unfold joint_update_expr_7863.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7864 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 91)) (@Eref VarOrder.T (@Eid VarOrder.T 7754))).
Lemma joint_update_ready_7864 old :
 (exists ground bits, VM.find 91 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7754 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7864.
Proof.
 intros [g91 [b91 H91]].
 intros [g7754 [b7754 H7754]].
 intros [g7855 [b7855 H7855]].
 unfold joint_update_expr_7864.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7865 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 92)) (@Eref VarOrder.T (@Eid VarOrder.T 7755))).
Lemma joint_update_ready_7865 old :
 (exists ground bits, VM.find 92 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7755 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7865.
Proof.
 intros [g92 [b92 H92]].
 intros [g7755 [b7755 H7755]].
 intros [g7855 [b7855 H7855]].
 unfold joint_update_expr_7865.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7866 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 93)) (@Eref VarOrder.T (@Eid VarOrder.T 7756))).
Lemma joint_update_ready_7866 old :
 (exists ground bits, VM.find 93 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7756 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7866.
Proof.
 intros [g93 [b93 H93]].
 intros [g7756 [b7756 H7756]].
 intros [g7855 [b7855 H7855]].
 unfold joint_update_expr_7866.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7867 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 94)) (@Eref VarOrder.T (@Eid VarOrder.T 7757))).
Lemma joint_update_ready_7867 old :
 (exists ground bits, VM.find 94 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7757 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7867.
Proof.
 intros [g94 [b94 H94]].
 intros [g7757 [b7757 H7757]].
 intros [g7855 [b7855 H7855]].
 unfold joint_update_expr_7867.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7868 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 95)) (@Eref VarOrder.T (@Eid VarOrder.T 7758))).
Lemma joint_update_ready_7868 old :
 (exists ground bits, VM.find 95 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7758 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7868.
Proof.
 intros [g95 [b95 H95]].
 intros [g7758 [b7758 H7758]].
 intros [g7855 [b7855 H7855]].
 unfold joint_update_expr_7868.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7869 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 96)) (@Eref VarOrder.T (@Eid VarOrder.T 7759))).
Lemma joint_update_ready_7869 old :
 (exists ground bits, VM.find 96 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7759 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7869.
Proof.
 intros [g96 [b96 H96]].
 intros [g7759 [b7759 H7759]].
 intros [g7855 [b7855 H7855]].
 unfold joint_update_expr_7869.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7870 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7855)) (@Eref VarOrder.T (@Eid VarOrder.T 7859)) (@Eref VarOrder.T (@Eid VarOrder.T 7760))).
Lemma joint_update_ready_7870 old :
 (exists ground bits, VM.find 7760 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7855 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7859 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7870.
Proof.
 intros [g7760 [b7760 H7760]].
 intros [g7855 [b7855 H7855]].
 intros [g7859 [b7859 H7859]].
 unfold joint_update_expr_7870.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7871 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7864))).
Lemma joint_update_ready_7871 old :
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7864 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7871.
Proof.
 intros [g7852 [b7852 H7852]].
 intros [g7864 [b7864 H7864]].
 unfold joint_update_expr_7871.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7872 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7865))).
Lemma joint_update_ready_7872 old :
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7865 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7872.
Proof.
 intros [g7852 [b7852 H7852]].
 intros [g7865 [b7865 H7865]].
 unfold joint_update_expr_7872.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7873 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7867))).
Lemma joint_update_ready_7873 old :
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7867 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7873.
Proof.
 intros [g7852 [b7852 H7852]].
 intros [g7867 [b7867 H7867]].
 unfold joint_update_expr_7873.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7874 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7868))).
Lemma joint_update_ready_7874 old :
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7868 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7874.
Proof.
 intros [g7852 [b7852 H7852]].
 intros [g7868 [b7868 H7868]].
 unfold joint_update_expr_7874.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7875 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7869))).
Lemma joint_update_ready_7875 old :
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7869 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7875.
Proof.
 intros [g7852 [b7852 H7852]].
 intros [g7869 [b7869 H7869]].
 unfold joint_update_expr_7875.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7876 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7870))).
Lemma joint_update_ready_7876 old :
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7870 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7876.
Proof.
 intros [g7852 [b7852 H7852]].
 intros [g7870 [b7870 H7870]].
 unfold joint_update_expr_7876.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7877 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Eref VarOrder.T (@Eid VarOrder.T 7751)) (@Eref VarOrder.T (@Eid VarOrder.T 7860))).
Lemma joint_update_ready_7877 old :
 (exists ground bits, VM.find 7751 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7860 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7877.
Proof.
 intros [g7751 [b7751 H7751]].
 intros [g7852 [b7852 H7852]].
 intros [g7860 [b7860 H7860]].
 unfold joint_update_expr_7877.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7878 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Eref VarOrder.T (@Eid VarOrder.T 7750)) (@Eref VarOrder.T (@Eid VarOrder.T 7861))).
Lemma joint_update_ready_7878 old :
 (exists ground bits, VM.find 7750 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7861 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7878.
Proof.
 intros [g7750 [b7750 H7750]].
 intros [g7852 [b7852 H7852]].
 intros [g7861 [b7861 H7861]].
 unfold joint_update_expr_7878.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7879 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Eref VarOrder.T (@Eid VarOrder.T 7752)) (@Eref VarOrder.T (@Eid VarOrder.T 7862))).
Lemma joint_update_ready_7879 old :
 (exists ground bits, VM.find 7752 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7862 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7879.
Proof.
 intros [g7752 [b7752 H7752]].
 intros [g7852 [b7852 H7852]].
 intros [g7862 [b7862 H7862]].
 unfold joint_update_expr_7879.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7880 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Eref VarOrder.T (@Eid VarOrder.T 7753)) (@Eref VarOrder.T (@Eid VarOrder.T 7863))).
Lemma joint_update_ready_7880 old :
 (exists ground bits, VM.find 7753 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7863 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7880.
Proof.
 intros [g7753 [b7753 H7753]].
 intros [g7852 [b7852 H7852]].
 intros [g7863 [b7863 H7863]].
 unfold joint_update_expr_7880.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7881 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7852)) (@Eref VarOrder.T (@Eid VarOrder.T 7756)) (@Eref VarOrder.T (@Eid VarOrder.T 7866))).
Lemma joint_update_ready_7881 old :
 (exists ground bits, VM.find 7756 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7852 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7866 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7881.
Proof.
 intros [g7756 [b7756 H7756]].
 intros [g7852 [b7852 H7852]].
 intros [g7866 [b7866 H7866]].
 unfold joint_update_expr_7881.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7882 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 7752))).
Lemma joint_update_ready_7882 old :
 (exists ground bits, VM.find 7752 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7882.
Proof.
 intros [g7752 [b7752 H7752]].
 unfold joint_update_expr_7882.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7883 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7882)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Lemma joint_update_ready_7883 old :
 (exists ground bits, VM.find 7882 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7883.
Proof.
 intros [g7882 [b7882 H7882]].
 unfold joint_update_expr_7883.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7884 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 7752))).
Lemma joint_update_ready_7884 old :
 (exists ground bits, VM.find 7752 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7884.
Proof.
 intros [g7752 [b7752 H7752]].
 unfold joint_update_expr_7884.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7885 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7884)) (@Econst VarOrder.T (Fuint 2) [::true; true])).
Lemma joint_update_ready_7885 old :
 (exists ground bits, VM.find 7884 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7885.
Proof.
 intros [g7884 [b7884 H7884]].
 unfold joint_update_expr_7885.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7886 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7883)) (@Eref VarOrder.T (@Eid VarOrder.T 7885))).
Lemma joint_update_ready_7886 old :
 (exists ground bits, VM.find 7883 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7885 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7886.
Proof.
 intros [g7883 [b7883 H7883]].
 intros [g7885 [b7885 H7885]].
 unfold joint_update_expr_7886.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7887 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 82)) (@Eref VarOrder.T (@Eid VarOrder.T 7886))).
Lemma joint_update_ready_7887 old :
 (exists ground bits, VM.find 82 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7886 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7887.
Proof.
 intros [g82 [b82 H82]].
 intros [g7886 [b7886 H7886]].
 unfold joint_update_expr_7887.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7888 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Ucvt (@Eref VarOrder.T (@Eid VarOrder.T 82))).
Lemma joint_update_ready_7888 old :
 (exists ground bits, VM.find 82 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7888.
Proof.
 intros [g82 [b82 H82]].
 unfold joint_update_expr_7888.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7889 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 7887))).
Lemma joint_update_ready_7889 old :
 (exists ground bits, VM.find 7887 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7889.
Proof.
 intros [g7887 [b7887 H7887]].
 unfold joint_update_expr_7889.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7890 : hfexpr VarOrder.T := (@Ecast VarOrder.T AsSInt (@Eref VarOrder.T (@Eid VarOrder.T 7889))).
Lemma joint_update_ready_7890 old :
 (exists ground bits, VM.find 7889 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7890.
Proof.
 intros [g7889 [b7889 H7889]].
 unfold joint_update_expr_7890.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7891 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 7887))).
Lemma joint_update_ready_7891 old :
 (exists ground bits, VM.find 7887 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7891.
Proof.
 intros [g7887 [b7887 H7887]].
 unfold joint_update_expr_7891.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7892 : hfexpr VarOrder.T := (@Ecast VarOrder.T AsSInt (@Eref VarOrder.T (@Eid VarOrder.T 7891))).
Lemma joint_update_ready_7892 old :
 (exists ground bits, VM.find 7891 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7892.
Proof.
 intros [g7891 [b7891 H7891]].
 unfold joint_update_expr_7892.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7893 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 15 0) (@Eref VarOrder.T (@Eid VarOrder.T 7887))).
Lemma joint_update_ready_7893 old :
 (exists ground bits, VM.find 7887 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7893.
Proof.
 intros [g7887 [b7887 H7887]].
 unfold joint_update_expr_7893.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7894 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Ucvt (@Eref VarOrder.T (@Eid VarOrder.T 7893))).
Lemma joint_update_ready_7894 old :
 (exists ground bits, VM.find 7893 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7894.
Proof.
 intros [g7893 [b7893 H7893]].
 unfold joint_update_expr_7894.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7895 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 7 0) (@Eref VarOrder.T (@Eid VarOrder.T 7887))).
Lemma joint_update_ready_7895 old :
 (exists ground bits, VM.find 7887 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7895.
Proof.
 intros [g7887 [b7887 H7887]].
 unfold joint_update_expr_7895.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7896 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Ucvt (@Eref VarOrder.T (@Eid VarOrder.T 7895))).
Lemma joint_update_ready_7896 old :
 (exists ground bits, VM.find 7895 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7896.
Proof.
 intros [g7895 [b7895 H7895]].
 unfold joint_update_expr_7896.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7897 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))).
Lemma joint_update_ready_7897 old :
 (exists ground bits, VM.find 7755 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7897.
Proof.
 intros [g7755 [b7755 H7755]].
 unfold joint_update_expr_7897.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7898 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7897)) (@Eref VarOrder.T (@Eid VarOrder.T 7890)) (@Eref VarOrder.T (@Eid VarOrder.T 7888))).
Lemma joint_update_ready_7898 old :
 (exists ground bits, VM.find 7888 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7890 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7897 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7898.
Proof.
 intros [g7888 [b7888 H7888]].
 intros [g7890 [b7890 H7890]].
 intros [g7897 [b7897 H7897]].
 unfold joint_update_expr_7898.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7899 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))).
Lemma joint_update_ready_7899 old :
 (exists ground bits, VM.find 7755 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7899.
Proof.
 intros [g7755 [b7755 H7755]].
 unfold joint_update_expr_7899.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7900 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7899)) (@Eref VarOrder.T (@Eid VarOrder.T 7892)) (@Eref VarOrder.T (@Eid VarOrder.T 7898))).
Lemma joint_update_ready_7900 old :
 (exists ground bits, VM.find 7892 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7898 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7899 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7900.
Proof.
 intros [g7892 [b7892 H7892]].
 intros [g7898 [b7898 H7898]].
 intros [g7899 [b7899 H7899]].
 unfold joint_update_expr_7900.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7901 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))).
Lemma joint_update_ready_7901 old :
 (exists ground bits, VM.find 7755 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7901.
Proof.
 intros [g7755 [b7755 H7755]].
 unfold joint_update_expr_7901.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7902 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7901)) (@Eref VarOrder.T (@Eid VarOrder.T 7894)) (@Eref VarOrder.T (@Eid VarOrder.T 7900))).
Lemma joint_update_ready_7902 old :
 (exists ground bits, VM.find 7894 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7900 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7901 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7902.
Proof.
 intros [g7894 [b7894 H7894]].
 intros [g7900 [b7900 H7900]].
 intros [g7901 [b7901 H7901]].
 unfold joint_update_expr_7902.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7903 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7755))).
Lemma joint_update_ready_7903 old :
 (exists ground bits, VM.find 7755 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7903.
Proof.
 intros [g7755 [b7755 H7755]].
 unfold joint_update_expr_7903.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7904 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7903)) (@Eref VarOrder.T (@Eid VarOrder.T 7896)) (@Eref VarOrder.T (@Eid VarOrder.T 7902))).
Lemma joint_update_ready_7904 old :
 (exists ground bits, VM.find 7896 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7902 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7903 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7904.
Proof.
 intros [g7896 [b7896 H7896]].
 intros [g7902 [b7902 H7902]].
 intros [g7903 [b7903 H7903]].
 unfold joint_update_expr_7904.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7926 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Ucvt (@Eref VarOrder.T (@Eid VarOrder.T 7752))).
Lemma joint_update_ready_7926 old :
 (exists ground bits, VM.find 7752 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7926.
Proof.
 intros [g7752 [b7752 H7752]].
 unfold joint_update_expr_7926.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7927 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 7751)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Lemma joint_update_ready_7927 old :
 (exists ground bits, VM.find 7751 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7927.
Proof.
 intros [g7751 [b7751 H7751]].
 unfold joint_update_expr_7927.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7928 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 7927))).
Lemma joint_update_ready_7928 old :
 (exists ground bits, VM.find 7927 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7928.
Proof.
 intros [g7927 [b7927 H7927]].
 unfold joint_update_expr_7928.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7929 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Ucvt (@Eref VarOrder.T (@Eid VarOrder.T 7928))).
Lemma joint_update_ready_7929 old :
 (exists ground bits, VM.find 7928 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7929.
Proof.
 intros [g7928 [b7928 H7928]].
 unfold joint_update_expr_7929.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7930 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Ucvt (@Eref VarOrder.T (@Eid VarOrder.T 120))).
Lemma joint_update_ready_7930 old :
 (exists ground bits, VM.find 120 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7930.
Proof.
 intros [g120 [b120 H120]].
 unfold joint_update_expr_7930.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7931 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7756))).
Lemma joint_update_ready_7931 old :
 (exists ground bits, VM.find 7756 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7931.
Proof.
 intros [g7756 [b7756 H7756]].
 unfold joint_update_expr_7931.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7932 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7931)) (@Eref VarOrder.T (@Eid VarOrder.T 7904)) (@Eref VarOrder.T (@Eid VarOrder.T 7926))).
Lemma joint_update_ready_7932 old :
 (exists ground bits, VM.find 7904 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7926 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7931 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7932.
Proof.
 intros [g7904 [b7904 H7904]].
 intros [g7926 [b7926 H7926]].
 intros [g7931 [b7931 H7931]].
 unfold joint_update_expr_7932.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7933 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7756))).
Lemma joint_update_ready_7933 old :
 (exists ground bits, VM.find 7756 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7933.
Proof.
 intros [g7756 [b7756 H7756]].
 unfold joint_update_expr_7933.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7934 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7933)) (@Eref VarOrder.T (@Eid VarOrder.T 7929)) (@Eref VarOrder.T (@Eid VarOrder.T 7932))).
Lemma joint_update_ready_7934 old :
 (exists ground bits, VM.find 7929 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7932 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7933 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7934.
Proof.
 intros [g7929 [b7929 H7929]].
 intros [g7932 [b7932 H7932]].
 intros [g7933 [b7933 H7933]].
 unfold joint_update_expr_7934.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7935 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7756))).
Lemma joint_update_ready_7935 old :
 (exists ground bits, VM.find 7756 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7935.
Proof.
 intros [g7756 [b7756 H7756]].
 unfold joint_update_expr_7935.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7936 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7935)) (@Eref VarOrder.T (@Eid VarOrder.T 7930)) (@Eref VarOrder.T (@Eid VarOrder.T 7934))).
Lemma joint_update_ready_7936 old :
 (exists ground bits, VM.find 7930 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7934 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7935 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7936.
Proof.
 intros [g7930 [b7930 H7930]].
 intros [g7934 [b7934 H7934]].
 intros [g7935 [b7935 H7935]].
 unfold joint_update_expr_7936.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7937 : hfexpr VarOrder.T := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 7936))).
Lemma joint_update_ready_7937 old :
 (exists ground bits, VM.find 7936 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7937.
Proof.
 intros [g7936 [b7936 H7936]].
 unfold joint_update_expr_7937.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7938 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_7938 old :
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7938.
Proof.
 intros [g7765 [b7765 H7765]].
 unfold joint_update_expr_7938.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7939 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7757)) (@Eref VarOrder.T (@Eid VarOrder.T 7938))).
Lemma joint_update_ready_7939 old :
 (exists ground bits, VM.find 7757 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7938 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7939.
Proof.
 intros [g7757 [b7757 H7757]].
 intros [g7938 [b7938 H7938]].
 unfold joint_update_expr_7939.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7940 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_7940 old :
 (exists ground bits, VM.find 128 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7940.
Proof.
 intros [g128 [b128 H128]].
 unfold joint_update_expr_7940.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_7941 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7939)) (@Eref VarOrder.T (@Eid VarOrder.T 7940))).
Lemma joint_update_ready_7941 old :
 (exists ground bits, VM.find 7939 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7940 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_7941.
Proof.
 intros [g7939 [b7939 H7939]].
 intros [g7940 [b7940 H7940]].
 unfold joint_update_expr_7941.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8089 : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Lemma joint_update_ready_8089 old :
 concrete_expression_ready old joint_update_expr_8089.
Proof.
 unfold joint_update_expr_8089.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8090 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8089)).
Lemma joint_update_ready_8090 old :
 (exists ground bits, VM.find 8089 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8090.
Proof.
 intros [g8089 [b8089 H8089]].
 unfold joint_update_expr_8090.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8091 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8091 old :
 concrete_expression_ready old joint_update_expr_8091.
Proof.
 unfold joint_update_expr_8091.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8092 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8091)).
Lemma joint_update_ready_8092 old :
 (exists ground bits, VM.find 8091 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8092.
Proof.
 intros [g8091 [b8091 H8091]].
 unfold joint_update_expr_8092.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8093 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8093 old :
 concrete_expression_ready old joint_update_expr_8093.
Proof.
 unfold joint_update_expr_8093.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8094 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8093)).
Lemma joint_update_ready_8094 old :
 (exists ground bits, VM.find 8093 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8094.
Proof.
 intros [g8093 [b8093 H8093]].
 unfold joint_update_expr_8094.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8095 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8095 old :
 concrete_expression_ready old joint_update_expr_8095.
Proof.
 unfold joint_update_expr_8095.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8096 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8095)).
Lemma joint_update_ready_8096 old :
 (exists ground bits, VM.find 8095 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8096.
Proof.
 intros [g8095 [b8095 H8095]].
 unfold joint_update_expr_8096.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8097 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8097 old :
 concrete_expression_ready old joint_update_expr_8097.
Proof.
 unfold joint_update_expr_8097.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8098 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8097)).
Lemma joint_update_ready_8098 old :
 (exists ground bits, VM.find 8097 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8098.
Proof.
 intros [g8097 [b8097 H8097]].
 unfold joint_update_expr_8098.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8099 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8099 old :
 concrete_expression_ready old joint_update_expr_8099.
Proof.
 unfold joint_update_expr_8099.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8100 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8099)).
Lemma joint_update_ready_8100 old :
 (exists ground bits, VM.find 8099 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8100.
Proof.
 intros [g8099 [b8099 H8099]].
 unfold joint_update_expr_8100.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8101 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8101 old :
 concrete_expression_ready old joint_update_expr_8101.
Proof.
 unfold joint_update_expr_8101.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8102 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8101)).
Lemma joint_update_ready_8102 old :
 (exists ground bits, VM.find 8101 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8102.
Proof.
 intros [g8101 [b8101 H8101]].
 unfold joint_update_expr_8102.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8103 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8103 old :
 concrete_expression_ready old joint_update_expr_8103.
Proof.
 unfold joint_update_expr_8103.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8104 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8103)).
Lemma joint_update_ready_8104 old :
 (exists ground bits, VM.find 8103 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8104.
Proof.
 intros [g8103 [b8103 H8103]].
 unfold joint_update_expr_8104.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8105 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8105 old :
 concrete_expression_ready old joint_update_expr_8105.
Proof.
 unfold joint_update_expr_8105.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8106 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8105)).
Lemma joint_update_ready_8106 old :
 (exists ground bits, VM.find 8105 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8106.
Proof.
 intros [g8105 [b8105 H8105]].
 unfold joint_update_expr_8106.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8107 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8107 old :
 concrete_expression_ready old joint_update_expr_8107.
Proof.
 unfold joint_update_expr_8107.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8108 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8107)).
Lemma joint_update_ready_8108 old :
 (exists ground bits, VM.find 8107 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8108.
Proof.
 intros [g8107 [b8107 H8107]].
 unfold joint_update_expr_8108.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8109 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8109 old :
 concrete_expression_ready old joint_update_expr_8109.
Proof.
 unfold joint_update_expr_8109.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8110 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8109)).
Lemma joint_update_ready_8110 old :
 (exists ground bits, VM.find 8109 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8110.
Proof.
 intros [g8109 [b8109 H8109]].
 unfold joint_update_expr_8110.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8111 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8111 old :
 concrete_expression_ready old joint_update_expr_8111.
Proof.
 unfold joint_update_expr_8111.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8112 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8111)).
Lemma joint_update_ready_8112 old :
 (exists ground bits, VM.find 8111 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8112.
Proof.
 intros [g8111 [b8111 H8111]].
 unfold joint_update_expr_8112.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8113 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8113 old :
 concrete_expression_ready old joint_update_expr_8113.
Proof.
 unfold joint_update_expr_8113.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8114 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8113)).
Lemma joint_update_ready_8114 old :
 (exists ground bits, VM.find 8113 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8114.
Proof.
 intros [g8113 [b8113 H8113]].
 unfold joint_update_expr_8114.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8115 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8115 old :
 concrete_expression_ready old joint_update_expr_8115.
Proof.
 unfold joint_update_expr_8115.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8116 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8115)).
Lemma joint_update_ready_8116 old :
 (exists ground bits, VM.find 8115 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8116.
Proof.
 intros [g8115 [b8115 H8115]].
 unfold joint_update_expr_8116.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8117 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8117 old :
 concrete_expression_ready old joint_update_expr_8117.
Proof.
 unfold joint_update_expr_8117.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8118 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8117)).
Lemma joint_update_ready_8118 old :
 (exists ground bits, VM.find 8117 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8118.
Proof.
 intros [g8117 [b8117 H8117]].
 unfold joint_update_expr_8118.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8119 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8119 old :
 concrete_expression_ready old joint_update_expr_8119.
Proof.
 unfold joint_update_expr_8119.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8120 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8119)).
Lemma joint_update_ready_8120 old :
 (exists ground bits, VM.find 8119 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8120.
Proof.
 intros [g8119 [b8119 H8119]].
 unfold joint_update_expr_8120.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8121 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8121 old :
 concrete_expression_ready old joint_update_expr_8121.
Proof.
 unfold joint_update_expr_8121.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8122 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8121)).
Lemma joint_update_ready_8122 old :
 (exists ground bits, VM.find 8121 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8122.
Proof.
 intros [g8121 [b8121 H8121]].
 unfold joint_update_expr_8122.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8123 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8123 old :
 concrete_expression_ready old joint_update_expr_8123.
Proof.
 unfold joint_update_expr_8123.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8124 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8123)).
Lemma joint_update_ready_8124 old :
 (exists ground bits, VM.find 8123 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8124.
Proof.
 intros [g8123 [b8123 H8123]].
 unfold joint_update_expr_8124.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8125 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8125 old :
 concrete_expression_ready old joint_update_expr_8125.
Proof.
 unfold joint_update_expr_8125.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8126 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8125)).
Lemma joint_update_ready_8126 old :
 (exists ground bits, VM.find 8125 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8126.
Proof.
 intros [g8125 [b8125 H8125]].
 unfold joint_update_expr_8126.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8127 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8127 old :
 concrete_expression_ready old joint_update_expr_8127.
Proof.
 unfold joint_update_expr_8127.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8128 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8127)).
Lemma joint_update_ready_8128 old :
 (exists ground bits, VM.find 8127 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8128.
Proof.
 intros [g8127 [b8127 H8127]].
 unfold joint_update_expr_8128.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8129 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8129 old :
 concrete_expression_ready old joint_update_expr_8129.
Proof.
 unfold joint_update_expr_8129.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8130 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8129)).
Lemma joint_update_ready_8130 old :
 (exists ground bits, VM.find 8129 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8130.
Proof.
 intros [g8129 [b8129 H8129]].
 unfold joint_update_expr_8130.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8131 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8131 old :
 concrete_expression_ready old joint_update_expr_8131.
Proof.
 unfold joint_update_expr_8131.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8132 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8131)).
Lemma joint_update_ready_8132 old :
 (exists ground bits, VM.find 8131 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8132.
Proof.
 intros [g8131 [b8131 H8131]].
 unfold joint_update_expr_8132.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8133 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8133 old :
 concrete_expression_ready old joint_update_expr_8133.
Proof.
 unfold joint_update_expr_8133.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8134 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8133)).
Lemma joint_update_ready_8134 old :
 (exists ground bits, VM.find 8133 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8134.
Proof.
 intros [g8133 [b8133 H8133]].
 unfold joint_update_expr_8134.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8135 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8135 old :
 concrete_expression_ready old joint_update_expr_8135.
Proof.
 unfold joint_update_expr_8135.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8136 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8135)).
Lemma joint_update_ready_8136 old :
 (exists ground bits, VM.find 8135 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8136.
Proof.
 intros [g8135 [b8135 H8135]].
 unfold joint_update_expr_8136.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8137 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8137 old :
 concrete_expression_ready old joint_update_expr_8137.
Proof.
 unfold joint_update_expr_8137.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8138 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8137)).
Lemma joint_update_ready_8138 old :
 (exists ground bits, VM.find 8137 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8138.
Proof.
 intros [g8137 [b8137 H8137]].
 unfold joint_update_expr_8138.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8139 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8139 old :
 concrete_expression_ready old joint_update_expr_8139.
Proof.
 unfold joint_update_expr_8139.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8140 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8139)).
Lemma joint_update_ready_8140 old :
 (exists ground bits, VM.find 8139 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8140.
Proof.
 intros [g8139 [b8139 H8139]].
 unfold joint_update_expr_8140.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8141 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8141 old :
 concrete_expression_ready old joint_update_expr_8141.
Proof.
 unfold joint_update_expr_8141.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8142 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8141)).
Lemma joint_update_ready_8142 old :
 (exists ground bits, VM.find 8141 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8142.
Proof.
 intros [g8141 [b8141 H8141]].
 unfold joint_update_expr_8142.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8143 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8143 old :
 concrete_expression_ready old joint_update_expr_8143.
Proof.
 unfold joint_update_expr_8143.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8144 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8143)).
Lemma joint_update_ready_8144 old :
 (exists ground bits, VM.find 8143 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8144.
Proof.
 intros [g8143 [b8143 H8143]].
 unfold joint_update_expr_8144.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8145 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8145 old :
 concrete_expression_ready old joint_update_expr_8145.
Proof.
 unfold joint_update_expr_8145.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8146 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8145)).
Lemma joint_update_ready_8146 old :
 (exists ground bits, VM.find 8145 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8146.
Proof.
 intros [g8145 [b8145 H8145]].
 unfold joint_update_expr_8146.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8147 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8147 old :
 concrete_expression_ready old joint_update_expr_8147.
Proof.
 unfold joint_update_expr_8147.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8148 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8147)).
Lemma joint_update_ready_8148 old :
 (exists ground bits, VM.find 8147 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8148.
Proof.
 intros [g8147 [b8147 H8147]].
 unfold joint_update_expr_8148.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8149 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8149 old :
 concrete_expression_ready old joint_update_expr_8149.
Proof.
 unfold joint_update_expr_8149.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8150 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8149)).
Lemma joint_update_ready_8150 old :
 (exists ground bits, VM.find 8149 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8150.
Proof.
 intros [g8149 [b8149 H8149]].
 unfold joint_update_expr_8150.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8151 : hfexpr VarOrder.T := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Lemma joint_update_ready_8151 old :
 concrete_expression_ready old joint_update_expr_8151.
Proof.
 unfold joint_update_expr_8151.
 eapply closure_validif with (width := 32%nat); [solve_joint_update_ready|solve_joint_update_ready|reflexivity].
Qed.
Definition joint_update_expr_8152 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 8151)).
Lemma joint_update_ready_8152 old :
 (exists ground bits, VM.find 8151 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8152.
Proof.
 intros [g8151 [b8151 H8151]].
 unfold joint_update_expr_8152.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8158 : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Lemma joint_update_ready_8158 old :
 concrete_expression_ready old joint_update_expr_8158.
Proof.
 unfold joint_update_expr_8158.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8159 : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Lemma joint_update_ready_8159 old :
 concrete_expression_ready old joint_update_expr_8159.
Proof.
 unfold joint_update_expr_8159.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8160 : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Lemma joint_update_ready_8160 old :
 concrete_expression_ready old joint_update_expr_8160.
Proof.
 unfold joint_update_expr_8160.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8161 : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Lemma joint_update_ready_8161 old :
 concrete_expression_ready old joint_update_expr_8161.
Proof.
 unfold joint_update_expr_8161.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8162 : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Lemma joint_update_ready_8162 old :
 concrete_expression_ready old joint_update_expr_8162.
Proof.
 unfold joint_update_expr_8162.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8163 : hfexpr VarOrder.T := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Lemma joint_update_ready_8163 old :
 concrete_expression_ready old joint_update_expr_8163.
Proof.
 unfold joint_update_expr_8163.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8361 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8360)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Lemma joint_update_ready_8361 old :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8361.
Proof.
 intros [g8360 [b8360 H8360]].
 unfold joint_update_expr_8361.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8362 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8358)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8361))).
Lemma joint_update_ready_8362 old :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8361 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8362.
Proof.
 intros [g8358 [b8358 H8358]].
 intros [g8361 [b8361 H8361]].
 unfold joint_update_expr_8362.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8363 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8356)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8362))).
Lemma joint_update_ready_8363 old :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8362 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8363.
Proof.
 intros [g8356 [b8356 H8356]].
 intros [g8362 [b8362 H8362]].
 unfold joint_update_expr_8363.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8364 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8354)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8363))).
Lemma joint_update_ready_8364 old :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8363 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8364.
Proof.
 intros [g8354 [b8354 H8354]].
 intros [g8363 [b8363 H8363]].
 unfold joint_update_expr_8364.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8365 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8352)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8364))).
Lemma joint_update_ready_8365 old :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8364 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8365.
Proof.
 intros [g8352 [b8352 H8352]].
 intros [g8364 [b8364 H8364]].
 unfold joint_update_expr_8365.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8366 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8350)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8365))).
Lemma joint_update_ready_8366 old :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8365 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8366.
Proof.
 intros [g8350 [b8350 H8350]].
 intros [g8365 [b8365 H8365]].
 unfold joint_update_expr_8366.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8367 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8348)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8366))).
Lemma joint_update_ready_8367 old :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8366 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8367.
Proof.
 intros [g8348 [b8348 H8348]].
 intros [g8366 [b8366 H8366]].
 unfold joint_update_expr_8367.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8368 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8346)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8367))).
Lemma joint_update_ready_8368 old :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8367 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8368.
Proof.
 intros [g8346 [b8346 H8346]].
 intros [g8367 [b8367 H8367]].
 unfold joint_update_expr_8368.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8369 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8344)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8368))).
Lemma joint_update_ready_8369 old :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8368 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8369.
Proof.
 intros [g8344 [b8344 H8344]].
 intros [g8368 [b8368 H8368]].
 unfold joint_update_expr_8369.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8370 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8342)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8369))).
Lemma joint_update_ready_8370 old :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8369 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8370.
Proof.
 intros [g8342 [b8342 H8342]].
 intros [g8369 [b8369 H8369]].
 unfold joint_update_expr_8370.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8371 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8340)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8370))).
Lemma joint_update_ready_8371 old :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8370 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8371.
Proof.
 intros [g8340 [b8340 H8340]].
 intros [g8370 [b8370 H8370]].
 unfold joint_update_expr_8371.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8372 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8338)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8371))).
Lemma joint_update_ready_8372 old :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8371 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8372.
Proof.
 intros [g8338 [b8338 H8338]].
 intros [g8371 [b8371 H8371]].
 unfold joint_update_expr_8372.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8373 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8336)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8372))).
Lemma joint_update_ready_8373 old :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8372 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8373.
Proof.
 intros [g8336 [b8336 H8336]].
 intros [g8372 [b8372 H8372]].
 unfold joint_update_expr_8373.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8374 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8334)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8373))).
Lemma joint_update_ready_8374 old :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8373 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8374.
Proof.
 intros [g8334 [b8334 H8334]].
 intros [g8373 [b8373 H8373]].
 unfold joint_update_expr_8374.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8375 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8332)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8374))).
Lemma joint_update_ready_8375 old :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8374 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8375.
Proof.
 intros [g8332 [b8332 H8332]].
 intros [g8374 [b8374 H8374]].
 unfold joint_update_expr_8375.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8376 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8330)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8375))).
Lemma joint_update_ready_8376 old :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8375 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8376.
Proof.
 intros [g8330 [b8330 H8330]].
 intros [g8375 [b8375 H8375]].
 unfold joint_update_expr_8376.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8377 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8328)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8376))).
Lemma joint_update_ready_8377 old :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8376 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8377.
Proof.
 intros [g8328 [b8328 H8328]].
 intros [g8376 [b8376 H8376]].
 unfold joint_update_expr_8377.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8378 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8326)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8377))).
Lemma joint_update_ready_8378 old :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8377 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8378.
Proof.
 intros [g8326 [b8326 H8326]].
 intros [g8377 [b8377 H8377]].
 unfold joint_update_expr_8378.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8379 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8324)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8378))).
Lemma joint_update_ready_8379 old :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8378 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8379.
Proof.
 intros [g8324 [b8324 H8324]].
 intros [g8378 [b8378 H8378]].
 unfold joint_update_expr_8379.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8380 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8322)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8379))).
Lemma joint_update_ready_8380 old :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8379 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8380.
Proof.
 intros [g8322 [b8322 H8322]].
 intros [g8379 [b8379 H8379]].
 unfold joint_update_expr_8380.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8381 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8320)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8380))).
Lemma joint_update_ready_8381 old :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8380 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8381.
Proof.
 intros [g8320 [b8320 H8320]].
 intros [g8380 [b8380 H8380]].
 unfold joint_update_expr_8381.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8382 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8318)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8381))).
Lemma joint_update_ready_8382 old :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8381 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8382.
Proof.
 intros [g8318 [b8318 H8318]].
 intros [g8381 [b8381 H8381]].
 unfold joint_update_expr_8382.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8383 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8316)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8382))).
Lemma joint_update_ready_8383 old :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8382 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8383.
Proof.
 intros [g8316 [b8316 H8316]].
 intros [g8382 [b8382 H8382]].
 unfold joint_update_expr_8383.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8384 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8314)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8383))).
Lemma joint_update_ready_8384 old :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8383 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8384.
Proof.
 intros [g8314 [b8314 H8314]].
 intros [g8383 [b8383 H8383]].
 unfold joint_update_expr_8384.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8385 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8312)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8384))).
Lemma joint_update_ready_8385 old :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8384 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8385.
Proof.
 intros [g8312 [b8312 H8312]].
 intros [g8384 [b8384 H8384]].
 unfold joint_update_expr_8385.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8386 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8310)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8385))).
Lemma joint_update_ready_8386 old :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8385 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8386.
Proof.
 intros [g8310 [b8310 H8310]].
 intros [g8385 [b8385 H8385]].
 unfold joint_update_expr_8386.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8387 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8308)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8386))).
Lemma joint_update_ready_8387 old :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8386 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8387.
Proof.
 intros [g8308 [b8308 H8308]].
 intros [g8386 [b8386 H8386]].
 unfold joint_update_expr_8387.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8388 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8306)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8387))).
Lemma joint_update_ready_8388 old :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8387 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8388.
Proof.
 intros [g8306 [b8306 H8306]].
 intros [g8387 [b8387 H8387]].
 unfold joint_update_expr_8388.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8389 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8304)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8388))).
Lemma joint_update_ready_8389 old :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8388 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8389.
Proof.
 intros [g8304 [b8304 H8304]].
 intros [g8388 [b8388 H8388]].
 unfold joint_update_expr_8389.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8390 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8302)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8389))).
Lemma joint_update_ready_8390 old :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8389 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8390.
Proof.
 intros [g8302 [b8302 H8302]].
 intros [g8389 [b8389 H8389]].
 unfold joint_update_expr_8390.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8391 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8300)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8390))).
Lemma joint_update_ready_8391 old :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8390 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8391.
Proof.
 intros [g8300 [b8300 H8300]].
 intros [g8390 [b8390 H8390]].
 unfold joint_update_expr_8391.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8392 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8298)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8391))).
Lemma joint_update_ready_8392 old :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8391 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8392.
Proof.
 intros [g8298 [b8298 H8298]].
 intros [g8391 [b8391 H8391]].
 unfold joint_update_expr_8392.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8393 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8296)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8392))).
Lemma joint_update_ready_8393 old :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8392 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8393.
Proof.
 intros [g8296 [b8296 H8296]].
 intros [g8392 [b8392 H8392]].
 unfold joint_update_expr_8393.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8394 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8294)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8393))).
Lemma joint_update_ready_8394 old :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8393 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8394.
Proof.
 intros [g8294 [b8294 H8294]].
 intros [g8393 [b8393 H8393]].
 unfold joint_update_expr_8394.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8395 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8292)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8394))).
Lemma joint_update_ready_8395 old :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8394 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8395.
Proof.
 intros [g8292 [b8292 H8292]].
 intros [g8394 [b8394 H8394]].
 unfold joint_update_expr_8395.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8396 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8290)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8395))).
Lemma joint_update_ready_8396 old :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8395 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8396.
Proof.
 intros [g8290 [b8290 H8290]].
 intros [g8395 [b8395 H8395]].
 unfold joint_update_expr_8396.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8397 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8288)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8396))).
Lemma joint_update_ready_8397 old :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8396 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8397.
Proof.
 intros [g8288 [b8288 H8288]].
 intros [g8396 [b8396 H8396]].
 unfold joint_update_expr_8397.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8398 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8286)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8397))).
Lemma joint_update_ready_8398 old :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8397 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8398.
Proof.
 intros [g8286 [b8286 H8286]].
 intros [g8397 [b8397 H8397]].
 unfold joint_update_expr_8398.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8399 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8284)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8398))).
Lemma joint_update_ready_8399 old :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8398 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8399.
Proof.
 intros [g8284 [b8284 H8284]].
 intros [g8398 [b8398 H8398]].
 unfold joint_update_expr_8399.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8400 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8282)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8399))).
Lemma joint_update_ready_8400 old :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8399 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8400.
Proof.
 intros [g8282 [b8282 H8282]].
 intros [g8399 [b8399 H8399]].
 unfold joint_update_expr_8400.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8401 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8280)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8400))).
Lemma joint_update_ready_8401 old :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8400 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8401.
Proof.
 intros [g8280 [b8280 H8280]].
 intros [g8400 [b8400 H8400]].
 unfold joint_update_expr_8401.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8402 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8278)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8401))).
Lemma joint_update_ready_8402 old :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8401 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8402.
Proof.
 intros [g8278 [b8278 H8278]].
 intros [g8401 [b8401 H8401]].
 unfold joint_update_expr_8402.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8403 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8276)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8402))).
Lemma joint_update_ready_8403 old :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8402 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8403.
Proof.
 intros [g8276 [b8276 H8276]].
 intros [g8402 [b8402 H8402]].
 unfold joint_update_expr_8403.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8404 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8274)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8403))).
Lemma joint_update_ready_8404 old :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8403 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8404.
Proof.
 intros [g8274 [b8274 H8274]].
 intros [g8403 [b8403 H8403]].
 unfold joint_update_expr_8404.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8405 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8272)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8404))).
Lemma joint_update_ready_8405 old :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8404 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8405.
Proof.
 intros [g8272 [b8272 H8272]].
 intros [g8404 [b8404 H8404]].
 unfold joint_update_expr_8405.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8406 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8270)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8405))).
Lemma joint_update_ready_8406 old :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8405 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8406.
Proof.
 intros [g8270 [b8270 H8270]].
 intros [g8405 [b8405 H8405]].
 unfold joint_update_expr_8406.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8407 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8268)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8406))).
Lemma joint_update_ready_8407 old :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8406 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8407.
Proof.
 intros [g8268 [b8268 H8268]].
 intros [g8406 [b8406 H8406]].
 unfold joint_update_expr_8407.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8408 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8266)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8407))).
Lemma joint_update_ready_8408 old :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8407 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8408.
Proof.
 intros [g8266 [b8266 H8266]].
 intros [g8407 [b8407 H8407]].
 unfold joint_update_expr_8408.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8409 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8264)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8408))).
Lemma joint_update_ready_8409 old :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8408 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8409.
Proof.
 intros [g8264 [b8264 H8264]].
 intros [g8408 [b8408 H8408]].
 unfold joint_update_expr_8409.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8606 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8360)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Econst VarOrder.T (Fuint 3) [::false; false; false])).
Lemma joint_update_ready_8606 old :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8606.
Proof.
 intros [g8360 [b8360 H8360]].
 unfold joint_update_expr_8606.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8607 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8358)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8606))).
Lemma joint_update_ready_8607 old :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8606 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8607.
Proof.
 intros [g8358 [b8358 H8358]].
 intros [g8606 [b8606 H8606]].
 unfold joint_update_expr_8607.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8608 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8356)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8607))).
Lemma joint_update_ready_8608 old :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8607 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8608.
Proof.
 intros [g8356 [b8356 H8356]].
 intros [g8607 [b8607 H8607]].
 unfold joint_update_expr_8608.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8609 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8354)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8608))).
Lemma joint_update_ready_8609 old :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8608 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8609.
Proof.
 intros [g8354 [b8354 H8354]].
 intros [g8608 [b8608 H8608]].
 unfold joint_update_expr_8609.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8610 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8352)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8609))).
Lemma joint_update_ready_8610 old :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8609 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8610.
Proof.
 intros [g8352 [b8352 H8352]].
 intros [g8609 [b8609 H8609]].
 unfold joint_update_expr_8610.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8611 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8350)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8610))).
Lemma joint_update_ready_8611 old :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8610 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8611.
Proof.
 intros [g8350 [b8350 H8350]].
 intros [g8610 [b8610 H8610]].
 unfold joint_update_expr_8611.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8612 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8348)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8611))).
Lemma joint_update_ready_8612 old :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8611 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8612.
Proof.
 intros [g8348 [b8348 H8348]].
 intros [g8611 [b8611 H8611]].
 unfold joint_update_expr_8612.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8613 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8346)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8612))).
Lemma joint_update_ready_8613 old :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8612 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8613.
Proof.
 intros [g8346 [b8346 H8346]].
 intros [g8612 [b8612 H8612]].
 unfold joint_update_expr_8613.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8614 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8344)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8613))).
Lemma joint_update_ready_8614 old :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8613 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8614.
Proof.
 intros [g8344 [b8344 H8344]].
 intros [g8613 [b8613 H8613]].
 unfold joint_update_expr_8614.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8615 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8342)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8614))).
Lemma joint_update_ready_8615 old :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8614 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8615.
Proof.
 intros [g8342 [b8342 H8342]].
 intros [g8614 [b8614 H8614]].
 unfold joint_update_expr_8615.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8616 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8340)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8615))).
Lemma joint_update_ready_8616 old :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8615 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8616.
Proof.
 intros [g8340 [b8340 H8340]].
 intros [g8615 [b8615 H8615]].
 unfold joint_update_expr_8616.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8617 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8338)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8616))).
Lemma joint_update_ready_8617 old :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8616 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8617.
Proof.
 intros [g8338 [b8338 H8338]].
 intros [g8616 [b8616 H8616]].
 unfold joint_update_expr_8617.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8618 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8336)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8617))).
Lemma joint_update_ready_8618 old :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8617 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8618.
Proof.
 intros [g8336 [b8336 H8336]].
 intros [g8617 [b8617 H8617]].
 unfold joint_update_expr_8618.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8619 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8334)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8618))).
Lemma joint_update_ready_8619 old :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8618 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8619.
Proof.
 intros [g8334 [b8334 H8334]].
 intros [g8618 [b8618 H8618]].
 unfold joint_update_expr_8619.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8620 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8332)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8619))).
Lemma joint_update_ready_8620 old :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8619 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8620.
Proof.
 intros [g8332 [b8332 H8332]].
 intros [g8619 [b8619 H8619]].
 unfold joint_update_expr_8620.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8621 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8330)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8620))).
Lemma joint_update_ready_8621 old :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8620 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8621.
Proof.
 intros [g8330 [b8330 H8330]].
 intros [g8620 [b8620 H8620]].
 unfold joint_update_expr_8621.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8622 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8328)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8621))).
Lemma joint_update_ready_8622 old :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8621 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8622.
Proof.
 intros [g8328 [b8328 H8328]].
 intros [g8621 [b8621 H8621]].
 unfold joint_update_expr_8622.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8623 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8326)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8622))).
Lemma joint_update_ready_8623 old :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8622 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8623.
Proof.
 intros [g8326 [b8326 H8326]].
 intros [g8622 [b8622 H8622]].
 unfold joint_update_expr_8623.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8624 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8324)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8623))).
Lemma joint_update_ready_8624 old :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8623 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8624.
Proof.
 intros [g8324 [b8324 H8324]].
 intros [g8623 [b8623 H8623]].
 unfold joint_update_expr_8624.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8625 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8322)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8624))).
Lemma joint_update_ready_8625 old :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8624 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8625.
Proof.
 intros [g8322 [b8322 H8322]].
 intros [g8624 [b8624 H8624]].
 unfold joint_update_expr_8625.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8626 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8320)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8625))).
Lemma joint_update_ready_8626 old :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8625 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8626.
Proof.
 intros [g8320 [b8320 H8320]].
 intros [g8625 [b8625 H8625]].
 unfold joint_update_expr_8626.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8627 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8318)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8626))).
Lemma joint_update_ready_8627 old :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8626 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8627.
Proof.
 intros [g8318 [b8318 H8318]].
 intros [g8626 [b8626 H8626]].
 unfold joint_update_expr_8627.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8628 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8316)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8627))).
Lemma joint_update_ready_8628 old :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8627 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8628.
Proof.
 intros [g8316 [b8316 H8316]].
 intros [g8627 [b8627 H8627]].
 unfold joint_update_expr_8628.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8629 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8314)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8628))).
Lemma joint_update_ready_8629 old :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8628 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8629.
Proof.
 intros [g8314 [b8314 H8314]].
 intros [g8628 [b8628 H8628]].
 unfold joint_update_expr_8629.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8630 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8312)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8629))).
Lemma joint_update_ready_8630 old :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8629 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8630.
Proof.
 intros [g8312 [b8312 H8312]].
 intros [g8629 [b8629 H8629]].
 unfold joint_update_expr_8630.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8631 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8310)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8630))).
Lemma joint_update_ready_8631 old :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8630 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8631.
Proof.
 intros [g8310 [b8310 H8310]].
 intros [g8630 [b8630 H8630]].
 unfold joint_update_expr_8631.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8632 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8308)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8631))).
Lemma joint_update_ready_8632 old :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8631 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8632.
Proof.
 intros [g8308 [b8308 H8308]].
 intros [g8631 [b8631 H8631]].
 unfold joint_update_expr_8632.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8633 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8306)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8632))).
Lemma joint_update_ready_8633 old :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8632 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8633.
Proof.
 intros [g8306 [b8306 H8306]].
 intros [g8632 [b8632 H8632]].
 unfold joint_update_expr_8633.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8634 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8304)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8633))).
Lemma joint_update_ready_8634 old :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8633 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8634.
Proof.
 intros [g8304 [b8304 H8304]].
 intros [g8633 [b8633 H8633]].
 unfold joint_update_expr_8634.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8635 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8302)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8634))).
Lemma joint_update_ready_8635 old :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8634 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8635.
Proof.
 intros [g8302 [b8302 H8302]].
 intros [g8634 [b8634 H8634]].
 unfold joint_update_expr_8635.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8636 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8300)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8635))).
Lemma joint_update_ready_8636 old :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8635 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8636.
Proof.
 intros [g8300 [b8300 H8300]].
 intros [g8635 [b8635 H8635]].
 unfold joint_update_expr_8636.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8637 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8298)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8636))).
Lemma joint_update_ready_8637 old :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8636 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8637.
Proof.
 intros [g8298 [b8298 H8298]].
 intros [g8636 [b8636 H8636]].
 unfold joint_update_expr_8637.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8638 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8296)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8637))).
Lemma joint_update_ready_8638 old :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8637 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8638.
Proof.
 intros [g8296 [b8296 H8296]].
 intros [g8637 [b8637 H8637]].
 unfold joint_update_expr_8638.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8639 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8294)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8638))).
Lemma joint_update_ready_8639 old :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8638 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8639.
Proof.
 intros [g8294 [b8294 H8294]].
 intros [g8638 [b8638 H8638]].
 unfold joint_update_expr_8639.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8640 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8292)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8639))).
Lemma joint_update_ready_8640 old :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8639 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8640.
Proof.
 intros [g8292 [b8292 H8292]].
 intros [g8639 [b8639 H8639]].
 unfold joint_update_expr_8640.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8641 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8290)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8640))).
Lemma joint_update_ready_8641 old :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8640 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8641.
Proof.
 intros [g8290 [b8290 H8290]].
 intros [g8640 [b8640 H8640]].
 unfold joint_update_expr_8641.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8642 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8288)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8641))).
Lemma joint_update_ready_8642 old :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8641 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8642.
Proof.
 intros [g8288 [b8288 H8288]].
 intros [g8641 [b8641 H8641]].
 unfold joint_update_expr_8642.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8643 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8286)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8642))).
Lemma joint_update_ready_8643 old :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8642 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8643.
Proof.
 intros [g8286 [b8286 H8286]].
 intros [g8642 [b8642 H8642]].
 unfold joint_update_expr_8643.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8644 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8284)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8643))).
Lemma joint_update_ready_8644 old :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8643 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8644.
Proof.
 intros [g8284 [b8284 H8284]].
 intros [g8643 [b8643 H8643]].
 unfold joint_update_expr_8644.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8645 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8282)) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8644))).
Lemma joint_update_ready_8645 old :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8644 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8645.
Proof.
 intros [g8282 [b8282 H8282]].
 intros [g8644 [b8644 H8644]].
 unfold joint_update_expr_8645.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8646 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8280)) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8645))).
Lemma joint_update_ready_8646 old :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8645 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8646.
Proof.
 intros [g8280 [b8280 H8280]].
 intros [g8645 [b8645 H8645]].
 unfold joint_update_expr_8646.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8647 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8278)) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8646))).
Lemma joint_update_ready_8647 old :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8646 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8647.
Proof.
 intros [g8278 [b8278 H8278]].
 intros [g8646 [b8646 H8646]].
 unfold joint_update_expr_8647.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8648 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8276)) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8647))).
Lemma joint_update_ready_8648 old :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8647 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8648.
Proof.
 intros [g8276 [b8276 H8276]].
 intros [g8647 [b8647 H8647]].
 unfold joint_update_expr_8648.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8649 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8274)) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8648))).
Lemma joint_update_ready_8649 old :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8648 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8649.
Proof.
 intros [g8274 [b8274 H8274]].
 intros [g8648 [b8648 H8648]].
 unfold joint_update_expr_8649.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8650 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8272)) (@Econst VarOrder.T (Fuint 3) [::true; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8649))).
Lemma joint_update_ready_8650 old :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8649 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8650.
Proof.
 intros [g8272 [b8272 H8272]].
 intros [g8649 [b8649 H8649]].
 unfold joint_update_expr_8650.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8651 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8270)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8650))).
Lemma joint_update_ready_8651 old :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8650 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8651.
Proof.
 intros [g8270 [b8270 H8270]].
 intros [g8650 [b8650 H8650]].
 unfold joint_update_expr_8651.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8652 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8268)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8651))).
Lemma joint_update_ready_8652 old :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8651 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8652.
Proof.
 intros [g8268 [b8268 H8268]].
 intros [g8651 [b8651 H8651]].
 unfold joint_update_expr_8652.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8653 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8266)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8652))).
Lemma joint_update_ready_8653 old :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8652 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8653.
Proof.
 intros [g8266 [b8266 H8266]].
 intros [g8652 [b8652 H8652]].
 unfold joint_update_expr_8653.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8654 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8264)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8653))).
Lemma joint_update_ready_8654 old :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8653 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8654.
Proof.
 intros [g8264 [b8264 H8264]].
 intros [g8653 [b8653 H8653]].
 unfold joint_update_expr_8654.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8655 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8360)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_8655 old :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8655.
Proof.
 intros [g8360 [b8360 H8360]].
 unfold joint_update_expr_8655.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8656 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8358)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8655))).
Lemma joint_update_ready_8656 old :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8655 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8656.
Proof.
 intros [g8358 [b8358 H8358]].
 intros [g8655 [b8655 H8655]].
 unfold joint_update_expr_8656.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8657 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8356)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8656))).
Lemma joint_update_ready_8657 old :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8656 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8657.
Proof.
 intros [g8356 [b8356 H8356]].
 intros [g8656 [b8656 H8656]].
 unfold joint_update_expr_8657.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8658 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8354)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8657))).
Lemma joint_update_ready_8658 old :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8657 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8658.
Proof.
 intros [g8354 [b8354 H8354]].
 intros [g8657 [b8657 H8657]].
 unfold joint_update_expr_8658.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8659 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8352)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8658))).
Lemma joint_update_ready_8659 old :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8658 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8659.
Proof.
 intros [g8352 [b8352 H8352]].
 intros [g8658 [b8658 H8658]].
 unfold joint_update_expr_8659.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8660 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8350)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8659))).
Lemma joint_update_ready_8660 old :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8659 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8660.
Proof.
 intros [g8350 [b8350 H8350]].
 intros [g8659 [b8659 H8659]].
 unfold joint_update_expr_8660.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8661 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8348)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8660))).
Lemma joint_update_ready_8661 old :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8660 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8661.
Proof.
 intros [g8348 [b8348 H8348]].
 intros [g8660 [b8660 H8660]].
 unfold joint_update_expr_8661.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8662 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8346)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8661))).
Lemma joint_update_ready_8662 old :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8661 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8662.
Proof.
 intros [g8346 [b8346 H8346]].
 intros [g8661 [b8661 H8661]].
 unfold joint_update_expr_8662.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8663 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8344)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8662))).
Lemma joint_update_ready_8663 old :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8662 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8663.
Proof.
 intros [g8344 [b8344 H8344]].
 intros [g8662 [b8662 H8662]].
 unfold joint_update_expr_8663.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8664 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8342)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8663))).
Lemma joint_update_ready_8664 old :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8663 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8664.
Proof.
 intros [g8342 [b8342 H8342]].
 intros [g8663 [b8663 H8663]].
 unfold joint_update_expr_8664.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8665 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8340)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8664))).
Lemma joint_update_ready_8665 old :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8664 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8665.
Proof.
 intros [g8340 [b8340 H8340]].
 intros [g8664 [b8664 H8664]].
 unfold joint_update_expr_8665.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8666 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8338)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8665))).
Lemma joint_update_ready_8666 old :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8665 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8666.
Proof.
 intros [g8338 [b8338 H8338]].
 intros [g8665 [b8665 H8665]].
 unfold joint_update_expr_8666.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8667 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8336)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8666))).
Lemma joint_update_ready_8667 old :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8666 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8667.
Proof.
 intros [g8336 [b8336 H8336]].
 intros [g8666 [b8666 H8666]].
 unfold joint_update_expr_8667.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8668 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8334)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8667))).
Lemma joint_update_ready_8668 old :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8667 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8668.
Proof.
 intros [g8334 [b8334 H8334]].
 intros [g8667 [b8667 H8667]].
 unfold joint_update_expr_8668.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8669 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8332)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8668))).
Lemma joint_update_ready_8669 old :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8668 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8669.
Proof.
 intros [g8332 [b8332 H8332]].
 intros [g8668 [b8668 H8668]].
 unfold joint_update_expr_8669.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8670 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8330)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8669))).
Lemma joint_update_ready_8670 old :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8669 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8670.
Proof.
 intros [g8330 [b8330 H8330]].
 intros [g8669 [b8669 H8669]].
 unfold joint_update_expr_8670.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8671 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8328)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8670))).
Lemma joint_update_ready_8671 old :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8670 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8671.
Proof.
 intros [g8328 [b8328 H8328]].
 intros [g8670 [b8670 H8670]].
 unfold joint_update_expr_8671.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8672 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8326)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8671))).
Lemma joint_update_ready_8672 old :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8671 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8672.
Proof.
 intros [g8326 [b8326 H8326]].
 intros [g8671 [b8671 H8671]].
 unfold joint_update_expr_8672.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8673 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8324)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8672))).
Lemma joint_update_ready_8673 old :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8672 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8673.
Proof.
 intros [g8324 [b8324 H8324]].
 intros [g8672 [b8672 H8672]].
 unfold joint_update_expr_8673.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8674 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8322)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8673))).
Lemma joint_update_ready_8674 old :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8673 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8674.
Proof.
 intros [g8322 [b8322 H8322]].
 intros [g8673 [b8673 H8673]].
 unfold joint_update_expr_8674.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8675 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8320)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8674))).
Lemma joint_update_ready_8675 old :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8674 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8675.
Proof.
 intros [g8320 [b8320 H8320]].
 intros [g8674 [b8674 H8674]].
 unfold joint_update_expr_8675.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8676 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8318)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8675))).
Lemma joint_update_ready_8676 old :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8675 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8676.
Proof.
 intros [g8318 [b8318 H8318]].
 intros [g8675 [b8675 H8675]].
 unfold joint_update_expr_8676.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8677 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8316)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8676))).
Lemma joint_update_ready_8677 old :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8676 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8677.
Proof.
 intros [g8316 [b8316 H8316]].
 intros [g8676 [b8676 H8676]].
 unfold joint_update_expr_8677.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8678 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8314)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8677))).
Lemma joint_update_ready_8678 old :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8677 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8678.
Proof.
 intros [g8314 [b8314 H8314]].
 intros [g8677 [b8677 H8677]].
 unfold joint_update_expr_8678.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8679 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8312)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8678))).
Lemma joint_update_ready_8679 old :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8678 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8679.
Proof.
 intros [g8312 [b8312 H8312]].
 intros [g8678 [b8678 H8678]].
 unfold joint_update_expr_8679.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8680 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8310)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8679))).
Lemma joint_update_ready_8680 old :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8679 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8680.
Proof.
 intros [g8310 [b8310 H8310]].
 intros [g8679 [b8679 H8679]].
 unfold joint_update_expr_8680.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8681 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8308)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8680))).
Lemma joint_update_ready_8681 old :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8680 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8681.
Proof.
 intros [g8308 [b8308 H8308]].
 intros [g8680 [b8680 H8680]].
 unfold joint_update_expr_8681.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8682 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8306)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8681))).
Lemma joint_update_ready_8682 old :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8681 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8682.
Proof.
 intros [g8306 [b8306 H8306]].
 intros [g8681 [b8681 H8681]].
 unfold joint_update_expr_8682.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8683 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8304)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8682))).
Lemma joint_update_ready_8683 old :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8682 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8683.
Proof.
 intros [g8304 [b8304 H8304]].
 intros [g8682 [b8682 H8682]].
 unfold joint_update_expr_8683.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8684 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8302)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8683))).
Lemma joint_update_ready_8684 old :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8683 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8684.
Proof.
 intros [g8302 [b8302 H8302]].
 intros [g8683 [b8683 H8683]].
 unfold joint_update_expr_8684.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8685 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8300)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8684))).
Lemma joint_update_ready_8685 old :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8684 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8685.
Proof.
 intros [g8300 [b8300 H8300]].
 intros [g8684 [b8684 H8684]].
 unfold joint_update_expr_8685.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8686 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8298)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8685))).
Lemma joint_update_ready_8686 old :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8685 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8686.
Proof.
 intros [g8298 [b8298 H8298]].
 intros [g8685 [b8685 H8685]].
 unfold joint_update_expr_8686.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8687 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8296)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8686))).
Lemma joint_update_ready_8687 old :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8686 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8687.
Proof.
 intros [g8296 [b8296 H8296]].
 intros [g8686 [b8686 H8686]].
 unfold joint_update_expr_8687.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8688 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8294)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8687))).
Lemma joint_update_ready_8688 old :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8687 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8688.
Proof.
 intros [g8294 [b8294 H8294]].
 intros [g8687 [b8687 H8687]].
 unfold joint_update_expr_8688.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8689 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8292)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8688))).
Lemma joint_update_ready_8689 old :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8688 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8689.
Proof.
 intros [g8292 [b8292 H8292]].
 intros [g8688 [b8688 H8688]].
 unfold joint_update_expr_8689.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8690 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8290)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8689))).
Lemma joint_update_ready_8690 old :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8689 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8690.
Proof.
 intros [g8290 [b8290 H8290]].
 intros [g8689 [b8689 H8689]].
 unfold joint_update_expr_8690.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8691 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8288)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8690))).
Lemma joint_update_ready_8691 old :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8690 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8691.
Proof.
 intros [g8288 [b8288 H8288]].
 intros [g8690 [b8690 H8690]].
 unfold joint_update_expr_8691.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8692 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8286)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8691))).
Lemma joint_update_ready_8692 old :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8691 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8692.
Proof.
 intros [g8286 [b8286 H8286]].
 intros [g8691 [b8691 H8691]].
 unfold joint_update_expr_8692.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8693 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8284)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8692))).
Lemma joint_update_ready_8693 old :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8692 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8693.
Proof.
 intros [g8284 [b8284 H8284]].
 intros [g8692 [b8692 H8692]].
 unfold joint_update_expr_8693.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8694 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8282)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8693))).
Lemma joint_update_ready_8694 old :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8693 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8694.
Proof.
 intros [g8282 [b8282 H8282]].
 intros [g8693 [b8693 H8693]].
 unfold joint_update_expr_8694.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8695 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8280)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8694))).
Lemma joint_update_ready_8695 old :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8694 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8695.
Proof.
 intros [g8280 [b8280 H8280]].
 intros [g8694 [b8694 H8694]].
 unfold joint_update_expr_8695.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8696 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8278)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8695))).
Lemma joint_update_ready_8696 old :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8695 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8696.
Proof.
 intros [g8278 [b8278 H8278]].
 intros [g8695 [b8695 H8695]].
 unfold joint_update_expr_8696.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8697 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8276)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8696))).
Lemma joint_update_ready_8697 old :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8696 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8697.
Proof.
 intros [g8276 [b8276 H8276]].
 intros [g8696 [b8696 H8696]].
 unfold joint_update_expr_8697.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8698 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8274)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8697))).
Lemma joint_update_ready_8698 old :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8697 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8698.
Proof.
 intros [g8274 [b8274 H8274]].
 intros [g8697 [b8697 H8697]].
 unfold joint_update_expr_8698.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8699 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8272)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8698))).
Lemma joint_update_ready_8699 old :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8698 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8699.
Proof.
 intros [g8272 [b8272 H8272]].
 intros [g8698 [b8698 H8698]].
 unfold joint_update_expr_8699.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8700 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8270)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8699))).
Lemma joint_update_ready_8700 old :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8699 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8700.
Proof.
 intros [g8270 [b8270 H8270]].
 intros [g8699 [b8699 H8699]].
 unfold joint_update_expr_8700.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8701 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8268)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8700))).
Lemma joint_update_ready_8701 old :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8700 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8701.
Proof.
 intros [g8268 [b8268 H8268]].
 intros [g8700 [b8700 H8700]].
 unfold joint_update_expr_8701.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8702 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8266)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8701))).
Lemma joint_update_ready_8702 old :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8701 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8702.
Proof.
 intros [g8266 [b8266 H8266]].
 intros [g8701 [b8701 H8701]].
 unfold joint_update_expr_8702.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8703 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8264)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8702))).
Lemma joint_update_ready_8703 old :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8702 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8703.
Proof.
 intros [g8264 [b8264 H8264]].
 intros [g8702 [b8702 H8702]].
 unfold joint_update_expr_8703.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8802 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8360)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Econst VarOrder.T (Fuint 2) [::false; false])).
Lemma joint_update_ready_8802 old :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8802.
Proof.
 intros [g8360 [b8360 H8360]].
 unfold joint_update_expr_8802.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8803 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8358)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8802))).
Lemma joint_update_ready_8803 old :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8802 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8803.
Proof.
 intros [g8358 [b8358 H8358]].
 intros [g8802 [b8802 H8802]].
 unfold joint_update_expr_8803.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8804 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8356)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8803))).
Lemma joint_update_ready_8804 old :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8803 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8804.
Proof.
 intros [g8356 [b8356 H8356]].
 intros [g8803 [b8803 H8803]].
 unfold joint_update_expr_8804.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8805 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8354)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8804))).
Lemma joint_update_ready_8805 old :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8804 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8805.
Proof.
 intros [g8354 [b8354 H8354]].
 intros [g8804 [b8804 H8804]].
 unfold joint_update_expr_8805.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8806 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8352)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8805))).
Lemma joint_update_ready_8806 old :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8805 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8806.
Proof.
 intros [g8352 [b8352 H8352]].
 intros [g8805 [b8805 H8805]].
 unfold joint_update_expr_8806.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8807 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8350)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8806))).
Lemma joint_update_ready_8807 old :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8806 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8807.
Proof.
 intros [g8350 [b8350 H8350]].
 intros [g8806 [b8806 H8806]].
 unfold joint_update_expr_8807.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8808 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8348)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8807))).
Lemma joint_update_ready_8808 old :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8807 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8808.
Proof.
 intros [g8348 [b8348 H8348]].
 intros [g8807 [b8807 H8807]].
 unfold joint_update_expr_8808.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8809 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8346)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8808))).
Lemma joint_update_ready_8809 old :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8808 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8809.
Proof.
 intros [g8346 [b8346 H8346]].
 intros [g8808 [b8808 H8808]].
 unfold joint_update_expr_8809.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8810 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8344)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8809))).
Lemma joint_update_ready_8810 old :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8809 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8810.
Proof.
 intros [g8344 [b8344 H8344]].
 intros [g8809 [b8809 H8809]].
 unfold joint_update_expr_8810.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8811 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8342)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8810))).
Lemma joint_update_ready_8811 old :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8810 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8811.
Proof.
 intros [g8342 [b8342 H8342]].
 intros [g8810 [b8810 H8810]].
 unfold joint_update_expr_8811.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8812 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8340)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8811))).
Lemma joint_update_ready_8812 old :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8811 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8812.
Proof.
 intros [g8340 [b8340 H8340]].
 intros [g8811 [b8811 H8811]].
 unfold joint_update_expr_8812.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8813 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8338)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8812))).
Lemma joint_update_ready_8813 old :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8812 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8813.
Proof.
 intros [g8338 [b8338 H8338]].
 intros [g8812 [b8812 H8812]].
 unfold joint_update_expr_8813.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8814 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8336)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8813))).
Lemma joint_update_ready_8814 old :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8813 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8814.
Proof.
 intros [g8336 [b8336 H8336]].
 intros [g8813 [b8813 H8813]].
 unfold joint_update_expr_8814.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8815 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8334)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8814))).
Lemma joint_update_ready_8815 old :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8814 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8815.
Proof.
 intros [g8334 [b8334 H8334]].
 intros [g8814 [b8814 H8814]].
 unfold joint_update_expr_8815.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8816 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8332)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8815))).
Lemma joint_update_ready_8816 old :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8815 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8816.
Proof.
 intros [g8332 [b8332 H8332]].
 intros [g8815 [b8815 H8815]].
 unfold joint_update_expr_8816.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8817 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8330)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8816))).
Lemma joint_update_ready_8817 old :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8816 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8817.
Proof.
 intros [g8330 [b8330 H8330]].
 intros [g8816 [b8816 H8816]].
 unfold joint_update_expr_8817.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8818 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8328)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8817))).
Lemma joint_update_ready_8818 old :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8817 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8818.
Proof.
 intros [g8328 [b8328 H8328]].
 intros [g8817 [b8817 H8817]].
 unfold joint_update_expr_8818.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8819 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8326)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8818))).
Lemma joint_update_ready_8819 old :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8818 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8819.
Proof.
 intros [g8326 [b8326 H8326]].
 intros [g8818 [b8818 H8818]].
 unfold joint_update_expr_8819.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8820 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8324)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8819))).
Lemma joint_update_ready_8820 old :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8819 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8820.
Proof.
 intros [g8324 [b8324 H8324]].
 intros [g8819 [b8819 H8819]].
 unfold joint_update_expr_8820.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8821 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8322)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8820))).
Lemma joint_update_ready_8821 old :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8820 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8821.
Proof.
 intros [g8322 [b8322 H8322]].
 intros [g8820 [b8820 H8820]].
 unfold joint_update_expr_8821.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8822 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8320)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8821))).
Lemma joint_update_ready_8822 old :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8821 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8822.
Proof.
 intros [g8320 [b8320 H8320]].
 intros [g8821 [b8821 H8821]].
 unfold joint_update_expr_8822.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8823 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8318)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8822))).
Lemma joint_update_ready_8823 old :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8822 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8823.
Proof.
 intros [g8318 [b8318 H8318]].
 intros [g8822 [b8822 H8822]].
 unfold joint_update_expr_8823.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8824 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8316)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8823))).
Lemma joint_update_ready_8824 old :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8823 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8824.
Proof.
 intros [g8316 [b8316 H8316]].
 intros [g8823 [b8823 H8823]].
 unfold joint_update_expr_8824.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8825 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8314)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8824))).
Lemma joint_update_ready_8825 old :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8824 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8825.
Proof.
 intros [g8314 [b8314 H8314]].
 intros [g8824 [b8824 H8824]].
 unfold joint_update_expr_8825.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8826 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8312)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8825))).
Lemma joint_update_ready_8826 old :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8825 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8826.
Proof.
 intros [g8312 [b8312 H8312]].
 intros [g8825 [b8825 H8825]].
 unfold joint_update_expr_8826.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8827 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8310)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8826))).
Lemma joint_update_ready_8827 old :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8826 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8827.
Proof.
 intros [g8310 [b8310 H8310]].
 intros [g8826 [b8826 H8826]].
 unfold joint_update_expr_8827.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8828 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8308)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8827))).
Lemma joint_update_ready_8828 old :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8827 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8828.
Proof.
 intros [g8308 [b8308 H8308]].
 intros [g8827 [b8827 H8827]].
 unfold joint_update_expr_8828.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8829 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8306)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8828))).
Lemma joint_update_ready_8829 old :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8828 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8829.
Proof.
 intros [g8306 [b8306 H8306]].
 intros [g8828 [b8828 H8828]].
 unfold joint_update_expr_8829.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8830 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8304)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8829))).
Lemma joint_update_ready_8830 old :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8829 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8830.
Proof.
 intros [g8304 [b8304 H8304]].
 intros [g8829 [b8829 H8829]].
 unfold joint_update_expr_8830.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8831 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8302)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8830))).
Lemma joint_update_ready_8831 old :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8830 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8831.
Proof.
 intros [g8302 [b8302 H8302]].
 intros [g8830 [b8830 H8830]].
 unfold joint_update_expr_8831.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8832 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8300)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8831))).
Lemma joint_update_ready_8832 old :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8831 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8832.
Proof.
 intros [g8300 [b8300 H8300]].
 intros [g8831 [b8831 H8831]].
 unfold joint_update_expr_8832.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8833 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8298)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8832))).
Lemma joint_update_ready_8833 old :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8832 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8833.
Proof.
 intros [g8298 [b8298 H8298]].
 intros [g8832 [b8832 H8832]].
 unfold joint_update_expr_8833.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8834 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8296)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8833))).
Lemma joint_update_ready_8834 old :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8833 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8834.
Proof.
 intros [g8296 [b8296 H8296]].
 intros [g8833 [b8833 H8833]].
 unfold joint_update_expr_8834.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8835 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8294)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8834))).
Lemma joint_update_ready_8835 old :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8834 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8835.
Proof.
 intros [g8294 [b8294 H8294]].
 intros [g8834 [b8834 H8834]].
 unfold joint_update_expr_8835.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8836 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8292)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8835))).
Lemma joint_update_ready_8836 old :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8835 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8836.
Proof.
 intros [g8292 [b8292 H8292]].
 intros [g8835 [b8835 H8835]].
 unfold joint_update_expr_8836.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8837 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8290)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8836))).
Lemma joint_update_ready_8837 old :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8836 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8837.
Proof.
 intros [g8290 [b8290 H8290]].
 intros [g8836 [b8836 H8836]].
 unfold joint_update_expr_8837.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8838 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8288)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8837))).
Lemma joint_update_ready_8838 old :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8837 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8838.
Proof.
 intros [g8288 [b8288 H8288]].
 intros [g8837 [b8837 H8837]].
 unfold joint_update_expr_8838.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8839 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8286)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8838))).
Lemma joint_update_ready_8839 old :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8838 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8839.
Proof.
 intros [g8286 [b8286 H8286]].
 intros [g8838 [b8838 H8838]].
 unfold joint_update_expr_8839.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8840 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8284)) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8839))).
Lemma joint_update_ready_8840 old :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8839 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8840.
Proof.
 intros [g8284 [b8284 H8284]].
 intros [g8839 [b8839 H8839]].
 unfold joint_update_expr_8840.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8841 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8282)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8840))).
Lemma joint_update_ready_8841 old :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8840 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8841.
Proof.
 intros [g8282 [b8282 H8282]].
 intros [g8840 [b8840 H8840]].
 unfold joint_update_expr_8841.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8842 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8280)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8841))).
Lemma joint_update_ready_8842 old :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8841 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8842.
Proof.
 intros [g8280 [b8280 H8280]].
 intros [g8841 [b8841 H8841]].
 unfold joint_update_expr_8842.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8843 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8278)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8842))).
Lemma joint_update_ready_8843 old :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8842 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8843.
Proof.
 intros [g8278 [b8278 H8278]].
 intros [g8842 [b8842 H8842]].
 unfold joint_update_expr_8843.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8844 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8276)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8843))).
Lemma joint_update_ready_8844 old :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8843 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8844.
Proof.
 intros [g8276 [b8276 H8276]].
 intros [g8843 [b8843 H8843]].
 unfold joint_update_expr_8844.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8845 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8274)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8844))).
Lemma joint_update_ready_8845 old :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8844 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8845.
Proof.
 intros [g8274 [b8274 H8274]].
 intros [g8844 [b8844 H8844]].
 unfold joint_update_expr_8845.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8846 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8272)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8845))).
Lemma joint_update_ready_8846 old :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8845 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8846.
Proof.
 intros [g8272 [b8272 H8272]].
 intros [g8845 [b8845 H8845]].
 unfold joint_update_expr_8846.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8847 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8270)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8846))).
Lemma joint_update_ready_8847 old :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8846 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8847.
Proof.
 intros [g8270 [b8270 H8270]].
 intros [g8846 [b8846 H8846]].
 unfold joint_update_expr_8847.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8848 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8268)) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8847))).
Lemma joint_update_ready_8848 old :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8847 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8848.
Proof.
 intros [g8268 [b8268 H8268]].
 intros [g8847 [b8847 H8847]].
 unfold joint_update_expr_8848.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8849 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8266)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8848))).
Lemma joint_update_ready_8849 old :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8848 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8849.
Proof.
 intros [g8266 [b8266 H8266]].
 intros [g8848 [b8848 H8848]].
 unfold joint_update_expr_8849.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8850 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8264)) (@Econst VarOrder.T (Fuint 2) [::false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8849))).
Lemma joint_update_ready_8850 old :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8849 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8850.
Proof.
 intros [g8264 [b8264 H8264]].
 intros [g8849 [b8849 H8849]].
 unfold joint_update_expr_8850.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8851 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8360)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma joint_update_ready_8851 old :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8851.
Proof.
 intros [g8360 [b8360 H8360]].
 unfold joint_update_expr_8851.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8852 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8358)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8851))).
Lemma joint_update_ready_8852 old :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8851 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8852.
Proof.
 intros [g8358 [b8358 H8358]].
 intros [g8851 [b8851 H8851]].
 unfold joint_update_expr_8852.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8853 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8356)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8852))).
Lemma joint_update_ready_8853 old :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8852 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8853.
Proof.
 intros [g8356 [b8356 H8356]].
 intros [g8852 [b8852 H8852]].
 unfold joint_update_expr_8853.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8854 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8354)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8853))).
Lemma joint_update_ready_8854 old :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8853 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8854.
Proof.
 intros [g8354 [b8354 H8354]].
 intros [g8853 [b8853 H8853]].
 unfold joint_update_expr_8854.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8855 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8352)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8854))).
Lemma joint_update_ready_8855 old :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8854 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8855.
Proof.
 intros [g8352 [b8352 H8352]].
 intros [g8854 [b8854 H8854]].
 unfold joint_update_expr_8855.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8856 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8350)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8855))).
Lemma joint_update_ready_8856 old :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8855 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8856.
Proof.
 intros [g8350 [b8350 H8350]].
 intros [g8855 [b8855 H8855]].
 unfold joint_update_expr_8856.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8857 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8348)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8856))).
Lemma joint_update_ready_8857 old :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8856 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8857.
Proof.
 intros [g8348 [b8348 H8348]].
 intros [g8856 [b8856 H8856]].
 unfold joint_update_expr_8857.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8858 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8346)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8857))).
Lemma joint_update_ready_8858 old :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8857 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8858.
Proof.
 intros [g8346 [b8346 H8346]].
 intros [g8857 [b8857 H8857]].
 unfold joint_update_expr_8858.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8859 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8344)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8858))).
Lemma joint_update_ready_8859 old :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8858 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8859.
Proof.
 intros [g8344 [b8344 H8344]].
 intros [g8858 [b8858 H8858]].
 unfold joint_update_expr_8859.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8860 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8342)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8859))).
Lemma joint_update_ready_8860 old :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8859 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8860.
Proof.
 intros [g8342 [b8342 H8342]].
 intros [g8859 [b8859 H8859]].
 unfold joint_update_expr_8860.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8861 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8340)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8860))).
Lemma joint_update_ready_8861 old :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8860 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8861.
Proof.
 intros [g8340 [b8340 H8340]].
 intros [g8860 [b8860 H8860]].
 unfold joint_update_expr_8861.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8862 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8338)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8861))).
Lemma joint_update_ready_8862 old :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8861 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8862.
Proof.
 intros [g8338 [b8338 H8338]].
 intros [g8861 [b8861 H8861]].
 unfold joint_update_expr_8862.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8863 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8336)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8862))).
Lemma joint_update_ready_8863 old :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8862 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8863.
Proof.
 intros [g8336 [b8336 H8336]].
 intros [g8862 [b8862 H8862]].
 unfold joint_update_expr_8863.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8864 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8334)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8863))).
Lemma joint_update_ready_8864 old :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8863 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8864.
Proof.
 intros [g8334 [b8334 H8334]].
 intros [g8863 [b8863 H8863]].
 unfold joint_update_expr_8864.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8865 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8332)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8864))).
Lemma joint_update_ready_8865 old :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8864 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8865.
Proof.
 intros [g8332 [b8332 H8332]].
 intros [g8864 [b8864 H8864]].
 unfold joint_update_expr_8865.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8866 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8330)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8865))).
Lemma joint_update_ready_8866 old :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8865 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8866.
Proof.
 intros [g8330 [b8330 H8330]].
 intros [g8865 [b8865 H8865]].
 unfold joint_update_expr_8866.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8867 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8328)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8866))).
Lemma joint_update_ready_8867 old :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8866 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8867.
Proof.
 intros [g8328 [b8328 H8328]].
 intros [g8866 [b8866 H8866]].
 unfold joint_update_expr_8867.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8868 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8326)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8867))).
Lemma joint_update_ready_8868 old :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8867 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8868.
Proof.
 intros [g8326 [b8326 H8326]].
 intros [g8867 [b8867 H8867]].
 unfold joint_update_expr_8868.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8869 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8324)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8868))).
Lemma joint_update_ready_8869 old :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8868 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8869.
Proof.
 intros [g8324 [b8324 H8324]].
 intros [g8868 [b8868 H8868]].
 unfold joint_update_expr_8869.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8870 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8322)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8869))).
Lemma joint_update_ready_8870 old :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8869 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8870.
Proof.
 intros [g8322 [b8322 H8322]].
 intros [g8869 [b8869 H8869]].
 unfold joint_update_expr_8870.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8871 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8320)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8870))).
Lemma joint_update_ready_8871 old :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8870 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8871.
Proof.
 intros [g8320 [b8320 H8320]].
 intros [g8870 [b8870 H8870]].
 unfold joint_update_expr_8871.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8872 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8318)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8871))).
Lemma joint_update_ready_8872 old :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8871 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8872.
Proof.
 intros [g8318 [b8318 H8318]].
 intros [g8871 [b8871 H8871]].
 unfold joint_update_expr_8872.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8873 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8316)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8872))).
Lemma joint_update_ready_8873 old :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8872 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8873.
Proof.
 intros [g8316 [b8316 H8316]].
 intros [g8872 [b8872 H8872]].
 unfold joint_update_expr_8873.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8874 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8314)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8873))).
Lemma joint_update_ready_8874 old :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8873 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8874.
Proof.
 intros [g8314 [b8314 H8314]].
 intros [g8873 [b8873 H8873]].
 unfold joint_update_expr_8874.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8875 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8312)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8874))).
Lemma joint_update_ready_8875 old :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8874 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8875.
Proof.
 intros [g8312 [b8312 H8312]].
 intros [g8874 [b8874 H8874]].
 unfold joint_update_expr_8875.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8876 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8310)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8875))).
Lemma joint_update_ready_8876 old :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8875 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8876.
Proof.
 intros [g8310 [b8310 H8310]].
 intros [g8875 [b8875 H8875]].
 unfold joint_update_expr_8876.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8877 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8308)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8876))).
Lemma joint_update_ready_8877 old :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8876 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8877.
Proof.
 intros [g8308 [b8308 H8308]].
 intros [g8876 [b8876 H8876]].
 unfold joint_update_expr_8877.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8878 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8306)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8877))).
Lemma joint_update_ready_8878 old :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8877 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8878.
Proof.
 intros [g8306 [b8306 H8306]].
 intros [g8877 [b8877 H8877]].
 unfold joint_update_expr_8878.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8879 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8304)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8878))).
Lemma joint_update_ready_8879 old :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8878 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8879.
Proof.
 intros [g8304 [b8304 H8304]].
 intros [g8878 [b8878 H8878]].
 unfold joint_update_expr_8879.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8880 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8302)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8879))).
Lemma joint_update_ready_8880 old :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8879 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8880.
Proof.
 intros [g8302 [b8302 H8302]].
 intros [g8879 [b8879 H8879]].
 unfold joint_update_expr_8880.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8881 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8300)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8880))).
Lemma joint_update_ready_8881 old :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8880 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8881.
Proof.
 intros [g8300 [b8300 H8300]].
 intros [g8880 [b8880 H8880]].
 unfold joint_update_expr_8881.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8882 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8298)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8881))).
Lemma joint_update_ready_8882 old :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8881 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8882.
Proof.
 intros [g8298 [b8298 H8298]].
 intros [g8881 [b8881 H8881]].
 unfold joint_update_expr_8882.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8883 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8296)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8882))).
Lemma joint_update_ready_8883 old :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8882 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8883.
Proof.
 intros [g8296 [b8296 H8296]].
 intros [g8882 [b8882 H8882]].
 unfold joint_update_expr_8883.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8884 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8294)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8883))).
Lemma joint_update_ready_8884 old :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8883 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8884.
Proof.
 intros [g8294 [b8294 H8294]].
 intros [g8883 [b8883 H8883]].
 unfold joint_update_expr_8884.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8885 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8292)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8884))).
Lemma joint_update_ready_8885 old :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8884 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8885.
Proof.
 intros [g8292 [b8292 H8292]].
 intros [g8884 [b8884 H8884]].
 unfold joint_update_expr_8885.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8886 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8290)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8885))).
Lemma joint_update_ready_8886 old :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8885 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8886.
Proof.
 intros [g8290 [b8290 H8290]].
 intros [g8885 [b8885 H8885]].
 unfold joint_update_expr_8886.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8887 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8288)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8886))).
Lemma joint_update_ready_8887 old :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8886 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8887.
Proof.
 intros [g8288 [b8288 H8288]].
 intros [g8886 [b8886 H8886]].
 unfold joint_update_expr_8887.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8888 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8286)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8887))).
Lemma joint_update_ready_8888 old :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8887 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8888.
Proof.
 intros [g8286 [b8286 H8286]].
 intros [g8887 [b8887 H8887]].
 unfold joint_update_expr_8888.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8889 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8284)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8888))).
Lemma joint_update_ready_8889 old :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8888 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8889.
Proof.
 intros [g8284 [b8284 H8284]].
 intros [g8888 [b8888 H8888]].
 unfold joint_update_expr_8889.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8890 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8282)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8889))).
Lemma joint_update_ready_8890 old :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8889 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8890.
Proof.
 intros [g8282 [b8282 H8282]].
 intros [g8889 [b8889 H8889]].
 unfold joint_update_expr_8890.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8891 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8280)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8890))).
Lemma joint_update_ready_8891 old :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8890 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8891.
Proof.
 intros [g8280 [b8280 H8280]].
 intros [g8890 [b8890 H8890]].
 unfold joint_update_expr_8891.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8892 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8278)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8891))).
Lemma joint_update_ready_8892 old :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8891 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8892.
Proof.
 intros [g8278 [b8278 H8278]].
 intros [g8891 [b8891 H8891]].
 unfold joint_update_expr_8892.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8893 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8276)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8892))).
Lemma joint_update_ready_8893 old :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8892 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8893.
Proof.
 intros [g8276 [b8276 H8276]].
 intros [g8892 [b8892 H8892]].
 unfold joint_update_expr_8893.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8894 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8274)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8893))).
Lemma joint_update_ready_8894 old :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8893 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8894.
Proof.
 intros [g8274 [b8274 H8274]].
 intros [g8893 [b8893 H8893]].
 unfold joint_update_expr_8894.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8895 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8272)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8894))).
Lemma joint_update_ready_8895 old :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8894 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8895.
Proof.
 intros [g8272 [b8272 H8272]].
 intros [g8894 [b8894 H8894]].
 unfold joint_update_expr_8895.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8896 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8270)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8895))).
Lemma joint_update_ready_8896 old :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8895 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8896.
Proof.
 intros [g8270 [b8270 H8270]].
 intros [g8895 [b8895 H8895]].
 unfold joint_update_expr_8896.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8897 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8268)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8896))).
Lemma joint_update_ready_8897 old :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8896 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8897.
Proof.
 intros [g8268 [b8268 H8268]].
 intros [g8896 [b8896 H8896]].
 unfold joint_update_expr_8897.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8898 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8266)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8897))).
Lemma joint_update_ready_8898 old :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8897 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8898.
Proof.
 intros [g8266 [b8266 H8266]].
 intros [g8897 [b8897 H8897]].
 unfold joint_update_expr_8898.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8899 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8264)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8898))).
Lemma joint_update_ready_8899 old :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8898 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8899.
Proof.
 intros [g8264 [b8264 H8264]].
 intros [g8898 [b8898 H8898]].
 unfold joint_update_expr_8899.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8900 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8360)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Econst VarOrder.T (Fuint 3) [::false; false; false])).
Lemma joint_update_ready_8900 old :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8900.
Proof.
 intros [g8360 [b8360 H8360]].
 unfold joint_update_expr_8900.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8901 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8358)) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8900))).
Lemma joint_update_ready_8901 old :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8900 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8901.
Proof.
 intros [g8358 [b8358 H8358]].
 intros [g8900 [b8900 H8900]].
 unfold joint_update_expr_8901.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8902 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8356)) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8901))).
Lemma joint_update_ready_8902 old :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8901 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8902.
Proof.
 intros [g8356 [b8356 H8356]].
 intros [g8901 [b8901 H8901]].
 unfold joint_update_expr_8902.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8903 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8354)) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8902))).
Lemma joint_update_ready_8903 old :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8902 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8903.
Proof.
 intros [g8354 [b8354 H8354]].
 intros [g8902 [b8902 H8902]].
 unfold joint_update_expr_8903.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8904 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8352)) (@Econst VarOrder.T (Fuint 3) [::true; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8903))).
Lemma joint_update_ready_8904 old :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8903 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8904.
Proof.
 intros [g8352 [b8352 H8352]].
 intros [g8903 [b8903 H8903]].
 unfold joint_update_expr_8904.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8905 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8350)) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8904))).
Lemma joint_update_ready_8905 old :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8904 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8905.
Proof.
 intros [g8350 [b8350 H8350]].
 intros [g8904 [b8904 H8904]].
 unfold joint_update_expr_8905.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8906 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8348)) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8905))).
Lemma joint_update_ready_8906 old :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8905 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8906.
Proof.
 intros [g8348 [b8348 H8348]].
 intros [g8905 [b8905 H8905]].
 unfold joint_update_expr_8906.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8907 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8346)) (@Econst VarOrder.T (Fuint 3) [::true; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8906))).
Lemma joint_update_ready_8907 old :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8906 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8907.
Proof.
 intros [g8346 [b8346 H8346]].
 intros [g8906 [b8906 H8906]].
 unfold joint_update_expr_8907.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8908 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8344)) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8907))).
Lemma joint_update_ready_8908 old :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8907 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8908.
Proof.
 intros [g8344 [b8344 H8344]].
 intros [g8907 [b8907 H8907]].
 unfold joint_update_expr_8908.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8909 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8342)) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8908))).
Lemma joint_update_ready_8909 old :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8908 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8909.
Proof.
 intros [g8342 [b8342 H8342]].
 intros [g8908 [b8908 H8908]].
 unfold joint_update_expr_8909.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8910 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8340)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8909))).
Lemma joint_update_ready_8910 old :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8909 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8910.
Proof.
 intros [g8340 [b8340 H8340]].
 intros [g8909 [b8909 H8909]].
 unfold joint_update_expr_8910.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8911 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8338)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8910))).
Lemma joint_update_ready_8911 old :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8910 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8911.
Proof.
 intros [g8338 [b8338 H8338]].
 intros [g8910 [b8910 H8910]].
 unfold joint_update_expr_8911.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8912 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8336)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8911))).
Lemma joint_update_ready_8912 old :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8911 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8912.
Proof.
 intros [g8336 [b8336 H8336]].
 intros [g8911 [b8911 H8911]].
 unfold joint_update_expr_8912.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8913 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8334)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8912))).
Lemma joint_update_ready_8913 old :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8912 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8913.
Proof.
 intros [g8334 [b8334 H8334]].
 intros [g8912 [b8912 H8912]].
 unfold joint_update_expr_8913.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8914 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8332)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8913))).
Lemma joint_update_ready_8914 old :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8913 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8914.
Proof.
 intros [g8332 [b8332 H8332]].
 intros [g8913 [b8913 H8913]].
 unfold joint_update_expr_8914.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8915 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8330)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8914))).
Lemma joint_update_ready_8915 old :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8914 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8915.
Proof.
 intros [g8330 [b8330 H8330]].
 intros [g8914 [b8914 H8914]].
 unfold joint_update_expr_8915.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8916 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8328)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8915))).
Lemma joint_update_ready_8916 old :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8915 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8916.
Proof.
 intros [g8328 [b8328 H8328]].
 intros [g8915 [b8915 H8915]].
 unfold joint_update_expr_8916.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8917 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8326)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8916))).
Lemma joint_update_ready_8917 old :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8916 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8917.
Proof.
 intros [g8326 [b8326 H8326]].
 intros [g8916 [b8916 H8916]].
 unfold joint_update_expr_8917.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8918 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8324)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8917))).
Lemma joint_update_ready_8918 old :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8917 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8918.
Proof.
 intros [g8324 [b8324 H8324]].
 intros [g8917 [b8917 H8917]].
 unfold joint_update_expr_8918.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8919 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8322)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8918))).
Lemma joint_update_ready_8919 old :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8918 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8919.
Proof.
 intros [g8322 [b8322 H8322]].
 intros [g8918 [b8918 H8918]].
 unfold joint_update_expr_8919.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8920 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8320)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8919))).
Lemma joint_update_ready_8920 old :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8919 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8920.
Proof.
 intros [g8320 [b8320 H8320]].
 intros [g8919 [b8919 H8919]].
 unfold joint_update_expr_8920.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8921 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8318)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8920))).
Lemma joint_update_ready_8921 old :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8920 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8921.
Proof.
 intros [g8318 [b8318 H8318]].
 intros [g8920 [b8920 H8920]].
 unfold joint_update_expr_8921.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8922 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8316)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8921))).
Lemma joint_update_ready_8922 old :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8921 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8922.
Proof.
 intros [g8316 [b8316 H8316]].
 intros [g8921 [b8921 H8921]].
 unfold joint_update_expr_8922.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8923 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8314)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8922))).
Lemma joint_update_ready_8923 old :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8922 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8923.
Proof.
 intros [g8314 [b8314 H8314]].
 intros [g8922 [b8922 H8922]].
 unfold joint_update_expr_8923.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8924 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8312)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8923))).
Lemma joint_update_ready_8924 old :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8923 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8924.
Proof.
 intros [g8312 [b8312 H8312]].
 intros [g8923 [b8923 H8923]].
 unfold joint_update_expr_8924.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8925 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8310)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8924))).
Lemma joint_update_ready_8925 old :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8924 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8925.
Proof.
 intros [g8310 [b8310 H8310]].
 intros [g8924 [b8924 H8924]].
 unfold joint_update_expr_8925.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8926 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8308)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8925))).
Lemma joint_update_ready_8926 old :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8925 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8926.
Proof.
 intros [g8308 [b8308 H8308]].
 intros [g8925 [b8925 H8925]].
 unfold joint_update_expr_8926.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8927 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8306)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8926))).
Lemma joint_update_ready_8927 old :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8926 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8927.
Proof.
 intros [g8306 [b8306 H8306]].
 intros [g8926 [b8926 H8926]].
 unfold joint_update_expr_8927.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8928 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8304)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8927))).
Lemma joint_update_ready_8928 old :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8927 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8928.
Proof.
 intros [g8304 [b8304 H8304]].
 intros [g8927 [b8927 H8927]].
 unfold joint_update_expr_8928.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8929 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8302)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8928))).
Lemma joint_update_ready_8929 old :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8928 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8929.
Proof.
 intros [g8302 [b8302 H8302]].
 intros [g8928 [b8928 H8928]].
 unfold joint_update_expr_8929.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8930 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8300)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8929))).
Lemma joint_update_ready_8930 old :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8929 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8930.
Proof.
 intros [g8300 [b8300 H8300]].
 intros [g8929 [b8929 H8929]].
 unfold joint_update_expr_8930.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8931 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8298)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8930))).
Lemma joint_update_ready_8931 old :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8930 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8931.
Proof.
 intros [g8298 [b8298 H8298]].
 intros [g8930 [b8930 H8930]].
 unfold joint_update_expr_8931.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8932 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8296)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8931))).
Lemma joint_update_ready_8932 old :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8931 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8932.
Proof.
 intros [g8296 [b8296 H8296]].
 intros [g8931 [b8931 H8931]].
 unfold joint_update_expr_8932.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8933 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8294)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8932))).
Lemma joint_update_ready_8933 old :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8932 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8933.
Proof.
 intros [g8294 [b8294 H8294]].
 intros [g8932 [b8932 H8932]].
 unfold joint_update_expr_8933.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8934 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8292)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8933))).
Lemma joint_update_ready_8934 old :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8933 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8934.
Proof.
 intros [g8292 [b8292 H8292]].
 intros [g8933 [b8933 H8933]].
 unfold joint_update_expr_8934.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8935 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8290)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8934))).
Lemma joint_update_ready_8935 old :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8934 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8935.
Proof.
 intros [g8290 [b8290 H8290]].
 intros [g8934 [b8934 H8934]].
 unfold joint_update_expr_8935.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8936 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8288)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8935))).
Lemma joint_update_ready_8936 old :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8935 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8936.
Proof.
 intros [g8288 [b8288 H8288]].
 intros [g8935 [b8935 H8935]].
 unfold joint_update_expr_8936.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8937 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8286)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8936))).
Lemma joint_update_ready_8937 old :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8936 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8937.
Proof.
 intros [g8286 [b8286 H8286]].
 intros [g8936 [b8936 H8936]].
 unfold joint_update_expr_8937.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8938 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8284)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8937))).
Lemma joint_update_ready_8938 old :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8937 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8938.
Proof.
 intros [g8284 [b8284 H8284]].
 intros [g8937 [b8937 H8937]].
 unfold joint_update_expr_8938.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8939 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8282)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8938))).
Lemma joint_update_ready_8939 old :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8938 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8939.
Proof.
 intros [g8282 [b8282 H8282]].
 intros [g8938 [b8938 H8938]].
 unfold joint_update_expr_8939.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8940 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8280)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8939))).
Lemma joint_update_ready_8940 old :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8939 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8940.
Proof.
 intros [g8280 [b8280 H8280]].
 intros [g8939 [b8939 H8939]].
 unfold joint_update_expr_8940.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8941 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8278)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8940))).
Lemma joint_update_ready_8941 old :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8940 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8941.
Proof.
 intros [g8278 [b8278 H8278]].
 intros [g8940 [b8940 H8940]].
 unfold joint_update_expr_8941.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8942 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8276)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8941))).
Lemma joint_update_ready_8942 old :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8941 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8942.
Proof.
 intros [g8276 [b8276 H8276]].
 intros [g8941 [b8941 H8941]].
 unfold joint_update_expr_8942.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8943 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8274)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8942))).
Lemma joint_update_ready_8943 old :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8942 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8943.
Proof.
 intros [g8274 [b8274 H8274]].
 intros [g8942 [b8942 H8942]].
 unfold joint_update_expr_8943.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8944 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8272)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8943))).
Lemma joint_update_ready_8944 old :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8943 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8944.
Proof.
 intros [g8272 [b8272 H8272]].
 intros [g8943 [b8943 H8943]].
 unfold joint_update_expr_8944.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8945 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8270)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8944))).
Lemma joint_update_ready_8945 old :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8944 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8945.
Proof.
 intros [g8270 [b8270 H8270]].
 intros [g8944 [b8944 H8944]].
 unfold joint_update_expr_8945.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8946 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8268)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8945))).
Lemma joint_update_ready_8946 old :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8945 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8946.
Proof.
 intros [g8268 [b8268 H8268]].
 intros [g8945 [b8945 H8945]].
 unfold joint_update_expr_8946.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8947 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8266)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8946))).
Lemma joint_update_ready_8947 old :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8946 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8947.
Proof.
 intros [g8266 [b8266 H8266]].
 intros [g8946 [b8946 H8946]].
 unfold joint_update_expr_8947.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8948 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8264)) (@Econst VarOrder.T (Fuint 3) [::false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 8947))).
Lemma joint_update_ready_8948 old :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8947 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8948.
Proof.
 intros [g8264 [b8264 H8264]].
 intros [g8947 [b8947 H8947]].
 unfold joint_update_expr_8948.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8949 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8360)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::true])).
Lemma joint_update_ready_8949 old :
 (exists ground bits, VM.find 8360 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8949.
Proof.
 intros [g8360 [b8360 H8360]].
 unfold joint_update_expr_8949.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8950 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8358)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8949))).
Lemma joint_update_ready_8950 old :
 (exists ground bits, VM.find 8358 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8949 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8950.
Proof.
 intros [g8358 [b8358 H8358]].
 intros [g8949 [b8949 H8949]].
 unfold joint_update_expr_8950.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8951 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8356)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8950))).
Lemma joint_update_ready_8951 old :
 (exists ground bits, VM.find 8356 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8950 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8951.
Proof.
 intros [g8356 [b8356 H8356]].
 intros [g8950 [b8950 H8950]].
 unfold joint_update_expr_8951.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8952 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8354)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8951))).
Lemma joint_update_ready_8952 old :
 (exists ground bits, VM.find 8354 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8951 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8952.
Proof.
 intros [g8354 [b8354 H8354]].
 intros [g8951 [b8951 H8951]].
 unfold joint_update_expr_8952.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8953 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8352)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8952))).
Lemma joint_update_ready_8953 old :
 (exists ground bits, VM.find 8352 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8952 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8953.
Proof.
 intros [g8352 [b8352 H8352]].
 intros [g8952 [b8952 H8952]].
 unfold joint_update_expr_8953.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8954 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8350)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8953))).
Lemma joint_update_ready_8954 old :
 (exists ground bits, VM.find 8350 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8953 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8954.
Proof.
 intros [g8350 [b8350 H8350]].
 intros [g8953 [b8953 H8953]].
 unfold joint_update_expr_8954.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8955 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8348)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8954))).
Lemma joint_update_ready_8955 old :
 (exists ground bits, VM.find 8348 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8954 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8955.
Proof.
 intros [g8348 [b8348 H8348]].
 intros [g8954 [b8954 H8954]].
 unfold joint_update_expr_8955.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8956 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8346)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8955))).
Lemma joint_update_ready_8956 old :
 (exists ground bits, VM.find 8346 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8955 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8956.
Proof.
 intros [g8346 [b8346 H8346]].
 intros [g8955 [b8955 H8955]].
 unfold joint_update_expr_8956.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8957 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8344)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8956))).
Lemma joint_update_ready_8957 old :
 (exists ground bits, VM.find 8344 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8956 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8957.
Proof.
 intros [g8344 [b8344 H8344]].
 intros [g8956 [b8956 H8956]].
 unfold joint_update_expr_8957.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8958 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8342)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8957))).
Lemma joint_update_ready_8958 old :
 (exists ground bits, VM.find 8342 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8957 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8958.
Proof.
 intros [g8342 [b8342 H8342]].
 intros [g8957 [b8957 H8957]].
 unfold joint_update_expr_8958.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8959 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8340)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8958))).
Lemma joint_update_ready_8959 old :
 (exists ground bits, VM.find 8340 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8958 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8959.
Proof.
 intros [g8340 [b8340 H8340]].
 intros [g8958 [b8958 H8958]].
 unfold joint_update_expr_8959.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8960 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8338)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8959))).
Lemma joint_update_ready_8960 old :
 (exists ground bits, VM.find 8338 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8959 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8960.
Proof.
 intros [g8338 [b8338 H8338]].
 intros [g8959 [b8959 H8959]].
 unfold joint_update_expr_8960.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8961 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8336)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8960))).
Lemma joint_update_ready_8961 old :
 (exists ground bits, VM.find 8336 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8960 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8961.
Proof.
 intros [g8336 [b8336 H8336]].
 intros [g8960 [b8960 H8960]].
 unfold joint_update_expr_8961.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8962 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8334)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8961))).
Lemma joint_update_ready_8962 old :
 (exists ground bits, VM.find 8334 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8961 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8962.
Proof.
 intros [g8334 [b8334 H8334]].
 intros [g8961 [b8961 H8961]].
 unfold joint_update_expr_8962.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8963 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8332)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8962))).
Lemma joint_update_ready_8963 old :
 (exists ground bits, VM.find 8332 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8962 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8963.
Proof.
 intros [g8332 [b8332 H8332]].
 intros [g8962 [b8962 H8962]].
 unfold joint_update_expr_8963.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8964 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8330)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8963))).
Lemma joint_update_ready_8964 old :
 (exists ground bits, VM.find 8330 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8963 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8964.
Proof.
 intros [g8330 [b8330 H8330]].
 intros [g8963 [b8963 H8963]].
 unfold joint_update_expr_8964.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8965 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8328)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8964))).
Lemma joint_update_ready_8965 old :
 (exists ground bits, VM.find 8328 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8964 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8965.
Proof.
 intros [g8328 [b8328 H8328]].
 intros [g8964 [b8964 H8964]].
 unfold joint_update_expr_8965.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8966 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8326)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8965))).
Lemma joint_update_ready_8966 old :
 (exists ground bits, VM.find 8326 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8965 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8966.
Proof.
 intros [g8326 [b8326 H8326]].
 intros [g8965 [b8965 H8965]].
 unfold joint_update_expr_8966.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8967 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8324)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8966))).
Lemma joint_update_ready_8967 old :
 (exists ground bits, VM.find 8324 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8966 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8967.
Proof.
 intros [g8324 [b8324 H8324]].
 intros [g8966 [b8966 H8966]].
 unfold joint_update_expr_8967.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8968 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8322)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8967))).
Lemma joint_update_ready_8968 old :
 (exists ground bits, VM.find 8322 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8967 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8968.
Proof.
 intros [g8322 [b8322 H8322]].
 intros [g8967 [b8967 H8967]].
 unfold joint_update_expr_8968.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8969 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8320)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8968))).
Lemma joint_update_ready_8969 old :
 (exists ground bits, VM.find 8320 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8968 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8969.
Proof.
 intros [g8320 [b8320 H8320]].
 intros [g8968 [b8968 H8968]].
 unfold joint_update_expr_8969.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8970 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8318)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8969))).
Lemma joint_update_ready_8970 old :
 (exists ground bits, VM.find 8318 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8969 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8970.
Proof.
 intros [g8318 [b8318 H8318]].
 intros [g8969 [b8969 H8969]].
 unfold joint_update_expr_8970.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8971 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8316)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8970))).
Lemma joint_update_ready_8971 old :
 (exists ground bits, VM.find 8316 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8970 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8971.
Proof.
 intros [g8316 [b8316 H8316]].
 intros [g8970 [b8970 H8970]].
 unfold joint_update_expr_8971.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8972 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8314)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8971))).
Lemma joint_update_ready_8972 old :
 (exists ground bits, VM.find 8314 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8971 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8972.
Proof.
 intros [g8314 [b8314 H8314]].
 intros [g8971 [b8971 H8971]].
 unfold joint_update_expr_8972.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8973 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8312)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8972))).
Lemma joint_update_ready_8973 old :
 (exists ground bits, VM.find 8312 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8972 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8973.
Proof.
 intros [g8312 [b8312 H8312]].
 intros [g8972 [b8972 H8972]].
 unfold joint_update_expr_8973.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8974 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8310)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8973))).
Lemma joint_update_ready_8974 old :
 (exists ground bits, VM.find 8310 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8973 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8974.
Proof.
 intros [g8310 [b8310 H8310]].
 intros [g8973 [b8973 H8973]].
 unfold joint_update_expr_8974.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8975 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8308)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8974))).
Lemma joint_update_ready_8975 old :
 (exists ground bits, VM.find 8308 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8974 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8975.
Proof.
 intros [g8308 [b8308 H8308]].
 intros [g8974 [b8974 H8974]].
 unfold joint_update_expr_8975.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8976 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8306)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8975))).
Lemma joint_update_ready_8976 old :
 (exists ground bits, VM.find 8306 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8975 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8976.
Proof.
 intros [g8306 [b8306 H8306]].
 intros [g8975 [b8975 H8975]].
 unfold joint_update_expr_8976.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8977 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8304)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8976))).
Lemma joint_update_ready_8977 old :
 (exists ground bits, VM.find 8304 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8976 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8977.
Proof.
 intros [g8304 [b8304 H8304]].
 intros [g8976 [b8976 H8976]].
 unfold joint_update_expr_8977.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8978 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8302)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8977))).
Lemma joint_update_ready_8978 old :
 (exists ground bits, VM.find 8302 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8977 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8978.
Proof.
 intros [g8302 [b8302 H8302]].
 intros [g8977 [b8977 H8977]].
 unfold joint_update_expr_8978.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8979 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8300)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8978))).
Lemma joint_update_ready_8979 old :
 (exists ground bits, VM.find 8300 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8978 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8979.
Proof.
 intros [g8300 [b8300 H8300]].
 intros [g8978 [b8978 H8978]].
 unfold joint_update_expr_8979.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8980 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8298)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8979))).
Lemma joint_update_ready_8980 old :
 (exists ground bits, VM.find 8298 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8979 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8980.
Proof.
 intros [g8298 [b8298 H8298]].
 intros [g8979 [b8979 H8979]].
 unfold joint_update_expr_8980.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8981 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8296)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8980))).
Lemma joint_update_ready_8981 old :
 (exists ground bits, VM.find 8296 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8980 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8981.
Proof.
 intros [g8296 [b8296 H8296]].
 intros [g8980 [b8980 H8980]].
 unfold joint_update_expr_8981.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8982 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8294)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8981))).
Lemma joint_update_ready_8982 old :
 (exists ground bits, VM.find 8294 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8981 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8982.
Proof.
 intros [g8294 [b8294 H8294]].
 intros [g8981 [b8981 H8981]].
 unfold joint_update_expr_8982.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8983 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8292)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8982))).
Lemma joint_update_ready_8983 old :
 (exists ground bits, VM.find 8292 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8982 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8983.
Proof.
 intros [g8292 [b8292 H8292]].
 intros [g8982 [b8982 H8982]].
 unfold joint_update_expr_8983.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8984 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8290)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8983))).
Lemma joint_update_ready_8984 old :
 (exists ground bits, VM.find 8290 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8983 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8984.
Proof.
 intros [g8290 [b8290 H8290]].
 intros [g8983 [b8983 H8983]].
 unfold joint_update_expr_8984.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8985 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8288)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8984))).
Lemma joint_update_ready_8985 old :
 (exists ground bits, VM.find 8288 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8984 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8985.
Proof.
 intros [g8288 [b8288 H8288]].
 intros [g8984 [b8984 H8984]].
 unfold joint_update_expr_8985.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8986 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8286)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8985))).
Lemma joint_update_ready_8986 old :
 (exists ground bits, VM.find 8286 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8985 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8986.
Proof.
 intros [g8286 [b8286 H8286]].
 intros [g8985 [b8985 H8985]].
 unfold joint_update_expr_8986.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8987 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8284)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8986))).
Lemma joint_update_ready_8987 old :
 (exists ground bits, VM.find 8284 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8986 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8987.
Proof.
 intros [g8284 [b8284 H8284]].
 intros [g8986 [b8986 H8986]].
 unfold joint_update_expr_8987.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8988 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8282)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8987))).
Lemma joint_update_ready_8988 old :
 (exists ground bits, VM.find 8282 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8987 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8988.
Proof.
 intros [g8282 [b8282 H8282]].
 intros [g8987 [b8987 H8987]].
 unfold joint_update_expr_8988.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8989 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8280)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8988))).
Lemma joint_update_ready_8989 old :
 (exists ground bits, VM.find 8280 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8988 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8989.
Proof.
 intros [g8280 [b8280 H8280]].
 intros [g8988 [b8988 H8988]].
 unfold joint_update_expr_8989.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8990 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8278)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8989))).
Lemma joint_update_ready_8990 old :
 (exists ground bits, VM.find 8278 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8989 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8990.
Proof.
 intros [g8278 [b8278 H8278]].
 intros [g8989 [b8989 H8989]].
 unfold joint_update_expr_8990.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8991 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8276)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8990))).
Lemma joint_update_ready_8991 old :
 (exists ground bits, VM.find 8276 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8990 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8991.
Proof.
 intros [g8276 [b8276 H8276]].
 intros [g8990 [b8990 H8990]].
 unfold joint_update_expr_8991.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8992 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8274)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8991))).
Lemma joint_update_ready_8992 old :
 (exists ground bits, VM.find 8274 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8991 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8992.
Proof.
 intros [g8274 [b8274 H8274]].
 intros [g8991 [b8991 H8991]].
 unfold joint_update_expr_8992.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8993 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8272)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8992))).
Lemma joint_update_ready_8993 old :
 (exists ground bits, VM.find 8272 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8992 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8993.
Proof.
 intros [g8272 [b8272 H8272]].
 intros [g8992 [b8992 H8992]].
 unfold joint_update_expr_8993.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8994 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8270)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8993))).
Lemma joint_update_ready_8994 old :
 (exists ground bits, VM.find 8270 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8993 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8994.
Proof.
 intros [g8270 [b8270 H8270]].
 intros [g8993 [b8993 H8993]].
 unfold joint_update_expr_8994.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8995 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8268)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8994))).
Lemma joint_update_ready_8995 old :
 (exists ground bits, VM.find 8268 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8994 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8995.
Proof.
 intros [g8268 [b8268 H8268]].
 intros [g8994 [b8994 H8994]].
 unfold joint_update_expr_8995.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8996 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8266)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8995))).
Lemma joint_update_ready_8996 old :
 (exists ground bits, VM.find 8266 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8995 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8996.
Proof.
 intros [g8266 [b8266 H8266]].
 intros [g8995 [b8995 H8995]].
 unfold joint_update_expr_8996.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8997 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8264)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8996))).
Lemma joint_update_ready_8997 old :
 (exists ground bits, VM.find 8264 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8996 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8997.
Proof.
 intros [g8264 [b8264 H8264]].
 intros [g8996 [b8996 H8996]].
 unfold joint_update_expr_8997.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8998 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 8703))).
Lemma joint_update_ready_8998 old :
 (exists ground bits, VM.find 8703 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8998.
Proof.
 intros [g8703 [b8703 H8703]].
 unfold joint_update_expr_8998.
 solve_joint_update_ready.
Qed.
Definition joint_update_expr_8999 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 8899))).
Lemma joint_update_ready_8999 old :
 (exists ground bits, VM.find 8899 old = Some (Gval ground bits)) ->
 concrete_expression_ready old joint_update_expr_8999.
Proof.
 intros [g8899 [b8899 H8899]].
 unfold joint_update_expr_8999.
 solve_joint_update_ready.
Qed.
