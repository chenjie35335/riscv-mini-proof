Require Import CoreSocModel ComparisonNodes X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety ReferenceControlExpressions ReferenceRedirectSpine ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceControlNodeCertificates3 FormalInstructionResetConstants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_nop_expr_3062 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2097))).
Definition rf_nop_expr_3064 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3062))).
Definition rf_nop_expr_3065 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3064))).
Definition rf_nop_expr_3070 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1891))).
Definition rf_nop_expr_3071 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3070))).
Definition rf_nop_expr_3072 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3071))).
Definition rf_nop_expr_3073 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1896))).
Definition rf_nop_expr_3074 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3073))).
Definition rf_nop_expr_3075 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3074))).
Definition rf_nop_expr_3076 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1901))).
Definition rf_nop_expr_3077 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3076))).
Definition rf_nop_expr_3078 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3077))).
Definition rf_nop_expr_3079 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1906))).
Definition rf_nop_expr_3080 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3079))).
Definition rf_nop_expr_3081 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3080))).
Definition rf_nop_expr_3082 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1911))).
Definition rf_nop_expr_3083 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3082))).
Definition rf_nop_expr_3084 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3083))).
Definition rf_nop_expr_3085 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1916))).
Definition rf_nop_expr_3086 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3085))).
Definition rf_nop_expr_3087 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3086))).
Definition rf_nop_expr_3088 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1921))).
Definition rf_nop_expr_3089 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3088))).
Definition rf_nop_expr_3090 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3089))).
Definition rf_nop_expr_3091 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1926))).
Definition rf_nop_expr_3092 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3091))).
Definition rf_nop_expr_3093 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3092))).
Definition rf_nop_expr_3094 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1930))).
Definition rf_nop_expr_3095 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3094))).
Definition rf_nop_expr_3096 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3095))).
Definition rf_nop_expr_3097 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1934))).
Definition rf_nop_expr_3098 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3097))).
Definition rf_nop_expr_3099 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3098))).
Definition rf_nop_expr_3100 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1938))).
Definition rf_nop_expr_3101 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3100))).
Definition rf_nop_expr_3102 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3101))).
Definition rf_nop_expr_3103 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1955))).
Definition rf_nop_expr_3104 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3103))).
Definition rf_nop_expr_3105 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3104))).
Definition rf_nop_expr_3106 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1959))).
Definition rf_nop_expr_3107 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3106))).
Definition rf_nop_expr_3108 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3107))).
Definition rf_nop_expr_3109 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1963))).
Definition rf_nop_expr_3110 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3109))).
Definition rf_nop_expr_3111 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3110))).
Definition rf_nop_expr_3112 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1967))).
Definition rf_nop_expr_3113 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3112))).
Definition rf_nop_expr_3114 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3113))).
Definition rf_nop_expr_3115 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 1971))).
Definition rf_nop_expr_3116 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3115))).
Definition rf_nop_expr_3117 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3116))).
Definition rf_nop_expr_3118 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2011))).
Definition rf_nop_expr_3119 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3118))).
Definition rf_nop_expr_3120 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3119))).
Definition rf_nop_expr_3121 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 2454))).
Definition rf_nop_expr_3122 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3121))).
Definition rf_nop_expr_3123 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2016))).
Definition rf_nop_expr_3124 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3123))).
Definition rf_nop_expr_3125 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3124))).
Definition rf_nop_expr_3126 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2021))).
Definition rf_nop_expr_3127 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3126))).
Definition rf_nop_expr_3128 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3127))).
Definition rf_nop_expr_3129 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2026))).
Definition rf_nop_expr_3130 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3129))).
Definition rf_nop_expr_3131 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3130))).
Definition rf_nop_expr_3132 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2031))).
Definition rf_nop_expr_3133 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3132))).
Definition rf_nop_expr_3134 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3133))).
Definition rf_nop_expr_3135 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2036))).
Definition rf_nop_expr_3136 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3135))).
Definition rf_nop_expr_3137 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3136))).
Definition rf_nop_expr_3138 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2041))).
Definition rf_nop_expr_3139 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3138))).
Definition rf_nop_expr_3140 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3139))).
Definition rf_nop_expr_3141 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2046))).
Definition rf_nop_expr_3142 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3141))).
Definition rf_nop_expr_3143 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3142))).
Definition rf_nop_expr_3144 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2051))).
Definition rf_nop_expr_3145 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3144))).
Definition rf_nop_expr_3146 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3145))).
Definition rf_nop_expr_3147 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2056))).
Definition rf_nop_expr_3148 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3147))).
Definition rf_nop_expr_3149 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3148))).
Definition rf_nop_expr_3150 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2061))).
Definition rf_nop_expr_3151 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3150))).
Definition rf_nop_expr_3152 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3151))).
Definition rf_nop_expr_3153 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 1884))).
Definition rf_nop_expr_3154 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3153))).
Definition rf_nop_expr_3155 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 1884))).
Definition rf_nop_expr_3156 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3155))).
Definition rf_nop_expr_3157 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2065))).
Definition rf_nop_expr_3158 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3157))).
Definition rf_nop_expr_3159 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3158))).
Definition rf_nop_expr_3160 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2069))).
Definition rf_nop_expr_3161 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3160))).
Definition rf_nop_expr_3162 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3161))).
Definition rf_nop_expr_3163 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2073))).
Definition rf_nop_expr_3164 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3163))).
Definition rf_nop_expr_3165 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3164))).
Definition rf_nop_expr_3166 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2077))).
Definition rf_nop_expr_3167 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3166))).
Definition rf_nop_expr_3168 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3167))).
Definition rf_nop_expr_3169 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2081))).
Definition rf_nop_expr_3170 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3169))).
Definition rf_nop_expr_3171 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3170))).
Definition rf_nop_expr_3172 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2085))).
Definition rf_nop_expr_3173 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3172))).
Definition rf_nop_expr_3174 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3173))).
Definition rf_nop_expr_3175 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2089))).
Definition rf_nop_expr_3176 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3175))).
Definition rf_nop_expr_3177 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3176))).
Definition rf_nop_expr_3178 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 14 0) (@Eref VarOrder.T (@Eid VarOrder.T 2093))).
Definition rf_nop_expr_3179 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 0) (@Eref VarOrder.T (@Eid VarOrder.T 3178))).
Definition rf_nop_expr_3180 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 3179))).
Definition rf_nop_expr_3181 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2096)) (@Eref VarOrder.T (@Eid VarOrder.T 3065)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; false])).
Definition rf_nop_expr_3182 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2092)) (@Eref VarOrder.T (@Eid VarOrder.T 3180)) (@Eref VarOrder.T (@Eid VarOrder.T 3181))).
Definition rf_nop_expr_3183 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2088)) (@Eref VarOrder.T (@Eid VarOrder.T 3177)) (@Eref VarOrder.T (@Eid VarOrder.T 3182))).
Definition rf_nop_expr_3184 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2084)) (@Eref VarOrder.T (@Eid VarOrder.T 3174)) (@Eref VarOrder.T (@Eid VarOrder.T 3183))).
Definition rf_nop_expr_3185 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2080)) (@Eref VarOrder.T (@Eid VarOrder.T 3171)) (@Eref VarOrder.T (@Eid VarOrder.T 3184))).
Definition rf_nop_expr_3186 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2076)) (@Eref VarOrder.T (@Eid VarOrder.T 3168)) (@Eref VarOrder.T (@Eid VarOrder.T 3185))).
Definition rf_nop_expr_3187 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2072)) (@Eref VarOrder.T (@Eid VarOrder.T 3165)) (@Eref VarOrder.T (@Eid VarOrder.T 3186))).
Definition rf_nop_expr_3188 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2068)) (@Eref VarOrder.T (@Eid VarOrder.T 3162)) (@Eref VarOrder.T (@Eid VarOrder.T 3187))).
Definition rf_nop_expr_3189 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2064)) (@Eref VarOrder.T (@Eid VarOrder.T 3159)) (@Eref VarOrder.T (@Eid VarOrder.T 3188))).
Definition rf_nop_expr_3190 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2475)) (@Eref VarOrder.T (@Eid VarOrder.T 3156)) (@Eref VarOrder.T (@Eid VarOrder.T 3189))).
Definition rf_nop_expr_3191 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2472)) (@Eref VarOrder.T (@Eid VarOrder.T 3154)) (@Eref VarOrder.T (@Eid VarOrder.T 3190))).
Definition rf_nop_expr_3192 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2059)) (@Eref VarOrder.T (@Eid VarOrder.T 3152)) (@Eref VarOrder.T (@Eid VarOrder.T 3191))).
Definition rf_nop_expr_3193 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2054)) (@Eref VarOrder.T (@Eid VarOrder.T 3149)) (@Eref VarOrder.T (@Eid VarOrder.T 3192))).
Definition rf_nop_expr_3194 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2049)) (@Eref VarOrder.T (@Eid VarOrder.T 3146)) (@Eref VarOrder.T (@Eid VarOrder.T 3193))).
Definition rf_nop_expr_3195 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2044)) (@Eref VarOrder.T (@Eid VarOrder.T 3143)) (@Eref VarOrder.T (@Eid VarOrder.T 3194))).
Definition rf_nop_expr_3196 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2039)) (@Eref VarOrder.T (@Eid VarOrder.T 3140)) (@Eref VarOrder.T (@Eid VarOrder.T 3195))).
Definition rf_nop_expr_3197 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2034)) (@Eref VarOrder.T (@Eid VarOrder.T 3137)) (@Eref VarOrder.T (@Eid VarOrder.T 3196))).
Definition rf_nop_expr_3198 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2029)) (@Eref VarOrder.T (@Eid VarOrder.T 3134)) (@Eref VarOrder.T (@Eid VarOrder.T 3197))).
Definition rf_nop_expr_3199 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2024)) (@Eref VarOrder.T (@Eid VarOrder.T 3131)) (@Eref VarOrder.T (@Eid VarOrder.T 3198))).
Definition rf_nop_expr_3200 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2019)) (@Eref VarOrder.T (@Eid VarOrder.T 3128)) (@Eref VarOrder.T (@Eid VarOrder.T 3199))).
Definition rf_nop_expr_3201 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2014)) (@Eref VarOrder.T (@Eid VarOrder.T 3125)) (@Eref VarOrder.T (@Eid VarOrder.T 3200))).
Definition rf_nop_expr_3202 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2357)) (@Eref VarOrder.T (@Eid VarOrder.T 3122)) (@Eref VarOrder.T (@Eid VarOrder.T 3201))).
Definition rf_nop_expr_3203 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2010)) (@Eref VarOrder.T (@Eid VarOrder.T 3120)) (@Eref VarOrder.T (@Eid VarOrder.T 3202))).
Definition rf_nop_expr_3204 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 3117)) (@Eref VarOrder.T (@Eid VarOrder.T 3203))).
Definition rf_nop_expr_3205 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 3114)) (@Eref VarOrder.T (@Eid VarOrder.T 3204))).
Definition rf_nop_expr_3206 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 3111)) (@Eref VarOrder.T (@Eid VarOrder.T 3205))).
Definition rf_nop_expr_3207 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Eref VarOrder.T (@Eid VarOrder.T 3108)) (@Eref VarOrder.T (@Eid VarOrder.T 3206))).
Definition rf_nop_expr_3208 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 3105)) (@Eref VarOrder.T (@Eid VarOrder.T 3207))).
Definition rf_nop_expr_3209 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1937)) (@Eref VarOrder.T (@Eid VarOrder.T 3102)) (@Eref VarOrder.T (@Eid VarOrder.T 3208))).
Definition rf_nop_expr_3210 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1933)) (@Eref VarOrder.T (@Eid VarOrder.T 3099)) (@Eref VarOrder.T (@Eid VarOrder.T 3209))).
Definition rf_nop_expr_3211 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1929)) (@Eref VarOrder.T (@Eid VarOrder.T 3096)) (@Eref VarOrder.T (@Eid VarOrder.T 3210))).
Definition rf_nop_expr_3212 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1924)) (@Eref VarOrder.T (@Eid VarOrder.T 3093)) (@Eref VarOrder.T (@Eid VarOrder.T 3211))).
Definition rf_nop_expr_3213 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1919)) (@Eref VarOrder.T (@Eid VarOrder.T 3090)) (@Eref VarOrder.T (@Eid VarOrder.T 3212))).
Definition rf_nop_expr_3214 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1914)) (@Eref VarOrder.T (@Eid VarOrder.T 3087)) (@Eref VarOrder.T (@Eid VarOrder.T 3213))).
Definition rf_nop_expr_3215 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1909)) (@Eref VarOrder.T (@Eid VarOrder.T 3084)) (@Eref VarOrder.T (@Eid VarOrder.T 3214))).
Definition rf_nop_expr_3216 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1904)) (@Eref VarOrder.T (@Eid VarOrder.T 3081)) (@Eref VarOrder.T (@Eid VarOrder.T 3215))).
Definition rf_nop_expr_3217 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1899)) (@Eref VarOrder.T (@Eid VarOrder.T 3078)) (@Eref VarOrder.T (@Eid VarOrder.T 3216))).
Definition rf_nop_expr_3218 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1894)) (@Eref VarOrder.T (@Eid VarOrder.T 3075)) (@Eref VarOrder.T (@Eid VarOrder.T 3217))).
Definition rf_nop_expr_3219 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1889)) (@Eref VarOrder.T (@Eid VarOrder.T 3072)) (@Eref VarOrder.T (@Eid VarOrder.T 3218))).
Definition rf_nop_expr_3220 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 3219)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; false])).
Definition rf_nop_expr_3221 : hfexpr VarOrder.T := (@Eref VarOrder.T (@Eid VarOrder.T 3220)).
Definition rf_nop_offsets : seq nat := [::3141%nat;1%nat;0%nat;4%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Definition rf_nop_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(3062,rf_nop_expr_3062);(3064,rf_nop_expr_3064);(3065,rf_nop_expr_3065);(3070,rf_nop_expr_3070);(3071,rf_nop_expr_3071);(3072,rf_nop_expr_3072);(3073,rf_nop_expr_3073);(3074,rf_nop_expr_3074);(3075,rf_nop_expr_3075);(3076,rf_nop_expr_3076);(3077,rf_nop_expr_3077);(3078,rf_nop_expr_3078);(3079,rf_nop_expr_3079);(3080,rf_nop_expr_3080);(3081,rf_nop_expr_3081);(3082,rf_nop_expr_3082);(3083,rf_nop_expr_3083);(3084,rf_nop_expr_3084);(3085,rf_nop_expr_3085);(3086,rf_nop_expr_3086);(3087,rf_nop_expr_3087);(3088,rf_nop_expr_3088);(3089,rf_nop_expr_3089);(3090,rf_nop_expr_3090);(3091,rf_nop_expr_3091);(3092,rf_nop_expr_3092);(3093,rf_nop_expr_3093);(3094,rf_nop_expr_3094);(3095,rf_nop_expr_3095);(3096,rf_nop_expr_3096);(3097,rf_nop_expr_3097);(3098,rf_nop_expr_3098);(3099,rf_nop_expr_3099);(3100,rf_nop_expr_3100);(3101,rf_nop_expr_3101);(3102,rf_nop_expr_3102);(3103,rf_nop_expr_3103);(3104,rf_nop_expr_3104);(3105,rf_nop_expr_3105);(3106,rf_nop_expr_3106);(3107,rf_nop_expr_3107);(3108,rf_nop_expr_3108);(3109,rf_nop_expr_3109);(3110,rf_nop_expr_3110);(3111,rf_nop_expr_3111);(3112,rf_nop_expr_3112);(3113,rf_nop_expr_3113);(3114,rf_nop_expr_3114);(3115,rf_nop_expr_3115);(3116,rf_nop_expr_3116);(3117,rf_nop_expr_3117);(3118,rf_nop_expr_3118);(3119,rf_nop_expr_3119);(3120,rf_nop_expr_3120);(3121,rf_nop_expr_3121);(3122,rf_nop_expr_3122);(3123,rf_nop_expr_3123);(3124,rf_nop_expr_3124);(3125,rf_nop_expr_3125);(3126,rf_nop_expr_3126);(3127,rf_nop_expr_3127);(3128,rf_nop_expr_3128);(3129,rf_nop_expr_3129);(3130,rf_nop_expr_3130);(3131,rf_nop_expr_3131);(3132,rf_nop_expr_3132);(3133,rf_nop_expr_3133);(3134,rf_nop_expr_3134);(3135,rf_nop_expr_3135);(3136,rf_nop_expr_3136);(3137,rf_nop_expr_3137);(3138,rf_nop_expr_3138);(3139,rf_nop_expr_3139);(3140,rf_nop_expr_3140);(3141,rf_nop_expr_3141);(3142,rf_nop_expr_3142);(3143,rf_nop_expr_3143);(3144,rf_nop_expr_3144);(3145,rf_nop_expr_3145);(3146,rf_nop_expr_3146);(3147,rf_nop_expr_3147);(3148,rf_nop_expr_3148);(3149,rf_nop_expr_3149);(3150,rf_nop_expr_3150);(3151,rf_nop_expr_3151);(3152,rf_nop_expr_3152);(3153,rf_nop_expr_3153);(3154,rf_nop_expr_3154);(3155,rf_nop_expr_3155);(3156,rf_nop_expr_3156);(3157,rf_nop_expr_3157);(3158,rf_nop_expr_3158);(3159,rf_nop_expr_3159);(3160,rf_nop_expr_3160);(3161,rf_nop_expr_3161);(3162,rf_nop_expr_3162);(3163,rf_nop_expr_3163);(3164,rf_nop_expr_3164);(3165,rf_nop_expr_3165);(3166,rf_nop_expr_3166);(3167,rf_nop_expr_3167);(3168,rf_nop_expr_3168);(3169,rf_nop_expr_3169);(3170,rf_nop_expr_3170);(3171,rf_nop_expr_3171);(3172,rf_nop_expr_3172);(3173,rf_nop_expr_3173);(3174,rf_nop_expr_3174);(3175,rf_nop_expr_3175);(3176,rf_nop_expr_3176);(3177,rf_nop_expr_3177);(3178,rf_nop_expr_3178);(3179,rf_nop_expr_3179);(3180,rf_nop_expr_3180);(3181,rf_nop_expr_3181);(3182,rf_nop_expr_3182);(3183,rf_nop_expr_3183);(3184,rf_nop_expr_3184);(3185,rf_nop_expr_3185);(3186,rf_nop_expr_3186);(3187,rf_nop_expr_3187);(3188,rf_nop_expr_3188);(3189,rf_nop_expr_3189);(3190,rf_nop_expr_3190);(3191,rf_nop_expr_3191);(3192,rf_nop_expr_3192);(3193,rf_nop_expr_3193);(3194,rf_nop_expr_3194);(3195,rf_nop_expr_3195);(3196,rf_nop_expr_3196);(3197,rf_nop_expr_3197);(3198,rf_nop_expr_3198);(3199,rf_nop_expr_3199);(3200,rf_nop_expr_3200);(3201,rf_nop_expr_3201);(3202,rf_nop_expr_3202);(3203,rf_nop_expr_3203);(3204,rf_nop_expr_3204);(3205,rf_nop_expr_3205);(3206,rf_nop_expr_3206);(3207,rf_nop_expr_3207);(3208,rf_nop_expr_3208);(3209,rf_nop_expr_3209);(3210,rf_nop_expr_3210);(3211,rf_nop_expr_3211);(3212,rf_nop_expr_3212);(3213,rf_nop_expr_3213);(3214,rf_nop_expr_3214);(3215,rf_nop_expr_3215);(3216,rf_nop_expr_3216);(3217,rf_nop_expr_3217);(3218,rf_nop_expr_3218);(3219,rf_nop_expr_3219);(3220,rf_nop_expr_3220);(3221,rf_nop_expr_3221)].
Lemma rf_nop_positions : select_node_offsets rf_nop_offsets flat_statements = Some rf_nop_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_nop_safety : selected_node_safety flat_memories flat_statements rf_nop_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Definition rf_reference_nop_guards : seq (VarOrder.T * bool) := [::(1889,false);(1894,false);(1899,false);(1904,false);(1909,false);(1914,false);(1919,false);(1924,false);(1886,false);(1958,false);(1962,false);(1966,false);(1970,false);(2010,false);(2357,false);(2014,false);(2019,false);(2024,false);(2029,false);(2034,false);(2039,false);(2044,false);(2049,false);(2054,false);(2059,false);(2472,false);(2475,false);(2064,false);(2068,false);(2072,false);(2076,false);(2080,false);(2084,false);(2088,false);(2092,false);(2096,true)].
Theorem rf_reference_nop_decode_history invalid history (limit start : nat) :
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1706 (history time) = Some (Gval (Fuint 32) instruction_nop)) ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true])) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, ((Nat.add start 47 <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
 VM.find 3221 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false]) /\
 forall node bit, List.In (node,bit) rf_reference_nop_guards -> VM.find node (history time) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros H1706 H1707 Steps.
 assert (H1883 : forall time, ((Nat.add start 1 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1883 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1883 reference_control_expr_1883);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 0%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1883 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1707 time ltac:(lia)).
    rewrite (H1706 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1884 : forall time, ((Nat.add start 2 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1884 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1884 reference_control_expr_1884);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 1%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1884 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1883 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1888 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1888 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1888 reference_control_expr_1888);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 5%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1888 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1889 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1889 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1889 reference_control_expr_1889);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 6%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1889 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1888 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1893 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1893 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1893 reference_control_expr_1893);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 10%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1893 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1894 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1894 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1894 reference_control_expr_1894);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 11%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1894 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1893 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1898 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1898 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1898 reference_control_expr_1898);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 15%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1898 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1899 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1899 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1899 reference_control_expr_1899);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 16%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1899 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1898 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1903 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1903 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1903 reference_control_expr_1903);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 20%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1903 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1904 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1904 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1904 reference_control_expr_1904);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 21%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1904 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1903 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1908 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1908 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1908 reference_control_expr_1908);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 25%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1908 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1909 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1909 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1909 reference_control_expr_1909);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 26%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1909 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1908 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1913 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1913 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1913 reference_control_expr_1913);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 30%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1913 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1914 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1914 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1914 reference_control_expr_1914);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 31%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1914 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1913 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1918 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1918 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1918 reference_control_expr_1918);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 35%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1918 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1919 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1919 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1919 reference_control_expr_1919);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 36%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1919 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1918 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1923 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1923 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1923 reference_control_expr_1923);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 40%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1923 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1924 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1924 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1924 reference_control_expr_1924);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 41%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1924 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1923 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1885 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1885 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1885 reference_control_expr_1885);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 2%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1885 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1886 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1886 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1886 reference_control_expr_1886);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 3%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1886 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1885 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1957 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1957 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1957 reference_control_expr_1957);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 74%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1957 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1958 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1958 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1958 reference_control_expr_1958);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 75%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1958 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1957 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1961 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1961 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1961 reference_control_expr_1961);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 78%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1961 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1962 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1962 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1962 reference_control_expr_1962);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 79%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1962 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1961 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1965 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1965 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1965 reference_control_expr_1965);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 82%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1965 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1966 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1966 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1966 reference_control_expr_1966);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 83%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1966 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1965 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1969 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1969 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1969 reference_control_expr_1969);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 86%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1969 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1970 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1970 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1970 reference_control_expr_1970);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 87%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1970 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1969 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2009 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2009 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2009 reference_control_expr_2009);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 126%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2009 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2010 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2010 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2010 reference_control_expr_2010);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 127%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2010 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2009 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2356 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2356 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2356 reference_control_expr_2356);
  [exact reference_control_1_positions|exact reference_control_1_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_1_nodes 173%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2356 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2357 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2357 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2357 reference_control_expr_2357);
  [exact reference_control_1_positions|exact reference_control_1_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_1_nodes 174%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2357 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2356 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2013 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2013 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2013 reference_control_expr_2013);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 130%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2013 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2014 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2014 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2014 reference_control_expr_2014);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 131%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2014 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2013 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2018 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2018 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2018 reference_control_expr_2018);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 135%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2018 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2019 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2019 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2019 reference_control_expr_2019);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 136%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2019 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2018 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2023 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2023 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2023 reference_control_expr_2023);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 140%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2023 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2024 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2024 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2024 reference_control_expr_2024);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 141%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2024 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2023 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2028 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2028 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2028 reference_control_expr_2028);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 145%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2028 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2029 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2029 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2029 reference_control_expr_2029);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 146%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2029 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2028 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2033 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2033 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2033 reference_control_expr_2033);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 150%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2033 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2034 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2034 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2034 reference_control_expr_2034);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 151%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2034 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2033 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2038 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2038 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2038 reference_control_expr_2038);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 155%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2038 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2039 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2039 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2039 reference_control_expr_2039);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 156%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2039 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2038 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2043 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2043 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2043 reference_control_expr_2043);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 160%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2043 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2044 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2044 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2044 reference_control_expr_2044);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 161%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2044 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2043 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2048 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2048 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2048 reference_control_expr_2048);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 165%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2048 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2049 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2049 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2049 reference_control_expr_2049);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 166%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2049 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2048 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2053 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2053 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2053 reference_control_expr_2053);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 170%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2053 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2054 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2054 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2054 reference_control_expr_2054);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 171%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2054 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2053 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2058 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2058 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2058 reference_control_expr_2058);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 175%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2058 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2059 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2059 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2059 reference_control_expr_2059);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 176%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2059 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2058 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2471 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2471 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2471 reference_control_expr_2471);
  [exact reference_control_1_positions|exact reference_control_1_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_1_nodes 288%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2471 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2472 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2472 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2472 reference_control_expr_2472);
  [exact reference_control_1_positions|exact reference_control_1_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_1_nodes 289%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2472 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2471 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2474 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2474 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2474 reference_control_expr_2474);
  [exact reference_control_1_positions|exact reference_control_1_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_1_nodes 291%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2474 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2475 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2475 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2475 reference_control_expr_2475);
  [exact reference_control_1_positions|exact reference_control_1_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_1_nodes 292%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2475 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2474 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2063 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2063 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2063 reference_control_expr_2063);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 180%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2063 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2064 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2064 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2064 reference_control_expr_2064);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 181%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2064 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2063 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2067 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2067 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2067 reference_control_expr_2067);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 184%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2067 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2068 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2068 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2068 reference_control_expr_2068);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 185%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2068 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2067 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2071 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2071 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2071 reference_control_expr_2071);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 188%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2071 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2072 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2072 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2072 reference_control_expr_2072);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 189%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2072 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2071 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2075 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2075 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2075 reference_control_expr_2075);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 192%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2075 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2076 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2076 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2076 reference_control_expr_2076);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 193%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2076 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2075 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2079 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2079 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2079 reference_control_expr_2079);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 196%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2079 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2080 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2080 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2080 reference_control_expr_2080);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 197%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2080 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2079 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2083 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2083 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2083 reference_control_expr_2083);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 200%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2083 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2084 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2084 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2084 reference_control_expr_2084);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 201%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2084 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2083 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2087 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2087 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2087 reference_control_expr_2087);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 204%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2087 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2088 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2088 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2088 reference_control_expr_2088);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 205%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2088 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2087 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2091 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2091 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2091 reference_control_expr_2091);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 208%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2091 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2092 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2092 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2092 reference_control_expr_2092);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 209%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2092 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2091 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2095 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2095 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2095 reference_control_expr_2095);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 212%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2095 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2096 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2096 (history time) = Some (Gval (Fuint 1) [::true])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2096 reference_control_expr_2096);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 213%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2096 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2095 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1890 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1890 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1890 reference_control_expr_1890);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 7%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1890 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1891 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1891 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1891 reference_control_expr_1891);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 8%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1891 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1890 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3070 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3070 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3070 rf_nop_expr_3070);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 3%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3070 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1891 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3071 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3071 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3071 rf_nop_expr_3071);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 4%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3071 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3070 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3072 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3072 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3072 rf_nop_expr_3072);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 5%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3072 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3071 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1895 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1895 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1895 reference_control_expr_1895);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 12%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1895 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1896 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1896 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1896 reference_control_expr_1896);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 13%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1896 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1895 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3073 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3073 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3073 rf_nop_expr_3073);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 6%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3073 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1896 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3074 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3074 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3074 rf_nop_expr_3074);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 7%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3074 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3073 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3075 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3075 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3075 rf_nop_expr_3075);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 8%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3075 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3074 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1900 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1900 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1900 reference_control_expr_1900);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 17%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1900 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1901 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1901 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1901 reference_control_expr_1901);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 18%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1901 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1900 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3076 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3076 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3076 rf_nop_expr_3076);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 9%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3076 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1901 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3077 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3077 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3077 rf_nop_expr_3077);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 10%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3077 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3076 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3078 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3078 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3078 rf_nop_expr_3078);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 11%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3078 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3077 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1905 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1905 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1905 reference_control_expr_1905);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 22%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1905 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1906 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1906 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1906 reference_control_expr_1906);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 23%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1906 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1905 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3079 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3079 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3079 rf_nop_expr_3079);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 12%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3079 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1906 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3080 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3080 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3080 rf_nop_expr_3080);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 13%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3080 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3079 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3081 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3081 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3081 rf_nop_expr_3081);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 14%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3081 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3080 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1910 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1910 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1910 reference_control_expr_1910);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 27%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1910 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1911 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1911 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1911 reference_control_expr_1911);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 28%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1911 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1910 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3082 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3082 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3082 rf_nop_expr_3082);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 15%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3082 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1911 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3083 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3083 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3083 rf_nop_expr_3083);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 16%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3083 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3082 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3084 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3084 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3084 rf_nop_expr_3084);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 17%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3084 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3083 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1915 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1915 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1915 reference_control_expr_1915);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 32%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1915 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1916 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1916 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1916 reference_control_expr_1916);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 33%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1916 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1915 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3085 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3085 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3085 rf_nop_expr_3085);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 18%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3085 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1916 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3086 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3086 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3086 rf_nop_expr_3086);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 19%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3086 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3085 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3087 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3087 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3087 rf_nop_expr_3087);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 20%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3087 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3086 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1920 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1920 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1920 reference_control_expr_1920);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 37%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1920 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1921 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1921 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1921 reference_control_expr_1921);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 38%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1921 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1920 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3088 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3088 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3088 rf_nop_expr_3088);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 21%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3088 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1921 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3089 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3089 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3089 rf_nop_expr_3089);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 22%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3089 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3088 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3090 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3090 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3090 rf_nop_expr_3090);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 23%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3090 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3089 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1925 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1925 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1925 reference_control_expr_1925);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 42%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1925 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1926 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1926 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1926 reference_control_expr_1926);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 43%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1926 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1925 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3091 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3091 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3091 rf_nop_expr_3091);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 24%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3091 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1926 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3092 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3092 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3092 rf_nop_expr_3092);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 25%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3092 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3091 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3093 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3093 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3093 rf_nop_expr_3093);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 26%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3093 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3092 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1928 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1928 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1928 reference_control_expr_1928);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 45%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1928 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1929 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1929 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1929 reference_control_expr_1929);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 46%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1929 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1928 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1930 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1930 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1930 reference_control_expr_1930);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 47%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1930 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3094 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3094 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3094 rf_nop_expr_3094);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 27%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3094 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1930 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3095 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3095 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3095 rf_nop_expr_3095);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 28%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3095 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3094 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3096 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3096 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3096 rf_nop_expr_3096);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 29%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3096 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3095 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1932 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1932 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1932 reference_control_expr_1932);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 49%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1932 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1933 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1933 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1933 reference_control_expr_1933);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 50%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1933 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1932 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1934 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1934 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1934 reference_control_expr_1934);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 51%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1934 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3097 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3097 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3097 rf_nop_expr_3097);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 30%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3097 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1934 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3098 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3098 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3098 rf_nop_expr_3098);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 31%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3098 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3097 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3099 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3099 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3099 rf_nop_expr_3099);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 32%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3099 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3098 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1936 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1936 (history time) = Some (Gval (Fuint 32) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1936 reference_control_expr_1936);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 53%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1936 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1937 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1937 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1937 reference_control_expr_1937);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 54%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1937 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1936 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1938 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1938 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1938 reference_control_expr_1938);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 55%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1938 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3100 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3100 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3100 rf_nop_expr_3100);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 33%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3100 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1938 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3101 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3101 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3101 rf_nop_expr_3101);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 34%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3101 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3100 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3102 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3102 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3102 rf_nop_expr_3102);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 35%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3102 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3101 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1955 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1955 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1955 reference_control_expr_1955);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 72%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1955 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3103 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3103 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3103 rf_nop_expr_3103);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 36%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3103 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1955 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3104 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3104 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3104 rf_nop_expr_3104);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 37%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3104 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3103 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3105 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3105 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3105 rf_nop_expr_3105);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 38%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3105 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3104 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1959 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1959 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1959 reference_control_expr_1959);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 76%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1959 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3106 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3106 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3106 rf_nop_expr_3106);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 39%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3106 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1959 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3107 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3107 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3107 rf_nop_expr_3107);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 40%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3107 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3106 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3108 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3108 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3108 rf_nop_expr_3108);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 41%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3108 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3107 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1963 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1963 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1963 reference_control_expr_1963);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 80%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1963 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3109 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3109 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3109 rf_nop_expr_3109);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 42%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3109 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1963 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3110 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3110 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3110 rf_nop_expr_3110);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 43%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3110 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3109 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3111 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3111 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3111 rf_nop_expr_3111);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 44%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3111 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3110 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1967 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1967 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1967 reference_control_expr_1967);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 84%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1967 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3112 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3112 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3112 rf_nop_expr_3112);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 45%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3112 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1967 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3113 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3113 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3113 rf_nop_expr_3113);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 46%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3113 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3112 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3114 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3114 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3114 rf_nop_expr_3114);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 47%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3114 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3113 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H1971 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1971 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1971 reference_control_expr_1971);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 88%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_1971 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3115 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3115 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3115 rf_nop_expr_3115);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 48%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3115 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1971 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3116 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3116 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3116 rf_nop_expr_3116);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 49%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3116 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3115 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3117 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3117 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3117 rf_nop_expr_3117);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 50%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3117 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3116 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2011 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2011 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2011 reference_control_expr_2011);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 128%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2011 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3118 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3118 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3118 rf_nop_expr_3118);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 51%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3118 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2011 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3119 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3119 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3119 rf_nop_expr_3119);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 52%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3119 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3118 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3120 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3120 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3120 rf_nop_expr_3120);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 53%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3120 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3119 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2358 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2358 (history time) = Some (Gval (Fuint 31) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2358 reference_control_expr_2358);
  [exact reference_control_1_positions|exact reference_control_1_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_1_nodes 175%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2358 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2359 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2359 (history time) = Some (Gval (Fuint 21) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2359 reference_control_expr_2359);
  [exact reference_control_1_positions|exact reference_control_1_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_1_nodes 176%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2359 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2358 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2454 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2454 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2454 reference_control_expr_2454);
  [exact reference_control_1_positions|exact reference_control_1_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_1_nodes 271%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2454 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2359 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3121 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3121 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3121 rf_nop_expr_3121);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 54%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3121 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2454 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3122 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3122 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3122 rf_nop_expr_3122);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 55%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3122 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3121 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2015 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2015 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2015 reference_control_expr_2015);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 132%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2015 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2016 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2016 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2016 reference_control_expr_2016);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 133%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2016 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2015 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3123 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3123 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3123 rf_nop_expr_3123);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 56%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3123 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2016 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3124 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3124 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3124 rf_nop_expr_3124);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 57%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3124 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3123 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3125 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3125 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3125 rf_nop_expr_3125);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 58%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3125 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3124 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2020 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2020 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2020 reference_control_expr_2020);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 137%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2020 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2021 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2021 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2021 reference_control_expr_2021);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 138%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2021 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2020 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3126 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3126 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3126 rf_nop_expr_3126);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 59%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3126 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2021 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3127 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3127 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3127 rf_nop_expr_3127);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 60%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3127 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3126 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3128 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3128 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3128 rf_nop_expr_3128);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 61%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3128 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3127 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2025 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2025 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2025 reference_control_expr_2025);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 142%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2025 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2026 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2026 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2026 reference_control_expr_2026);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 143%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2026 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2025 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3129 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3129 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3129 rf_nop_expr_3129);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 62%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3129 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2026 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3130 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3130 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3130 rf_nop_expr_3130);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 63%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3130 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3129 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3131 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3131 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3131 rf_nop_expr_3131);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 64%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3131 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3130 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2030 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2030 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2030 reference_control_expr_2030);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 147%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2030 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2031 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2031 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2031 reference_control_expr_2031);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 148%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2031 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2030 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3132 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3132 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3132 rf_nop_expr_3132);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 65%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3132 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2031 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3133 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3133 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3133 rf_nop_expr_3133);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 66%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3133 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3132 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3134 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3134 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3134 rf_nop_expr_3134);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 67%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3134 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3133 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2035 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2035 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2035 reference_control_expr_2035);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 152%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2035 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2036 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2036 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2036 reference_control_expr_2036);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 153%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2036 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2035 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3135 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3135 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3135 rf_nop_expr_3135);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 68%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3135 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2036 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3136 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3136 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3136 rf_nop_expr_3136);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 69%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3136 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3135 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3137 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3137 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3137 rf_nop_expr_3137);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 70%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3137 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3136 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2040 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2040 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2040 reference_control_expr_2040);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 157%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2040 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2041 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2041 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2041 reference_control_expr_2041);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 158%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2041 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2040 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3138 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3138 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3138 rf_nop_expr_3138);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 71%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3138 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2041 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3139 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3139 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3139 rf_nop_expr_3139);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 72%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3139 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3138 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3140 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3140 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3140 rf_nop_expr_3140);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 73%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3140 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3139 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2045 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2045 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2045 reference_control_expr_2045);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 162%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2045 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2046 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2046 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2046 reference_control_expr_2046);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 163%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2046 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2045 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3141 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3141 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3141 rf_nop_expr_3141);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 74%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3141 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2046 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3142 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3142 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3142 rf_nop_expr_3142);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 75%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3142 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3141 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3143 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3143 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3143 rf_nop_expr_3143);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 76%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3143 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3142 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2050 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2050 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2050 reference_control_expr_2050);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 167%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2050 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2051 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2051 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2051 reference_control_expr_2051);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 168%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2051 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2050 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3144 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3144 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3144 rf_nop_expr_3144);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 77%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3144 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2051 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3145 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3145 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3145 rf_nop_expr_3145);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 78%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3145 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3144 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3146 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3146 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3146 rf_nop_expr_3146);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 79%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3146 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3145 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2055 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2055 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2055 reference_control_expr_2055);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 172%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2055 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2056 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2056 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2056 reference_control_expr_2056);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 173%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2056 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2055 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3147 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3147 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3147 rf_nop_expr_3147);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 80%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3147 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2056 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3148 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3148 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3148 rf_nop_expr_3148);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 81%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3148 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3147 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3149 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3149 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3149 rf_nop_expr_3149);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 82%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3149 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3148 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2060 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2060 (history time) = Some (Gval (Fuint 25) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2060 reference_control_expr_2060);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 177%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2060 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2061 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2061 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2061 reference_control_expr_2061);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 178%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2061 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2060 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3150 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3150 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3150 rf_nop_expr_3150);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 83%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3150 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2061 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3151 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3151 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3151 rf_nop_expr_3151);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 84%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3151 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3150 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3152 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3152 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3152 rf_nop_expr_3152);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 85%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3152 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3151 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3153 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3153 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3153 rf_nop_expr_3153);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 86%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3153 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3154 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3154 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3154 rf_nop_expr_3154);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 87%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3154 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3153 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3155 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3155 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3155 rf_nop_expr_3155);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 88%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3155 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3156 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3156 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3156 rf_nop_expr_3156);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 89%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3156 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3155 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2065 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2065 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2065 reference_control_expr_2065);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 182%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2065 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3157 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3157 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3157 rf_nop_expr_3157);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 90%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3157 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2065 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3158 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3158 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3158 rf_nop_expr_3158);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 91%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3158 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3157 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3159 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3159 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3159 rf_nop_expr_3159);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 92%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3159 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3158 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2069 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2069 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2069 reference_control_expr_2069);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 186%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2069 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3160 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3160 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3160 rf_nop_expr_3160);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 93%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3160 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2069 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3161 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3161 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3161 rf_nop_expr_3161);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 94%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3161 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3160 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3162 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3162 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3162 rf_nop_expr_3162);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 95%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3162 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3161 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2073 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2073 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2073 reference_control_expr_2073);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 190%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2073 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3163 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3163 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3163 rf_nop_expr_3163);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 96%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3163 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2073 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3164 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3164 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3164 rf_nop_expr_3164);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 97%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3164 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3163 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3165 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3165 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3165 rf_nop_expr_3165);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 98%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3165 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3164 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2077 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2077 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2077 reference_control_expr_2077);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 194%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2077 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3166 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3166 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3166 rf_nop_expr_3166);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 99%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3166 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2077 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3167 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3167 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3167 rf_nop_expr_3167);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 100%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3167 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3166 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3168 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3168 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3168 rf_nop_expr_3168);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 101%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3168 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3167 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2081 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2081 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2081 reference_control_expr_2081);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 198%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2081 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3169 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3169 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3169 rf_nop_expr_3169);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 102%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3169 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2081 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3170 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3170 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3170 rf_nop_expr_3170);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 103%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3170 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3169 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3171 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3171 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3171 rf_nop_expr_3171);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 104%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3171 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3170 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2085 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2085 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2085 reference_control_expr_2085);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 202%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2085 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3172 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3172 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3172 rf_nop_expr_3172);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 105%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3172 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2085 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3173 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3173 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3173 rf_nop_expr_3173);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 106%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3173 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3172 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3174 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3174 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3174 rf_nop_expr_3174);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 107%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3174 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3173 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2089 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2089 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2089 reference_control_expr_2089);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 206%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2089 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3175 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3175 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3175 rf_nop_expr_3175);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 108%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3175 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2089 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3176 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3176 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3176 rf_nop_expr_3176);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 109%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3176 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3175 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3177 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3177 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3177 rf_nop_expr_3177);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 110%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3177 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3176 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2093 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2093 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2093 reference_control_expr_2093);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 210%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2093 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3178 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3178 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3178 rf_nop_expr_3178);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 111%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3178 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2093 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3179 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3179 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3179 rf_nop_expr_3179);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 112%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3179 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3178 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3180 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3180 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3180 rf_nop_expr_3180);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 113%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3180 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3179 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H2097 : forall time, ((Nat.add start 3 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 2097 (history time) = Some (Gval (Fuint 20) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2097 reference_control_expr_2097);
  [exact reference_control_0_positions|exact reference_control_0_safety| | |apply Steps;lia].
  - apply (List.nth_error_In reference_control_0_nodes 214%nat). vm_compute. reflexivity.
  - intros site. cbn [reference_control_expr_2097 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1884 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3062 : forall time, ((Nat.add start 4 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3062 (history time) = Some (Gval (Fuint 15) [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3062 rf_nop_expr_3062);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 0%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3062 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2097 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3064 : forall time, ((Nat.add start 5 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3064 (history time) = Some (Gval (Fuint 12) [::true;true;false;false;true;false;false;false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3064 rf_nop_expr_3064);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 1%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3064 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3062 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3065 : forall time, ((Nat.add start 6 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3065 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3065 rf_nop_expr_3065);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 2%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3065 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3064 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3181 : forall time, ((Nat.add start 7 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3181 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3181 rf_nop_expr_3181);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 114%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3181 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2096 time ltac:(lia)).
    rewrite (H3065 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3182 : forall time, ((Nat.add start 8 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3182 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3182 rf_nop_expr_3182);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 115%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3182 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2092 time ltac:(lia)).
    rewrite (H3180 time ltac:(lia)).
    rewrite (H3181 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3183 : forall time, ((Nat.add start 9 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3183 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3183 rf_nop_expr_3183);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 116%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3183 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2088 time ltac:(lia)).
    rewrite (H3177 time ltac:(lia)).
    rewrite (H3182 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3184 : forall time, ((Nat.add start 10 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3184 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3184 rf_nop_expr_3184);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 117%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3184 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2084 time ltac:(lia)).
    rewrite (H3174 time ltac:(lia)).
    rewrite (H3183 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3185 : forall time, ((Nat.add start 11 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3185 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3185 rf_nop_expr_3185);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 118%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3185 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2080 time ltac:(lia)).
    rewrite (H3171 time ltac:(lia)).
    rewrite (H3184 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3186 : forall time, ((Nat.add start 12 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3186 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3186 rf_nop_expr_3186);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 119%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3186 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2076 time ltac:(lia)).
    rewrite (H3168 time ltac:(lia)).
    rewrite (H3185 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3187 : forall time, ((Nat.add start 13 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3187 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3187 rf_nop_expr_3187);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 120%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3187 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2072 time ltac:(lia)).
    rewrite (H3165 time ltac:(lia)).
    rewrite (H3186 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3188 : forall time, ((Nat.add start 14 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3188 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3188 rf_nop_expr_3188);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 121%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3188 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2068 time ltac:(lia)).
    rewrite (H3162 time ltac:(lia)).
    rewrite (H3187 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3189 : forall time, ((Nat.add start 15 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3189 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3189 rf_nop_expr_3189);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 122%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3189 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2064 time ltac:(lia)).
    rewrite (H3159 time ltac:(lia)).
    rewrite (H3188 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3190 : forall time, ((Nat.add start 16 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3190 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3190 rf_nop_expr_3190);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 123%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3190 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2475 time ltac:(lia)).
    rewrite (H3156 time ltac:(lia)).
    rewrite (H3189 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3191 : forall time, ((Nat.add start 17 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3191 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3191 rf_nop_expr_3191);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 124%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3191 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2472 time ltac:(lia)).
    rewrite (H3154 time ltac:(lia)).
    rewrite (H3190 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3192 : forall time, ((Nat.add start 18 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3192 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3192 rf_nop_expr_3192);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 125%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3192 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2059 time ltac:(lia)).
    rewrite (H3152 time ltac:(lia)).
    rewrite (H3191 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3193 : forall time, ((Nat.add start 19 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3193 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3193 rf_nop_expr_3193);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 126%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3193 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2054 time ltac:(lia)).
    rewrite (H3149 time ltac:(lia)).
    rewrite (H3192 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3194 : forall time, ((Nat.add start 20 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3194 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3194 rf_nop_expr_3194);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 127%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3194 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2049 time ltac:(lia)).
    rewrite (H3146 time ltac:(lia)).
    rewrite (H3193 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3195 : forall time, ((Nat.add start 21 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3195 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3195 rf_nop_expr_3195);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 128%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3195 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2044 time ltac:(lia)).
    rewrite (H3143 time ltac:(lia)).
    rewrite (H3194 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3196 : forall time, ((Nat.add start 22 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3196 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3196 rf_nop_expr_3196);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 129%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3196 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2039 time ltac:(lia)).
    rewrite (H3140 time ltac:(lia)).
    rewrite (H3195 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3197 : forall time, ((Nat.add start 23 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3197 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3197 rf_nop_expr_3197);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 130%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3197 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2034 time ltac:(lia)).
    rewrite (H3137 time ltac:(lia)).
    rewrite (H3196 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3198 : forall time, ((Nat.add start 24 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3198 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3198 rf_nop_expr_3198);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 131%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3198 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2029 time ltac:(lia)).
    rewrite (H3134 time ltac:(lia)).
    rewrite (H3197 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3199 : forall time, ((Nat.add start 25 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3199 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3199 rf_nop_expr_3199);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 132%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3199 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2024 time ltac:(lia)).
    rewrite (H3131 time ltac:(lia)).
    rewrite (H3198 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3200 : forall time, ((Nat.add start 26 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3200 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3200 rf_nop_expr_3200);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 133%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3200 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2019 time ltac:(lia)).
    rewrite (H3128 time ltac:(lia)).
    rewrite (H3199 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3201 : forall time, ((Nat.add start 27 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3201 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3201 rf_nop_expr_3201);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 134%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3201 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2014 time ltac:(lia)).
    rewrite (H3125 time ltac:(lia)).
    rewrite (H3200 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3202 : forall time, ((Nat.add start 28 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3202 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3202 rf_nop_expr_3202);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 135%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3202 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2357 time ltac:(lia)).
    rewrite (H3122 time ltac:(lia)).
    rewrite (H3201 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3203 : forall time, ((Nat.add start 29 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3203 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3203 rf_nop_expr_3203);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 136%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3203 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H2010 time ltac:(lia)).
    rewrite (H3120 time ltac:(lia)).
    rewrite (H3202 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3204 : forall time, ((Nat.add start 30 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3204 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3204 rf_nop_expr_3204);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 137%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3204 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1970 time ltac:(lia)).
    rewrite (H3117 time ltac:(lia)).
    rewrite (H3203 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3205 : forall time, ((Nat.add start 31 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3205 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3205 rf_nop_expr_3205);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 138%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3205 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1966 time ltac:(lia)).
    rewrite (H3114 time ltac:(lia)).
    rewrite (H3204 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3206 : forall time, ((Nat.add start 32 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3206 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3206 rf_nop_expr_3206);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 139%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3206 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1962 time ltac:(lia)).
    rewrite (H3111 time ltac:(lia)).
    rewrite (H3205 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3207 : forall time, ((Nat.add start 33 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3207 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3207 rf_nop_expr_3207);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 140%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3207 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1958 time ltac:(lia)).
    rewrite (H3108 time ltac:(lia)).
    rewrite (H3206 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3208 : forall time, ((Nat.add start 34 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3208 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3208 rf_nop_expr_3208);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 141%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3208 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1886 time ltac:(lia)).
    rewrite (H3105 time ltac:(lia)).
    rewrite (H3207 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3209 : forall time, ((Nat.add start 35 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3209 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3209 rf_nop_expr_3209);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 142%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3209 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1937 time ltac:(lia)).
    rewrite (H3102 time ltac:(lia)).
    rewrite (H3208 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3210 : forall time, ((Nat.add start 36 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3210 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3210 rf_nop_expr_3210);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 143%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3210 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1933 time ltac:(lia)).
    rewrite (H3099 time ltac:(lia)).
    rewrite (H3209 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3211 : forall time, ((Nat.add start 37 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3211 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3211 rf_nop_expr_3211);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 144%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3211 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1929 time ltac:(lia)).
    rewrite (H3096 time ltac:(lia)).
    rewrite (H3210 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3212 : forall time, ((Nat.add start 38 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3212 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3212 rf_nop_expr_3212);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 145%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3212 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1924 time ltac:(lia)).
    rewrite (H3093 time ltac:(lia)).
    rewrite (H3211 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3213 : forall time, ((Nat.add start 39 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3213 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3213 rf_nop_expr_3213);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 146%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3213 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1919 time ltac:(lia)).
    rewrite (H3090 time ltac:(lia)).
    rewrite (H3212 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3214 : forall time, ((Nat.add start 40 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3214 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3214 rf_nop_expr_3214);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 147%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3214 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1914 time ltac:(lia)).
    rewrite (H3087 time ltac:(lia)).
    rewrite (H3213 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3215 : forall time, ((Nat.add start 41 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3215 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3215 rf_nop_expr_3215);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 148%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3215 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1909 time ltac:(lia)).
    rewrite (H3084 time ltac:(lia)).
    rewrite (H3214 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3216 : forall time, ((Nat.add start 42 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3216 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3216 rf_nop_expr_3216);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 149%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3216 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1904 time ltac:(lia)).
    rewrite (H3081 time ltac:(lia)).
    rewrite (H3215 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3217 : forall time, ((Nat.add start 43 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3217 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3217 rf_nop_expr_3217);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 150%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3217 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1899 time ltac:(lia)).
    rewrite (H3078 time ltac:(lia)).
    rewrite (H3216 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3218 : forall time, ((Nat.add start 44 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3218 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3218 rf_nop_expr_3218);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 151%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3218 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1894 time ltac:(lia)).
    rewrite (H3075 time ltac:(lia)).
    rewrite (H3217 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3219 : forall time, ((Nat.add start 45 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3219 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3219 rf_nop_expr_3219);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 152%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3219 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1889 time ltac:(lia)).
    rewrite (H3072 time ltac:(lia)).
    rewrite (H3218 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3220 : forall time, ((Nat.add start 46 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3220 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3220 rf_nop_expr_3220);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 153%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3220 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H1707 time ltac:(lia)).
    rewrite (H3219 time ltac:(lia)).
    vm_compute. reflexivity. }
 assert (H3221 : forall time, ((Nat.add start 47 <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 3221 (history time) = Some (Gval (Fuint 5) [::false;false;false;false;false])).
 { intros time [Lower Upper]. destruct time as [|time]; [lia|].
  eapply (reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3221 rf_nop_expr_3221);
  [exact rf_nop_positions|exact rf_nop_safety| | |apply Steps;lia].
  - apply (List.nth_error_In rf_nop_nodes 154%nat). vm_compute. reflexivity.
  - intros site. cbn [rf_nop_expr_3221 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
    try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
    rewrite (H3220 time ltac:(lia)).
    vm_compute. reflexivity. }
 intros time Bounds. split.
 - apply H3221. lia.
 - intros node bit Member.
   cbn [rf_reference_nop_guards] in Member.
   destruct Member as [M0|Member].
   { inversion M0; subst. apply H1889. lia. }
   destruct Member as [M1|Member].
   { inversion M1; subst. apply H1894. lia. }
   destruct Member as [M2|Member].
   { inversion M2; subst. apply H1899. lia. }
   destruct Member as [M3|Member].
   { inversion M3; subst. apply H1904. lia. }
   destruct Member as [M4|Member].
   { inversion M4; subst. apply H1909. lia. }
   destruct Member as [M5|Member].
   { inversion M5; subst. apply H1914. lia. }
   destruct Member as [M6|Member].
   { inversion M6; subst. apply H1919. lia. }
   destruct Member as [M7|Member].
   { inversion M7; subst. apply H1924. lia. }
   destruct Member as [M8|Member].
   { inversion M8; subst. apply H1886. lia. }
   destruct Member as [M9|Member].
   { inversion M9; subst. apply H1958. lia. }
   destruct Member as [M10|Member].
   { inversion M10; subst. apply H1962. lia. }
   destruct Member as [M11|Member].
   { inversion M11; subst. apply H1966. lia. }
   destruct Member as [M12|Member].
   { inversion M12; subst. apply H1970. lia. }
   destruct Member as [M13|Member].
   { inversion M13; subst. apply H2010. lia. }
   destruct Member as [M14|Member].
   { inversion M14; subst. apply H2357. lia. }
   destruct Member as [M15|Member].
   { inversion M15; subst. apply H2014. lia. }
   destruct Member as [M16|Member].
   { inversion M16; subst. apply H2019. lia. }
   destruct Member as [M17|Member].
   { inversion M17; subst. apply H2024. lia. }
   destruct Member as [M18|Member].
   { inversion M18; subst. apply H2029. lia. }
   destruct Member as [M19|Member].
   { inversion M19; subst. apply H2034. lia. }
   destruct Member as [M20|Member].
   { inversion M20; subst. apply H2039. lia. }
   destruct Member as [M21|Member].
   { inversion M21; subst. apply H2044. lia. }
   destruct Member as [M22|Member].
   { inversion M22; subst. apply H2049. lia. }
   destruct Member as [M23|Member].
   { inversion M23; subst. apply H2054. lia. }
   destruct Member as [M24|Member].
   { inversion M24; subst. apply H2059. lia. }
   destruct Member as [M25|Member].
   { inversion M25; subst. apply H2472. lia. }
   destruct Member as [M26|Member].
   { inversion M26; subst. apply H2475. lia. }
   destruct Member as [M27|Member].
   { inversion M27; subst. apply H2064. lia. }
   destruct Member as [M28|Member].
   { inversion M28; subst. apply H2068. lia. }
   destruct Member as [M29|Member].
   { inversion M29; subst. apply H2072. lia. }
   destruct Member as [M30|Member].
   { inversion M30; subst. apply H2076. lia. }
   destruct Member as [M31|Member].
   { inversion M31; subst. apply H2080. lia. }
   destruct Member as [M32|Member].
   { inversion M32; subst. apply H2084. lia. }
   destruct Member as [M33|Member].
   { inversion M33; subst. apply H2088. lia. }
   destruct Member as [M34|Member].
   { inversion M34; subst. apply H2092. lia. }
   destruct Member as [M35|Member].
   { inversion M35; subst. apply H2096. lia. }
   contradiction.
Qed.
