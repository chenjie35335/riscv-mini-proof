Require Import CoreSocModel ComparisonNodes RFReferenceNopDecode ReferenceRedirectSpine ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceControlNodeCertificates3 X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Record rf_rd_slice := {rds_node:N;rds_source:N;rds_high:nat;rds_low:nat;rds_source_width:nat;rds_rank:nat}.
Definition rf_rd_slices := [::{|rds_node:=1890;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1891;rds_source:=1890;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=1895;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1896;rds_source:=1895;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=1900;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1901;rds_source:=1900;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=1905;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1906;rds_source:=1905;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=1910;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1911;rds_source:=1910;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=1915;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1916;rds_source:=1915;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=1920;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1921;rds_source:=1920;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=1925;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1926;rds_source:=1925;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=1930;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1934;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1938;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1955;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1959;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1963;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1967;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=1971;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2011;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2015;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2016;rds_source:=2015;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2020;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2021;rds_source:=2020;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2025;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2026;rds_source:=2025;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2030;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2031;rds_source:=2030;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2035;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2036;rds_source:=2035;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2040;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2041;rds_source:=2040;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2045;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2046;rds_source:=2045;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2050;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2051;rds_source:=2050;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2055;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2056;rds_source:=2055;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2060;rds_source:=1884;rds_high:=24%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2061;rds_source:=2060;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=25%nat;rds_rank:=2%nat|};{|rds_node:=2065;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2069;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2073;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2077;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2081;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2085;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2089;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2093;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2097;rds_source:=1884;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2358;rds_source:=1884;rds_high:=30%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=2359;rds_source:=2358;rds_high:=20%nat;rds_low:=0%nat;rds_source_width:=31%nat;rds_rank:=2%nat|};{|rds_node:=2454;rds_source:=2359;rds_high:=19%nat;rds_low:=0%nat;rds_source_width:=21%nat;rds_rank:=3%nat|};{|rds_node:=3062;rds_source:=2097;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3064;rds_source:=3062;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3065;rds_source:=3064;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3070;rds_source:=1891;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3071;rds_source:=3070;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3072;rds_source:=3071;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3073;rds_source:=1896;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3074;rds_source:=3073;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3075;rds_source:=3074;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3076;rds_source:=1901;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3077;rds_source:=3076;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3078;rds_source:=3077;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3079;rds_source:=1906;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3080;rds_source:=3079;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3081;rds_source:=3080;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3082;rds_source:=1911;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3083;rds_source:=3082;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3084;rds_source:=3083;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3085;rds_source:=1916;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3086;rds_source:=3085;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3087;rds_source:=3086;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3088;rds_source:=1921;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3089;rds_source:=3088;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3090;rds_source:=3089;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3091;rds_source:=1926;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3092;rds_source:=3091;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3093;rds_source:=3092;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3094;rds_source:=1930;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3095;rds_source:=3094;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3096;rds_source:=3095;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3097;rds_source:=1934;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3098;rds_source:=3097;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3099;rds_source:=3098;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3100;rds_source:=1938;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3101;rds_source:=3100;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3102;rds_source:=3101;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3103;rds_source:=1955;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3104;rds_source:=3103;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3105;rds_source:=3104;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3106;rds_source:=1959;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3107;rds_source:=3106;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3108;rds_source:=3107;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3109;rds_source:=1963;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3110;rds_source:=3109;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3111;rds_source:=3110;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3112;rds_source:=1967;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3113;rds_source:=3112;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3114;rds_source:=3113;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3115;rds_source:=1971;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3116;rds_source:=3115;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3117;rds_source:=3116;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3118;rds_source:=2011;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3119;rds_source:=3118;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3120;rds_source:=3119;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3121;rds_source:=2454;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=4%nat|};{|rds_node:=3122;rds_source:=3121;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3123;rds_source:=2016;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3124;rds_source:=3123;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3125;rds_source:=3124;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3126;rds_source:=2021;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3127;rds_source:=3126;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3128;rds_source:=3127;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3129;rds_source:=2026;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3130;rds_source:=3129;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3131;rds_source:=3130;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3132;rds_source:=2031;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3133;rds_source:=3132;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3134;rds_source:=3133;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3135;rds_source:=2036;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3136;rds_source:=3135;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3137;rds_source:=3136;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3138;rds_source:=2041;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3139;rds_source:=3138;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3140;rds_source:=3139;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3141;rds_source:=2046;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3142;rds_source:=3141;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3143;rds_source:=3142;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3144;rds_source:=2051;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3145;rds_source:=3144;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3146;rds_source:=3145;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3147;rds_source:=2056;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3148;rds_source:=3147;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3149;rds_source:=3148;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3150;rds_source:=2061;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=3%nat|};{|rds_node:=3151;rds_source:=3150;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=4%nat|};{|rds_node:=3152;rds_source:=3151;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=5%nat|};{|rds_node:=3153;rds_source:=1884;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=3154;rds_source:=3153;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=2%nat|};{|rds_node:=3155;rds_source:=1884;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=32%nat;rds_rank:=1%nat|};{|rds_node:=3156;rds_source:=3155;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=2%nat|};{|rds_node:=3157;rds_source:=2065;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3158;rds_source:=3157;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3159;rds_source:=3158;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3160;rds_source:=2069;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3161;rds_source:=3160;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3162;rds_source:=3161;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3163;rds_source:=2073;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3164;rds_source:=3163;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3165;rds_source:=3164;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3166;rds_source:=2077;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3167;rds_source:=3166;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3168;rds_source:=3167;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3169;rds_source:=2081;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3170;rds_source:=3169;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3171;rds_source:=3170;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3172;rds_source:=2085;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3173;rds_source:=3172;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3174;rds_source:=3173;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3175;rds_source:=2089;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3176;rds_source:=3175;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3177;rds_source:=3176;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|};{|rds_node:=3178;rds_source:=2093;rds_high:=14%nat;rds_low:=0%nat;rds_source_width:=20%nat;rds_rank:=2%nat|};{|rds_node:=3179;rds_source:=3178;rds_high:=11%nat;rds_low:=0%nat;rds_source_width:=15%nat;rds_rank:=3%nat|};{|rds_node:=3180;rds_source:=3179;rds_high:=11%nat;rds_low:=7%nat;rds_source_width:=12%nat;rds_rank:=4%nat|}].
Definition rf_rd_slice_at i := nth {|rds_node:=0;rds_source:=0;rds_high:=0%nat;rds_low:=0%nat;rds_source_width:=0%nat;rds_rank:=0%nat|} rf_rd_slices i.
Definition rf_rd_slice_expr row := @Eprim_unop VarOrder.T (Uextr(rds_high row)(rds_low row))(@Eref VarOrder.T(@Eid VarOrder.T(rds_source row))).
Definition rf_rd_slice_value row instruction := Gval(Fuint(S(rds_high row)-rds_low row)%nat)(drop(rds_low row)(take(S(rds_high row))instruction)).
Lemma rf_rd_slice_certificates i : (i<171)%coq_nat ->
 exists offsets nodes,select_node_offsets offsets flat_statements=Some nodes /\selected_node_safety flat_memories flat_statements offsets flat_statements=true /\List.In(rds_node(rf_rd_slice_at i),rf_rd_slice_expr(rf_rd_slice_at i))nodes /\(rds_low(rf_rd_slice_at i)<=rds_high(rf_rd_slice_at i))%nat /\(S(rds_high(rf_rd_slice_at i))<=rds_source_width(rf_rd_slice_at i))%nat.
Proof. intro Bound.
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 7%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 8%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 12%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 13%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 17%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 18%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 22%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 23%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 27%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 28%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 32%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 33%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 37%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 38%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 42%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 43%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 47%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 51%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 55%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 72%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 76%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 80%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 84%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 88%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 128%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 132%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 133%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 137%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 138%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 142%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 143%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 147%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 148%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 152%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 153%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 157%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 158%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 162%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 163%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 167%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 168%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 172%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 173%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 177%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 178%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 182%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 186%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 190%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 194%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 198%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 202%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 206%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 210%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_0_offsets,reference_control_0_nodes. split;[exact reference_control_0_positions|]. split;[exact reference_control_0_safety|]. split;[apply(List.nth_error_In reference_control_0_nodes 214%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_1_offsets,reference_control_1_nodes. split;[exact reference_control_1_positions|]. split;[exact reference_control_1_safety|]. split;[apply(List.nth_error_In reference_control_1_nodes 175%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_1_offsets,reference_control_1_nodes. split;[exact reference_control_1_positions|]. split;[exact reference_control_1_safety|]. split;[apply(List.nth_error_In reference_control_1_nodes 176%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists reference_control_1_offsets,reference_control_1_nodes. split;[exact reference_control_1_positions|]. split;[exact reference_control_1_safety|]. split;[apply(List.nth_error_In reference_control_1_nodes 271%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 0%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 1%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 2%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 3%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 4%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 5%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 6%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 7%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 8%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 9%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 10%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 11%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 12%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 13%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 14%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 15%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 16%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 17%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 18%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 19%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 20%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 21%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 22%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 23%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 24%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 25%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 26%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 27%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 28%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 29%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 30%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 31%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 32%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 33%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 34%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 35%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 36%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 37%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 38%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 39%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 40%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 41%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 42%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 43%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 44%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 45%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 46%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 47%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 48%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 49%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 50%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 51%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 52%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 53%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 54%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 55%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 56%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 57%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 58%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 59%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 60%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 61%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 62%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 63%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 64%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 65%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 66%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 67%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 68%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 69%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 70%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 71%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 72%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 73%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 74%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 75%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 76%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 77%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 78%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 79%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 80%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 81%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 82%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 83%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 84%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 85%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 86%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 87%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 88%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 89%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 90%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 91%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 92%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 93%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 94%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 95%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 96%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 97%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 98%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 99%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 100%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 101%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 102%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 103%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 104%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 105%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 106%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 107%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 108%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 109%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 110%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 111%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 112%nat);reflexivity|split;reflexivity]. }
destruct i as[|i]. {exists rf_nop_offsets,rf_nop_nodes. split;[exact rf_nop_positions|]. split;[exact rf_nop_safety|]. split;[apply(List.nth_error_In rf_nop_nodes 113%nat);reflexivity|split;reflexivity]. }
lia. Qed.
Lemma rf_rd_slice_step i invalid old result instruction : (i<171)%coq_nat ->
 VM.find(rds_source(rf_rd_slice_at i))old=Some(Gval(Fuint(rds_source_width(rf_rd_slice_at i)))(take(rds_source_width(rf_rd_slice_at i))instruction)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(rds_node(rf_rd_slice_at i))result=Some(rf_rd_slice_value(rf_rd_slice_at i)instruction).
Proof.
 intros Bound Source Step. destruct(rf_rd_slice_certificates i Bound)as[offsets[nodes[Positions[Safety[Member[Lower Width]]]]]].
 eapply(reference_redirect_ground_step offsets nodes _ (rf_rd_slice_expr(rf_rd_slice_at i)));[exact Positions|exact Safety|exact Member| |exact Step].
 intros site. unfold rf_rd_slice_expr. cbn[eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source.
 cbn [eval_unop]. rewrite Lower Width.
 change(Some(Gval(Fuint(S(rds_high(rf_rd_slice_at i))-rds_low(rf_rd_slice_at i))%nat)(drop(rds_low(rf_rd_slice_at i))(take(S(rds_high(rf_rd_slice_at i)))(take(rds_source_width(rf_rd_slice_at i))instruction))))=Some(rf_rd_slice_value(rf_rd_slice_at i)instruction)).
 rewrite take_takel;[reflexivity|exact Width].
Qed.
(* Scalar history and ISA composition. *)


Lemma rf_rd_slice_rank_positive i : (i<171)%coq_nat ->(0<rds_rank(rf_rd_slice_at i))%coq_nat.
Proof. intro Bound. do 171(destruct i as[|i];[vm_compute;lia|]);lia. Qed.
Lemma rf_rd_slice_source i : (i<171)%coq_nat ->
 (rds_source(rf_rd_slice_at i)=1884 /\rds_source_width(rf_rd_slice_at i)=32%nat) \/
 exists prior,(prior<171)%coq_nat /\rds_source(rf_rd_slice_at i)=rds_node(rf_rd_slice_at prior) /\rds_low(rf_rd_slice_at prior)=0%nat /\S(rds_high(rf_rd_slice_at prior))=rds_source_width(rf_rd_slice_at i) /\(rds_rank(rf_rd_slice_at prior)<rds_rank(rf_rd_slice_at i))%coq_nat.
Proof. intro Bound.
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 0%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 2%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 4%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 6%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 8%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 10%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 12%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 14%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 25%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 27%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 29%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 31%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 33%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 35%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 37%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 39%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 41%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 43%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 54%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 55%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 53%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 57%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 58%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 1%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 60%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 61%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 3%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 63%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 64%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 5%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 66%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 67%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 7%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 69%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 70%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 9%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 72%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 73%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 11%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 75%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 76%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 13%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 78%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 79%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 15%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 81%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 82%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 16%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 84%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 85%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 17%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 87%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 88%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 18%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 90%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 91%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 19%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 93%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 94%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 20%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 96%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 97%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 21%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 99%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 100%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 22%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 102%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 103%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 23%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 105%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 106%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 24%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 108%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 109%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 56%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 111%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 26%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 113%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 114%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 28%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 116%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 117%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 30%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 119%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 120%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 32%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 122%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 123%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 34%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 125%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 126%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 36%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 128%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 129%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 38%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 131%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 132%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 40%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 134%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 135%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 42%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 137%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 138%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 44%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 140%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 141%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 143%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { left;split;reflexivity. }
destruct i as[|i]. { right;exists 145%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 45%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 147%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 148%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 46%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 150%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 151%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 47%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 153%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 154%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 48%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 156%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 157%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 49%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 159%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 160%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 50%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 162%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 163%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 51%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 165%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 166%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 52%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 168%nat;vm_compute;repeat split;lia. }
destruct i as[|i]. { right;exists 169%nat;vm_compute;repeat split;lia. }
lia. Qed.
Theorem rf_reference_rd_slices_history invalid history (limit start:nat) instruction :size instruction=32%nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time i,(i<171)%coq_nat ->(Nat.add start(rds_rank(rf_rd_slice_at i))<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find(rds_node(rf_rd_slice_at i))(history time)=Some(rf_rd_slice_value(rf_rd_slice_at i)instruction).
Proof.
 intros Size Instruction Steps time. induction time as[|time IH];intros i Bound Lower Upper.
 - pose proof(rf_rd_slice_rank_positive i Bound). lia.
 - eapply(rf_rd_slice_step i invalid(history time)(history(S time))instruction Bound);[|apply Steps;lia].
 destruct(rf_rd_slice_source i Bound)as[[Source Width]|[prior[Prior[Source[Low[Width Rank]]]]]].
 + assert(Take:take 32 instruction=instruction)by(rewrite -Size take_size;reflexivity). rewrite Source Width Take. apply Instruction;[pose proof(rf_rd_slice_rank_positive i Bound);lia|lia].
 + pose proof(IH prior Prior ltac:(lia)ltac:(lia))as Value.
   unfold rf_rd_slice_value in Value. rewrite Low subn0 in Value. rewrite drop0 in Value.
   rewrite Width in Value. rewrite Source. exact Value.
Qed.
Definition rf_instruction_rd (instruction:bits) :=drop 7(take 12 instruction).
Lemma rf_instruction_rd_size instruction :size instruction=32%nat ->size(rf_instruction_rd instruction)=5%nat.
Proof. intro Size. unfold rf_instruction_rd. rewrite size_drop size_take Size. reflexivity. Qed.

Definition rf_rd_guards :seq N := [::2096;2092;2088;2084;2080;2076;2072;2068;2064;2475;2472;2059;2054;2049;2044;2039;2034;2029;2024;2019;2014;2357;2010;1970;1966;1962;1958;1886;1937;1933;1929;1924;1919;1914;1909;1904;1899;1894;1889].
Definition rf_rd_candidates :seq nat := [::59%nat;170%nat;167%nat;164%nat;161%nat;158%nat;155%nat;152%nat;149%nat;146%nat;144%nat;142%nat;139%nat;136%nat;133%nat;130%nat;127%nat;124%nat;121%nat;118%nat;115%nat;112%nat;110%nat;107%nat;104%nat;101%nat;98%nat;95%nat;92%nat;89%nat;86%nat;83%nat;80%nat;77%nat;74%nat;71%nat;68%nat;65%nat;62%nat].
Definition rf_rd_guard stage := nth 0 rf_rd_guards stage.
Definition rf_rd_candidate stage :=nth 0%nat rf_rd_candidates stage.
Definition rf_rd_previous_expr stage :=if Nat.eqb stage 0 then @Econst VarOrder.T(Fuint 5)[::false;false;false;false;false]else @Eref VarOrder.T(@Eid VarOrder.T(3180+N.of_nat stage)).
Definition rf_rd_mux_expr stage := @Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T(rf_rd_guard stage)))(@Eref VarOrder.T(@Eid VarOrder.T(rds_node(rf_rd_slice_at(rf_rd_candidate stage)))))(rf_rd_previous_expr stage).
Lemma rf_rd_mux_certificate stage :(stage<39)%coq_nat ->
 List.In(3181+N.of_nat stage,rf_rd_mux_expr stage)rf_nop_nodes /\(rf_rd_candidate stage<171)%coq_nat /\rds_high(rf_rd_slice_at(rf_rd_candidate stage))=11%nat /\rds_low(rf_rd_slice_at(rf_rd_candidate stage))=7%nat /\(rds_rank(rf_rd_slice_at(rf_rd_candidate stage))<=5)%coq_nat.
Proof. intro Bound.
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 114%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 115%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 116%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 117%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 118%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 119%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 120%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 121%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 122%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 123%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 124%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 125%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 126%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 127%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 128%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 129%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 130%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 131%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 132%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 133%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 134%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 135%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 136%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 137%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 138%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 139%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 140%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 141%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 142%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 143%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 144%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 145%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 146%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 147%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 148%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 149%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 150%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 151%nat);reflexivity|vm_compute;repeat split;lia]. }
destruct stage as[|stage]. {split;[apply(List.nth_error_In rf_nop_nodes 152%nat);reflexivity|vm_compute;repeat split;lia]. }
lia. Qed.
Lemma rf_rd_uint5_resize word :size word=5%nat ->zext_to 5(take 5 word)=word.
Proof. intro Size. rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity. Qed.
Lemma rf_rd_mux_step stage invalid old result instruction previous bit : (stage<39)%coq_nat ->size instruction=32%nat ->size previous=5%nat ->
 VM.find(rf_rd_guard stage)old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find(rds_node(rf_rd_slice_at(rf_rd_candidate stage)))old=Some(Gval(Fuint 5)(rf_instruction_rd instruction)) ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(rf_rd_previous_expr stage)old old=Some(Gval(Fuint 5)previous)) ->
 eval_type_of_expr(rf_rd_previous_expr stage)old=Some(Gtyp(Fuint 5)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(3181+N.of_nat stage)result=Some(Gval(Fuint 5)(if bit then rf_instruction_rd instruction else previous)).
Proof.
 intros Bound Size PrevSize Guard Candidate Previous PreviousType Step.
 destruct(rf_rd_mux_certificate stage Bound)as[Member _].
 eapply(reference_redirect_ground_step rf_nop_offsets rf_nop_nodes _ (rf_rd_mux_expr stage));[exact rf_nop_positions|exact rf_nop_safety|exact Member| |exact Step].
 intros site. unfold rf_rd_mux_expr. cbn[eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Guard.
 destruct bit;cbn[is_zero].
 - rewrite Candidate PreviousType. change(Some(Gval(Fuint 5)(zext_to 5(take 5(rf_instruction_rd instruction))))=Some(Gval(Fuint 5)(rf_instruction_rd instruction))). rewrite(rf_rd_uint5_resize _ (rf_instruction_rd_size instruction Size)). reflexivity.
 - rewrite Previous. unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref]. rewrite Candidate. change(Some(Gval(Fuint 5)(zext_to 5(take 5 previous)))=Some(Gval(Fuint 5)previous)). rewrite(rf_rd_uint5_resize _ PrevSize). reflexivity.
Qed.
Fixpoint rf_rd_enabled guards count :=match count with O=>false|S n=>guards n || rf_rd_enabled guards n end.
Definition rf_rd_fold instruction guards count :=if rf_rd_enabled guards count then rf_instruction_rd instruction else [::false;false;false;false;false].
Lemma rf_rd_fold_size instruction guards count :size instruction=32%nat ->size(rf_rd_fold instruction guards count)=5%nat.
Proof. intro Size. unfold rf_rd_fold. destruct(rf_rd_enabled guards count);[apply rf_instruction_rd_size;exact Size|reflexivity]. Qed.
Lemma rf_rd_fold_succ instruction guards count :rf_rd_fold instruction guards(S count)=if guards count then rf_instruction_rd instruction else rf_rd_fold instruction guards count.
Proof. unfold rf_rd_fold. cbn[rf_rd_enabled]. destruct(guards count);reflexivity. Qed.
From Coq Require Import NArith.
Theorem rf_reference_rd_mux_history invalid history (limit start:nat) instruction guards :size instruction=32%nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall stage t,(stage<39)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_rd_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall stage time,(stage<39)%coq_nat ->(Nat.add(Nat.add start 6)stage<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find(3181+N.of_nat stage)(history time)=Some(Gval(Fuint 5)(rf_rd_fold instruction guards(S stage))).
Proof.
 intros Size Instruction Guards Steps stage. induction stage as[|stage IH];intros[|time]Bound Lower Upper;try lia.
 - rewrite rf_rd_fold_succ. eapply(rf_rd_mux_step 0 invalid(history time)(history(S time))instruction(rf_rd_fold instruction guards 0)(guards 0)Bound Size);[reflexivity|exact(Guards 0%nat time ltac:(lia)ltac:(lia)ltac:(lia))| | | |apply Steps;lia].
   + destruct(rf_rd_mux_certificate 0 Bound)as[Member[Candidate[High[Low Rank]]]].
     pose proof(rf_reference_rd_slices_history invalid history limit start instruction Size Instruction Steps time(rf_rd_candidate 0)Candidate ltac:(lia)ltac:(lia))as Value.
     unfold rf_rd_slice_value in Value. rewrite High Low in Value. exact Value.
   + intros site. reflexivity.
   + reflexivity.
 - rewrite rf_rd_fold_succ. eapply(rf_rd_mux_step(S stage)invalid(history time)(history(S time))instruction(rf_rd_fold instruction guards(S stage))(guards(S stage))Bound Size);[apply rf_rd_fold_size;exact Size|exact(Guards(S stage)time ltac:(lia)ltac:(lia)ltac:(lia))| | | |apply Steps;lia].
   + destruct(rf_rd_mux_certificate(S stage)Bound)as[Member[Candidate[High[Low Rank]]]].
     pose proof(rf_reference_rd_slices_history invalid history limit start instruction Size Instruction Steps time(rf_rd_candidate(S stage))Candidate ltac:(lia)ltac:(lia))as Value.
     unfold rf_rd_slice_value in Value. rewrite High Low in Value. exact Value.
   + intros site. unfold rf_rd_previous_expr. cbn[eval_hfexpr_validif_policy eval_href_validif_policy Nat.eqb].
     replace(3180+N.of_nat(S stage))with(3181+N.of_nat stage)by(rewrite Nat2N.inj_succ;lia).
     apply IH;lia.
   + unfold rf_rd_previous_expr,eval_type_of_expr. cbn[Nat.eqb type_of_expr' eval_type_of_ref].
     replace(3180+N.of_nat(S stage))with(3181+N.of_nat stage)by(rewrite Nat2N.inj_succ;lia).
     rewrite(IH time ltac:(lia)ltac:(lia)ltac:(lia)). reflexivity.
Qed.
Lemma rf_rd_enabled_member guards count stage :(stage<count)%coq_nat ->guards stage=true ->rf_rd_enabled guards count=true.
Proof.
 revert stage. induction count as[|count IH];intros stage Bound Guard;[lia|].
 cbn[rf_rd_enabled]. destruct(Nat.eq_dec stage count)as[Same|Different].
 - subst stage. rewrite Guard. reflexivity.
 - rewrite(IH stage ltac:(lia)Guard). apply orbT.
Qed.
Lemma rf_reference_rd_exit invalid s0 s1 s2 word :size word=5%nat ->
 VM.find 3219 s0=Some(Gval(Fuint 5)word) ->VM.find 1707 s0=Some(Gval(Fuint 1)[::true]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find 3221 s2=Some(Gval(Fuint 5)word).
Proof.
 intros Size Word Active S1 S2.
 assert(Outer:VM.find 3220 s1=Some(Gval(Fuint 5)word)).
 { eapply(reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3220 rf_nop_expr_3220);[exact rf_nop_positions|exact rf_nop_safety|apply(List.nth_error_In rf_nop_nodes 153);reflexivity| |exact S1].
 intros site. cbn[rf_nop_expr_3220 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Active.
 cbn[is_zero]. rewrite Word. change(Some(Gval(Fuint 5)(zext_to 5(take 5 word)))=Some(Gval(Fuint 5)word)). rewrite(rf_rd_uint5_resize word Size). reflexivity. }
 eapply(reference_redirect_ground_step rf_nop_offsets rf_nop_nodes 3221 rf_nop_expr_3221);[exact rf_nop_positions|exact rf_nop_safety|apply(List.nth_error_In rf_nop_nodes 154);reflexivity| |exact S2].
 intros site. cbn[rf_nop_expr_3221 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Outer.
Qed.
Theorem rf_reference_rd_history invalid history (limit start:nat) instruction guards :size instruction=32%nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall stage t,(stage<39)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_rd_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::true])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(Nat.add start 46<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 3221(history time)=Some(Gval(Fuint 5)(rf_rd_fold instruction guards 39)).
Proof.
 intros Size Instruction Guards Active Steps[|[|time]]Lower Upper;try lia.
 eapply(rf_reference_rd_exit invalid(history time)(history(S time))(history(S(S time))));[apply rf_rd_fold_size;exact Size| |apply Active;lia|apply Steps;lia|apply Steps;lia].
 exact(rf_reference_rd_mux_history invalid history limit start instruction guards Size Instruction Guards Steps 38 time ltac:(lia)ltac:(lia)ltac:(lia)).
Qed.
Require Import ReferenceInstructionDecode LegalInstructionClass.
Definition rf_decode_disjoint_check := List.forallb(fun row=>List.forallb(fun col=>
 Nat.eqb row col || negb(N.eqb(N.land(reference_instruction_code row)(reference_instruction_mask col))(N.land(reference_instruction_code col)(reference_instruction_mask row))))(List.seq 0 48))(List.seq 0 37).
Lemma rf_decode_disjoint_checked :rf_decode_disjoint_check=true.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_decode_disjoint row col :(row<37)%coq_nat ->(col<48)%coq_nat ->row<>col ->
 N.land(reference_instruction_code row)(reference_instruction_mask col)<>N.land(reference_instruction_code col)(reference_instruction_mask row).
Proof.
 intros Row Col Different.
 pose proof rf_decode_disjoint_checked as Check. unfold rf_decode_disjoint_check in Check.
 rewrite List.forallb_forall in Check.
 specialize(Check row ltac:(apply List.in_seq;lia)).
 rewrite List.forallb_forall in Check. specialize(Check col ltac:(apply List.in_seq;lia)).
 assert(D:Nat.eqb row col=false)by(apply Nat.eqb_neq;exact Different).
 rewrite D in Check. cbn[orb]in Check.
 apply N.eqb_neq. apply Bool.negb_true_iff in Check. exact Check.
Qed.
Theorem rf_reference_decode_onehot instruction row col :(row<37)%coq_nat ->(col<48)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 N.eqb(reference_instruction_code col)(N.land(to_N instruction)(reference_instruction_mask col))=Nat.eqb col row.
Proof.
 intros Row Col Match. destruct(Nat.eq_dec col row)as[Same|Different].
 - subst col. rewrite Match Nat.eqb_refl N.eqb_refl. reflexivity.
 - rewrite(proj2(Nat.eqb_neq col row)Different). apply N.eqb_neq. intro Other.
   apply(rf_decode_disjoint row col Row Col ltac:(lia)).
   rewrite -Match Other -!N.land_assoc.
   rewrite(N.land_comm(reference_instruction_mask row)(reference_instruction_mask col)). reflexivity.
Qed.

Definition rf_rd_decoder_indices :seq nat :=[::0%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;21%nat;22%nat;29%nat;30%nat;31%nat;32%nat;33%nat;37%nat;38%nat;39%nat;40%nat;41%nat;42%nat;43%nat;44%nat;45%nat;46%nat;47%nat].
Definition rf_rd_decoder_index stage :=nth 0%nat rf_rd_decoder_indices stage.
Lemma rf_rd_decoder_certificate stage :(stage<39)%coq_nat ->(rf_rd_decoder_index stage<48)%coq_nat /\rf_rd_guard stage=reference_instruction_guard(rf_rd_decoder_index stage).
Proof. intro Bound. do 39(destruct stage as[|stage];[split;[vm_compute;lia|reflexivity]|]);lia. Qed.
Definition rf_rd_opcode_bit instruction stage :=N.eqb(reference_instruction_code(rf_rd_decoder_index stage))(N.land(to_N instruction)(reference_instruction_mask(rf_rd_decoder_index stage))).
Definition rf_isa_writes row :=Nat.ltb row 23 || (Nat.leb 29 row && Nat.ltb row 34).
Lemma rf_rd_enabled_ext guards other count :(forall stage,(stage<count)%coq_nat ->guards stage=other stage) ->rf_rd_enabled guards count=rf_rd_enabled other count.
Proof. intro Values. induction count as[|count IH];[reflexivity|]. cbn[rf_rd_enabled]. rewrite(Values count ltac:(lia)). rewrite IH;[reflexivity|intros stage Bound;apply Values;lia]. Qed.
Lemma rf_rd_onehot_writes row :(row<37)%coq_nat ->rf_rd_enabled(fun stage=>Nat.eqb(rf_rd_decoder_index stage)row)39=rf_isa_writes row.
Proof. intro Bound. do 37(destruct row as[|row];[reflexivity|]);lia. Qed.
Lemma rf_rd_legal_fold instruction row :(row<37)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 rf_rd_fold instruction(rf_rd_opcode_bit instruction)39=if rf_isa_writes row then rf_instruction_rd instruction else[::false;false;false;false;false].
Proof.
 intros Row Match. unfold rf_rd_fold.
 assert(Enabled:rf_rd_enabled(rf_rd_opcode_bit instruction)39=rf_rd_enabled(fun stage=>Nat.eqb(rf_rd_decoder_index stage)row)39).
 { apply rf_rd_enabled_ext. intros stage Stage. unfold rf_rd_opcode_bit.
   apply rf_reference_decode_onehot;[exact Row|exact(proj1(rf_rd_decoder_certificate stage Stage))|exact Match]. }
 rewrite Enabled(rf_rd_onehot_writes row Row). reflexivity.
Qed.
Theorem rf_reference_rd_class_history invalid history limit instruction row :size instruction=32%nat ->(row<37)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::true])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(48<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 3221(history time)=Some(Gval(Fuint 5)(if rf_isa_writes row then rf_instruction_rd instruction else[::false;false;false;false;false])).
Proof.
 intros Size Row Match Instruction Active Steps time Lower Upper.
 rewrite -(rf_rd_legal_fold instruction row Row Match).
 eapply(rf_reference_rd_history invalid history limit 2 instruction(rf_rd_opcode_bit instruction)Size);[intros t L U;apply Instruction;exact U| |exact Active|exact Steps|exact Lower|exact Upper].
 intros stage t Stage L U. destruct(rf_rd_decoder_certificate stage Stage)as[Bound Guard]. rewrite Guard.
 exact(reference_instruction_decode_history invalid history limit instruction(rf_rd_decoder_index stage)Bound Steps Instruction t L U).
Qed.
Require Import RFReferenceNopHistory RFReferenceWriteEffect RFWriteEffect.
Definition rf_write_decoder_index stage :=if Nat.ltb stage 23 then stage else if Nat.ltb stage 28 then Nat.add stage 6 else Nat.add stage 12.
Definition rf_write_opcode_bit instruction stage :=N.eqb(reference_instruction_code(rf_write_decoder_index stage))(N.land(to_N instruction)(reference_instruction_mask(rf_write_decoder_index stage))).
Lemma rf_write_decoder_certificate stage :(stage<36)%coq_nat ->(rf_write_decoder_index stage<48)%coq_nat /\rf_reference_chain_guard stage=reference_instruction_guard(rf_write_decoder_index stage).
Proof. intro Bound. do 36(destruct stage as[|stage];[split;[vm_compute;lia|vm_compute;reflexivity]|]);lia. Qed.
Definition rf_no_write_check :=List.forallb(fun row=>List.forallb(fun stage=>rf_isa_writes row || negb(Nat.eqb(rf_write_decoder_index stage)row))(List.seq 0 36))(List.seq 0 37).
Lemma rf_no_write_checked :rf_no_write_check=true.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_no_write_decoder row stage :(row<37)%coq_nat ->(stage<36)%coq_nat ->rf_isa_writes row=false ->Nat.eqb(rf_write_decoder_index stage)row=false.
Proof.
 intros Row Stage NoWrite. pose proof rf_no_write_checked as Check. unfold rf_no_write_check in Check.
 rewrite List.forallb_forall in Check. specialize(Check row ltac:(apply List.in_seq;lia)).
 rewrite List.forallb_forall in Check. specialize(Check stage ltac:(apply List.in_seq;lia)).
 rewrite NoWrite in Check. cbn[orb]in Check. apply Bool.negb_true_iff in Check. exact Check.
Qed.
Lemma rf_no_write_opcode instruction row stage :(row<37)%coq_nat ->(stage<36)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->rf_isa_writes row=false ->rf_write_opcode_bit instruction stage=false.
Proof.
 intros Row Stage Match NoWrite. unfold rf_write_opcode_bit.
 rewrite(rf_reference_decode_onehot instruction row(rf_write_decoder_index stage)Row(proj1(rf_write_decoder_certificate stage Stage))Match).
 exact(rf_no_write_decoder row stage Row Stage NoWrite).
Qed.
Lemma rf_reference_effect_disabled guards permissions words destination count :(forall stage,(stage<count)%coq_nat ->guards stage=false) ->rf_reference_effect guards permissions words destination count=RFNoWrite.
Proof.
 intro Disabled. induction count as[|count IH];[reflexivity|]. cbn[rf_reference_effect]. rewrite(Disabled count ltac:(lia)). cbn[andb]. apply IH. intros stage Bound. apply Disabled;lia.
Qed.
Theorem rf_reference_class_no_write instruction row permissions words destination :(row<37)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->rf_isa_writes row=false ->
 rf_reference_effect(rf_write_opcode_bit instruction)permissions words destination 36=RFNoWrite.
Proof.
 intros Row Match NoWrite. apply rf_reference_effect_disabled. intros stage Stage. exact(rf_no_write_opcode instruction row stage Row Stage Match NoWrite).
Qed.
Theorem rf_reference_class_no_write_guards_history invalid history limit instruction row :
 (row<37)%coq_nat ->N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->rf_isa_writes row=false ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall stage time,(stage<36)%coq_nat ->(2<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history time)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Row Match NoWrite Instruction Steps stage time Stage Lower Upper.
 destruct(rf_write_decoder_certificate stage Stage)as[Bound Guard]. rewrite Guard.
 pose proof(reference_instruction_decode_history invalid history limit instruction(rf_write_decoder_index stage)Bound Steps Instruction time Lower Upper)as Value.
 change(VM.find(reference_instruction_guard(rf_write_decoder_index stage))(history time)=Some(Gval(Fuint 1)[::rf_write_opcode_bit instruction stage]))in Value.
 rewrite(rf_no_write_opcode instruction row stage Row Stage Match NoWrite)in Value. exact Value.
Qed.
Require Import FormalRFDestination.
Theorem rf_dut_rd_history invalid history limit instruction :size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(2<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 785(history time)=Some(Gval(Fuint 5)(rf_instruction_rd instruction)).
Proof.
 intros Size Instruction Steps[|[|time]]Lower Upper;try lia.
 exact(rf_destination_port_after_two invalid(history time)(history(S time))(history(S(S time)))instruction Size(Instruction time ltac:(lia))(Steps time ltac:(lia))(Steps(S time)ltac:(lia))).
Qed.
Require Import MemoryRequestObservedSemantics FormalObservedHistory ObservedJointRegisterConcrete LoadTypeCorrespondence JointUpdateBoundaryHistory ReferenceControlStabilityHistory FormalLocalHistory.
Theorem rf_destination_class_observed memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 (row<37)%coq_nat ->N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find 785(top_environment observed)=Some(Gval(Fuint 5)(rf_instruction_rd instruction)) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(if rf_isa_writes row then rf_instruction_rd instruction else[::false;false;false;false;false])).
Proof.
 intros Observe Legal Instruction Enabled Row Match.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Inst:forall t,(t<=9259)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite <-(Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert(Enable:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::true])).
 { intros t Lower Upper. rewrite(reference_control_stable_1707_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat ltac:(lia)ltac:(lia)Upper ltac:(lia))Last. exact Enabled. }
 assert(Source:forall t,(205<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Lower Upper. exact(memory_reference_instruction_history _ history 9259 200 instruction true Size Steps Inst Enable t Lower Upper). }
 split.
 - rewrite <-Last. exact(rf_dut_rd_history _ history 9259 instruction Size Inst Steps 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)).
 - set h:=fun t=>history(Nat.add 9211 t).
   assert(LocalSteps:forall i,(i<48)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(h i)false(h i)flat_statements=Some(h(S i))).
   { intros i Bound. unfold h. replace(Nat.add 9211(S i))with(S(Nat.add 9211 i))by lia. apply Steps. eapply Nat.lt_le_trans;[apply Nat.add_lt_mono_l;exact Bound|vm_compute;lia]. }
   assert(LocalSource:forall i,(i<=48)%coq_nat ->VM.find 1884(h i)=Some(Gval(Fuint 32)instruction)).
   { intros i Bound. unfold h. apply Source;[eapply Nat.le_trans with(m:=9211%nat);[vm_compute;lia|apply Nat.le_add_r]|]. eapply Nat.le_trans;[apply Nat.add_le_mono_l;exact Bound|vm_compute;lia]. }
   assert(LocalEnable:forall i,(2<=i)%coq_nat ->(i<=48)%coq_nat ->VM.find 1707(h i)=Some(Gval(Fuint 1)[::true])).
   { intros i Lower Upper. unfold h. apply Enable;[eapply Nat.le_trans with(m:=9211%nat);[vm_compute;lia|apply Nat.le_add_r]|]. eapply Nat.le_trans;[apply Nat.add_le_mono_l;exact Upper|vm_compute;lia]. }
   pose proof(rf_reference_rd_class_history _ h 48 instruction row Size Row Match LocalSource LocalEnable LocalSteps 48 ltac:(lia)ltac:(lia))as Result.
   unfold h in Result. change(Nat.add 9211 48)with 9259%nat in Result. rewrite Last in Result. exact Result.
Qed.

Lemma rf_legal_class_row instruction :legal_instruction_classified instruction ->exists row,(row<37)%coq_nat /\N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row.
Proof.
 intros[mask[code[Member Match]]]. cbn[legal_instruction_classes List.In]in Member.
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 0%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 1%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 2%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 3%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 4%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 5%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 6%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 7%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 8%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 9%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 10%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 11%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 12%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 13%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 14%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 15%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 16%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 17%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 18%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 19%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 20%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 21%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 22%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 23%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 24%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 25%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 26%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 27%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 28%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 29%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 30%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 31%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 32%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 33%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 34%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 35%nat. split;[lia|exact Match]. }
destruct Member as[Equal|Member]. {injection Equal as MaskEqual CodeEqual. rewrite -MaskEqual -CodeEqual in Match. exists 36%nat. split;[lia|exact Match]. }
contradiction. Qed.
Require Import ReferenceIllegalObserved FormalLocalHistory.
Theorem rf_scalar_destination_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 exists row,(row<37)%coq_nat /\N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row /\
 VM.find 785(top_environment observed)=Some(Gval(Fuint 5)(rf_instruction_rd instruction)) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(if rf_isa_writes row then rf_instruction_rd instruction else[::false;false;false;false;false])).
Proof.
 intros Observe Legal Reset Instruction Active.
 destruct(rf_legal_class_row instruction(legal_observed_instruction_classified memory inputs k observed instruction Observe Legal Reset Instruction))as[row[Row Match]].
 exists row. split;[exact Row|]. split;[exact Match|]. exact(rf_destination_class_observed memory inputs k observed instruction row Observe Legal Instruction Active Row Match).
Qed.
