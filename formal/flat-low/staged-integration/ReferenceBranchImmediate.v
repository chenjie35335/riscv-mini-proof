Require Import CoreSocModel ComparisonNodes ReferenceImmediateTypes ReferenceLoadImmediate ReferenceRedirectSpine ReferenceControlStabilityHistory ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 SelectedNodeSafety.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma reference_immediate_same_history i inputs path history limit reset time :
 (i < 304)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find (reference_immediate_node i) (history time) = VM.find (reference_immediate_node i) (history (S time)).
Proof.
 intros Bound Resets Steps Lower Upper.
 destruct i as [|i];[change (VM.find 1942 (history time) = VM.find 1942 (history (S time)));apply (reference_control_stable_1942_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1943 (history time) = VM.find 1943 (history (S time)));apply (reference_control_stable_1943_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1947 (history time) = VM.find 1947 (history (S time)));apply (reference_control_stable_1947_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1948 (history time) = VM.find 1948 (history (S time)));apply (reference_control_stable_1948_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1952 (history time) = VM.find 1952 (history (S time)));apply (reference_control_stable_1952_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1953 (history time) = VM.find 1953 (history (S time)));apply (reference_control_stable_1953_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1975 (history time) = VM.find 1975 (history (S time)));apply (reference_control_stable_1975_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1976 (history time) = VM.find 1976 (history (S time)));apply (reference_control_stable_1976_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1977 (history time) = VM.find 1977 (history (S time)));apply (reference_control_stable_1977_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1981 (history time) = VM.find 1981 (history (S time)));apply (reference_control_stable_1981_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1982 (history time) = VM.find 1982 (history (S time)));apply (reference_control_stable_1982_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1983 (history time) = VM.find 1983 (history (S time)));apply (reference_control_stable_1983_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1987 (history time) = VM.find 1987 (history (S time)));apply (reference_control_stable_1987_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1988 (history time) = VM.find 1988 (history (S time)));apply (reference_control_stable_1988_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1989 (history time) = VM.find 1989 (history (S time)));apply (reference_control_stable_1989_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1993 (history time) = VM.find 1993 (history (S time)));apply (reference_control_stable_1993_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1994 (history time) = VM.find 1994 (history (S time)));apply (reference_control_stable_1994_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1995 (history time) = VM.find 1995 (history (S time)));apply (reference_control_stable_1995_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 1999 (history time) = VM.find 1999 (history (S time)));apply (reference_control_stable_1999_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2000 (history time) = VM.find 2000 (history (S time)));apply (reference_control_stable_2000_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2001 (history time) = VM.find 2001 (history (S time)));apply (reference_control_stable_2001_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2005 (history time) = VM.find 2005 (history (S time)));apply (reference_control_stable_2005_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2006 (history time) = VM.find 2006 (history (S time)));apply (reference_control_stable_2006_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2007 (history time) = VM.find 2007 (history (S time)));apply (reference_control_stable_2007_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2211 (history time) = VM.find 2211 (history (S time)));apply (reference_control_stable_2211_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2212 (history time) = VM.find 2212 (history (S time)));apply (reference_control_stable_2212_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2213 (history time) = VM.find 2213 (history (S time)));apply (reference_control_stable_2213_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2214 (history time) = VM.find 2214 (history (S time)));apply (reference_control_stable_2214_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2215 (history time) = VM.find 2215 (history (S time)));apply (reference_control_stable_2215_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2216 (history time) = VM.find 2216 (history (S time)));apply (reference_control_stable_2216_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2217 (history time) = VM.find 2217 (history (S time)));apply (reference_control_stable_2217_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2218 (history time) = VM.find 2218 (history (S time)));apply (reference_control_stable_2218_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2219 (history time) = VM.find 2219 (history (S time)));apply (reference_control_stable_2219_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2220 (history time) = VM.find 2220 (history (S time)));apply (reference_control_stable_2220_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2221 (history time) = VM.find 2221 (history (S time)));apply (reference_control_stable_2221_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2222 (history time) = VM.find 2222 (history (S time)));apply (reference_control_stable_2222_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2223 (history time) = VM.find 2223 (history (S time)));apply (reference_control_stable_2223_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2224 (history time) = VM.find 2224 (history (S time)));apply (reference_control_stable_2224_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2225 (history time) = VM.find 2225 (history (S time)));apply (reference_control_stable_2225_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2226 (history time) = VM.find 2226 (history (S time)));apply (reference_control_stable_2226_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2227 (history time) = VM.find 2227 (history (S time)));apply (reference_control_stable_2227_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2228 (history time) = VM.find 2228 (history (S time)));apply (reference_control_stable_2228_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2229 (history time) = VM.find 2229 (history (S time)));apply (reference_control_stable_2229_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2230 (history time) = VM.find 2230 (history (S time)));apply (reference_control_stable_2230_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2231 (history time) = VM.find 2231 (history (S time)));apply (reference_control_stable_2231_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2232 (history time) = VM.find 2232 (history (S time)));apply (reference_control_stable_2232_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2233 (history time) = VM.find 2233 (history (S time)));apply (reference_control_stable_2233_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2234 (history time) = VM.find 2234 (history (S time)));apply (reference_control_stable_2234_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2235 (history time) = VM.find 2235 (history (S time)));apply (reference_control_stable_2235_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2236 (history time) = VM.find 2236 (history (S time)));apply (reference_control_stable_2236_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2237 (history time) = VM.find 2237 (history (S time)));apply (reference_control_stable_2237_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2238 (history time) = VM.find 2238 (history (S time)));apply (reference_control_stable_2238_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2239 (history time) = VM.find 2239 (history (S time)));apply (reference_control_stable_2239_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2240 (history time) = VM.find 2240 (history (S time)));apply (reference_control_stable_2240_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2241 (history time) = VM.find 2241 (history (S time)));apply (reference_control_stable_2241_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2242 (history time) = VM.find 2242 (history (S time)));apply (reference_control_stable_2242_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2243 (history time) = VM.find 2243 (history (S time)));apply (reference_control_stable_2243_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2244 (history time) = VM.find 2244 (history (S time)));apply (reference_control_stable_2244_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2245 (history time) = VM.find 2245 (history (S time)));apply (reference_control_stable_2245_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2246 (history time) = VM.find 2246 (history (S time)));apply (reference_control_stable_2246_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2247 (history time) = VM.find 2247 (history (S time)));apply (reference_control_stable_2247_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2248 (history time) = VM.find 2248 (history (S time)));apply (reference_control_stable_2248_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2251 (history time) = VM.find 2251 (history (S time)));apply (reference_control_stable_2251_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2252 (history time) = VM.find 2252 (history (S time)));apply (reference_control_stable_2252_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2255 (history time) = VM.find 2255 (history (S time)));apply (reference_control_stable_2255_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2256 (history time) = VM.find 2256 (history (S time)));apply (reference_control_stable_2256_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2259 (history time) = VM.find 2259 (history (S time)));apply (reference_control_stable_2259_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2260 (history time) = VM.find 2260 (history (S time)));apply (reference_control_stable_2260_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2261 (history time) = VM.find 2261 (history (S time)));apply (reference_control_stable_2261_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2262 (history time) = VM.find 2262 (history (S time)));apply (reference_control_stable_2262_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2263 (history time) = VM.find 2263 (history (S time)));apply (reference_control_stable_2263_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2264 (history time) = VM.find 2264 (history (S time)));apply (reference_control_stable_2264_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2265 (history time) = VM.find 2265 (history (S time)));apply (reference_control_stable_2265_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2266 (history time) = VM.find 2266 (history (S time)));apply (reference_control_stable_2266_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2267 (history time) = VM.find 2267 (history (S time)));apply (reference_control_stable_2267_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2268 (history time) = VM.find 2268 (history (S time)));apply (reference_control_stable_2268_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2269 (history time) = VM.find 2269 (history (S time)));apply (reference_control_stable_2269_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2270 (history time) = VM.find 2270 (history (S time)));apply (reference_control_stable_2270_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2271 (history time) = VM.find 2271 (history (S time)));apply (reference_control_stable_2271_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2272 (history time) = VM.find 2272 (history (S time)));apply (reference_control_stable_2272_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2273 (history time) = VM.find 2273 (history (S time)));apply (reference_control_stable_2273_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2274 (history time) = VM.find 2274 (history (S time)));apply (reference_control_stable_2274_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2275 (history time) = VM.find 2275 (history (S time)));apply (reference_control_stable_2275_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2276 (history time) = VM.find 2276 (history (S time)));apply (reference_control_stable_2276_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2277 (history time) = VM.find 2277 (history (S time)));apply (reference_control_stable_2277_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2278 (history time) = VM.find 2278 (history (S time)));apply (reference_control_stable_2278_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2279 (history time) = VM.find 2279 (history (S time)));apply (reference_control_stable_2279_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2280 (history time) = VM.find 2280 (history (S time)));apply (reference_control_stable_2280_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2281 (history time) = VM.find 2281 (history (S time)));apply (reference_control_stable_2281_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2282 (history time) = VM.find 2282 (history (S time)));apply (reference_control_stable_2282_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2283 (history time) = VM.find 2283 (history (S time)));apply (reference_control_stable_2283_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2286 (history time) = VM.find 2286 (history (S time)));apply (reference_control_stable_2286_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2287 (history time) = VM.find 2287 (history (S time)));apply (reference_control_stable_2287_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2288 (history time) = VM.find 2288 (history (S time)));apply (reference_control_stable_2288_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2291 (history time) = VM.find 2291 (history (S time)));apply (reference_control_stable_2291_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2292 (history time) = VM.find 2292 (history (S time)));apply (reference_control_stable_2292_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2293 (history time) = VM.find 2293 (history (S time)));apply (reference_control_stable_2293_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2296 (history time) = VM.find 2296 (history (S time)));apply (reference_control_stable_2296_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2297 (history time) = VM.find 2297 (history (S time)));apply (reference_control_stable_2297_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2300 (history time) = VM.find 2300 (history (S time)));apply (reference_control_stable_2300_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2301 (history time) = VM.find 2301 (history (S time)));apply (reference_control_stable_2301_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2304 (history time) = VM.find 2304 (history (S time)));apply (reference_control_stable_2304_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2305 (history time) = VM.find 2305 (history (S time)));apply (reference_control_stable_2305_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2308 (history time) = VM.find 2308 (history (S time)));apply (reference_control_stable_2308_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2309 (history time) = VM.find 2309 (history (S time)));apply (reference_control_stable_2309_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2312 (history time) = VM.find 2312 (history (S time)));apply (reference_control_stable_2312_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2313 (history time) = VM.find 2313 (history (S time)));apply (reference_control_stable_2313_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2316 (history time) = VM.find 2316 (history (S time)));apply (reference_control_stable_2316_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2317 (history time) = VM.find 2317 (history (S time)));apply (reference_control_stable_2317_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2318 (history time) = VM.find 2318 (history (S time)));apply (reference_control_stable_2318_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2319 (history time) = VM.find 2319 (history (S time)));apply (reference_control_stable_2319_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2320 (history time) = VM.find 2320 (history (S time)));apply (reference_control_stable_2320_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2321 (history time) = VM.find 2321 (history (S time)));apply (reference_control_stable_2321_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2322 (history time) = VM.find 2322 (history (S time)));apply (reference_control_stable_2322_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2323 (history time) = VM.find 2323 (history (S time)));apply (reference_control_stable_2323_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2324 (history time) = VM.find 2324 (history (S time)));apply (reference_control_stable_2324_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2325 (history time) = VM.find 2325 (history (S time)));apply (reference_control_stable_2325_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2326 (history time) = VM.find 2326 (history (S time)));apply (reference_control_stable_2326_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2327 (history time) = VM.find 2327 (history (S time)));apply (reference_control_stable_2327_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2328 (history time) = VM.find 2328 (history (S time)));apply (reference_control_stable_2328_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2329 (history time) = VM.find 2329 (history (S time)));apply (reference_control_stable_2329_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2330 (history time) = VM.find 2330 (history (S time)));apply (reference_control_stable_2330_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2331 (history time) = VM.find 2331 (history (S time)));apply (reference_control_stable_2331_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2332 (history time) = VM.find 2332 (history (S time)));apply (reference_control_stable_2332_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2333 (history time) = VM.find 2333 (history (S time)));apply (reference_control_stable_2333_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2334 (history time) = VM.find 2334 (history (S time)));apply (reference_control_stable_2334_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2335 (history time) = VM.find 2335 (history (S time)));apply (reference_control_stable_2335_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2336 (history time) = VM.find 2336 (history (S time)));apply (reference_control_stable_2336_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2337 (history time) = VM.find 2337 (history (S time)));apply (reference_control_stable_2337_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2338 (history time) = VM.find 2338 (history (S time)));apply (reference_control_stable_2338_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2339 (history time) = VM.find 2339 (history (S time)));apply (reference_control_stable_2339_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2340 (history time) = VM.find 2340 (history (S time)));apply (reference_control_stable_2340_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2341 (history time) = VM.find 2341 (history (S time)));apply (reference_control_stable_2341_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2342 (history time) = VM.find 2342 (history (S time)));apply (reference_control_stable_2342_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2343 (history time) = VM.find 2343 (history (S time)));apply (reference_control_stable_2343_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2344 (history time) = VM.find 2344 (history (S time)));apply (reference_control_stable_2344_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2345 (history time) = VM.find 2345 (history (S time)));apply (reference_control_stable_2345_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2346 (history time) = VM.find 2346 (history (S time)));apply (reference_control_stable_2346_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2347 (history time) = VM.find 2347 (history (S time)));apply (reference_control_stable_2347_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2348 (history time) = VM.find 2348 (history (S time)));apply (reference_control_stable_2348_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2349 (history time) = VM.find 2349 (history (S time)));apply (reference_control_stable_2349_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2350 (history time) = VM.find 2350 (history (S time)));apply (reference_control_stable_2350_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2351 (history time) = VM.find 2351 (history (S time)));apply (reference_control_stable_2351_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2352 (history time) = VM.find 2352 (history (S time)));apply (reference_control_stable_2352_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2353 (history time) = VM.find 2353 (history (S time)));apply (reference_control_stable_2353_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2354 (history time) = VM.find 2354 (history (S time)));apply (reference_control_stable_2354_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2355 (history time) = VM.find 2355 (history (S time)));apply (reference_control_stable_2355_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2358 (history time) = VM.find 2358 (history (S time)));apply (reference_control_stable_2358_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2359 (history time) = VM.find 2359 (history (S time)));apply (reference_control_stable_2359_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2360 (history time) = VM.find 2360 (history (S time)));apply (reference_control_stable_2360_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2361 (history time) = VM.find 2361 (history (S time)));apply (reference_control_stable_2361_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2362 (history time) = VM.find 2362 (history (S time)));apply (reference_control_stable_2362_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2363 (history time) = VM.find 2363 (history (S time)));apply (reference_control_stable_2363_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2364 (history time) = VM.find 2364 (history (S time)));apply (reference_control_stable_2364_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2365 (history time) = VM.find 2365 (history (S time)));apply (reference_control_stable_2365_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2366 (history time) = VM.find 2366 (history (S time)));apply (reference_control_stable_2366_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2367 (history time) = VM.find 2367 (history (S time)));apply (reference_control_stable_2367_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2368 (history time) = VM.find 2368 (history (S time)));apply (reference_control_stable_2368_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2369 (history time) = VM.find 2369 (history (S time)));apply (reference_control_stable_2369_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2370 (history time) = VM.find 2370 (history (S time)));apply (reference_control_stable_2370_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2371 (history time) = VM.find 2371 (history (S time)));apply (reference_control_stable_2371_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2372 (history time) = VM.find 2372 (history (S time)));apply (reference_control_stable_2372_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2373 (history time) = VM.find 2373 (history (S time)));apply (reference_control_stable_2373_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2374 (history time) = VM.find 2374 (history (S time)));apply (reference_control_stable_2374_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2375 (history time) = VM.find 2375 (history (S time)));apply (reference_control_stable_2375_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2376 (history time) = VM.find 2376 (history (S time)));apply (reference_control_stable_2376_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2377 (history time) = VM.find 2377 (history (S time)));apply (reference_control_stable_2377_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2378 (history time) = VM.find 2378 (history (S time)));apply (reference_control_stable_2378_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2379 (history time) = VM.find 2379 (history (S time)));apply (reference_control_stable_2379_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2380 (history time) = VM.find 2380 (history (S time)));apply (reference_control_stable_2380_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2381 (history time) = VM.find 2381 (history (S time)));apply (reference_control_stable_2381_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2382 (history time) = VM.find 2382 (history (S time)));apply (reference_control_stable_2382_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2383 (history time) = VM.find 2383 (history (S time)));apply (reference_control_stable_2383_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2384 (history time) = VM.find 2384 (history (S time)));apply (reference_control_stable_2384_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2385 (history time) = VM.find 2385 (history (S time)));apply (reference_control_stable_2385_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2386 (history time) = VM.find 2386 (history (S time)));apply (reference_control_stable_2386_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2387 (history time) = VM.find 2387 (history (S time)));apply (reference_control_stable_2387_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2388 (history time) = VM.find 2388 (history (S time)));apply (reference_control_stable_2388_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2389 (history time) = VM.find 2389 (history (S time)));apply (reference_control_stable_2389_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2390 (history time) = VM.find 2390 (history (S time)));apply (reference_control_stable_2390_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2391 (history time) = VM.find 2391 (history (S time)));apply (reference_control_stable_2391_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2392 (history time) = VM.find 2392 (history (S time)));apply (reference_control_stable_2392_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2393 (history time) = VM.find 2393 (history (S time)));apply (reference_control_stable_2393_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2394 (history time) = VM.find 2394 (history (S time)));apply (reference_control_stable_2394_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2395 (history time) = VM.find 2395 (history (S time)));apply (reference_control_stable_2395_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2396 (history time) = VM.find 2396 (history (S time)));apply (reference_control_stable_2396_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2397 (history time) = VM.find 2397 (history (S time)));apply (reference_control_stable_2397_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2398 (history time) = VM.find 2398 (history (S time)));apply (reference_control_stable_2398_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2399 (history time) = VM.find 2399 (history (S time)));apply (reference_control_stable_2399_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2400 (history time) = VM.find 2400 (history (S time)));apply (reference_control_stable_2400_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2401 (history time) = VM.find 2401 (history (S time)));apply (reference_control_stable_2401_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2404 (history time) = VM.find 2404 (history (S time)));apply (reference_control_stable_2404_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2405 (history time) = VM.find 2405 (history (S time)));apply (reference_control_stable_2405_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2406 (history time) = VM.find 2406 (history (S time)));apply (reference_control_stable_2406_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2407 (history time) = VM.find 2407 (history (S time)));apply (reference_control_stable_2407_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2408 (history time) = VM.find 2408 (history (S time)));apply (reference_control_stable_2408_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2409 (history time) = VM.find 2409 (history (S time)));apply (reference_control_stable_2409_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2412 (history time) = VM.find 2412 (history (S time)));apply (reference_control_stable_2412_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2413 (history time) = VM.find 2413 (history (S time)));apply (reference_control_stable_2413_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2414 (history time) = VM.find 2414 (history (S time)));apply (reference_control_stable_2414_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2415 (history time) = VM.find 2415 (history (S time)));apply (reference_control_stable_2415_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2416 (history time) = VM.find 2416 (history (S time)));apply (reference_control_stable_2416_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2417 (history time) = VM.find 2417 (history (S time)));apply (reference_control_stable_2417_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2420 (history time) = VM.find 2420 (history (S time)));apply (reference_control_stable_2420_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2421 (history time) = VM.find 2421 (history (S time)));apply (reference_control_stable_2421_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2422 (history time) = VM.find 2422 (history (S time)));apply (reference_control_stable_2422_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2423 (history time) = VM.find 2423 (history (S time)));apply (reference_control_stable_2423_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2424 (history time) = VM.find 2424 (history (S time)));apply (reference_control_stable_2424_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2425 (history time) = VM.find 2425 (history (S time)));apply (reference_control_stable_2425_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2428 (history time) = VM.find 2428 (history (S time)));apply (reference_control_stable_2428_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2429 (history time) = VM.find 2429 (history (S time)));apply (reference_control_stable_2429_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2430 (history time) = VM.find 2430 (history (S time)));apply (reference_control_stable_2430_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2431 (history time) = VM.find 2431 (history (S time)));apply (reference_control_stable_2431_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2432 (history time) = VM.find 2432 (history (S time)));apply (reference_control_stable_2432_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2433 (history time) = VM.find 2433 (history (S time)));apply (reference_control_stable_2433_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2436 (history time) = VM.find 2436 (history (S time)));apply (reference_control_stable_2436_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2437 (history time) = VM.find 2437 (history (S time)));apply (reference_control_stable_2437_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2438 (history time) = VM.find 2438 (history (S time)));apply (reference_control_stable_2438_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2439 (history time) = VM.find 2439 (history (S time)));apply (reference_control_stable_2439_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2440 (history time) = VM.find 2440 (history (S time)));apply (reference_control_stable_2440_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2441 (history time) = VM.find 2441 (history (S time)));apply (reference_control_stable_2441_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2444 (history time) = VM.find 2444 (history (S time)));apply (reference_control_stable_2444_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2445 (history time) = VM.find 2445 (history (S time)));apply (reference_control_stable_2445_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2448 (history time) = VM.find 2448 (history (S time)));apply (reference_control_stable_2448_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2449 (history time) = VM.find 2449 (history (S time)));apply (reference_control_stable_2449_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2450 (history time) = VM.find 2450 (history (S time)));apply (reference_control_stable_2450_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2451 (history time) = VM.find 2451 (history (S time)));apply (reference_control_stable_2451_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2452 (history time) = VM.find 2452 (history (S time)));apply (reference_control_stable_2452_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2453 (history time) = VM.find 2453 (history (S time)));apply (reference_control_stable_2453_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2454 (history time) = VM.find 2454 (history (S time)));apply (reference_control_stable_2454_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2455 (history time) = VM.find 2455 (history (S time)));apply (reference_control_stable_2455_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2456 (history time) = VM.find 2456 (history (S time)));apply (reference_control_stable_2456_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2457 (history time) = VM.find 2457 (history (S time)));apply (reference_control_stable_2457_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2458 (history time) = VM.find 2458 (history (S time)));apply (reference_control_stable_2458_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2459 (history time) = VM.find 2459 (history (S time)));apply (reference_control_stable_2459_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2460 (history time) = VM.find 2460 (history (S time)));apply (reference_control_stable_2460_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2461 (history time) = VM.find 2461 (history (S time)));apply (reference_control_stable_2461_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2462 (history time) = VM.find 2462 (history (S time)));apply (reference_control_stable_2462_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2463 (history time) = VM.find 2463 (history (S time)));apply (reference_control_stable_2463_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2464 (history time) = VM.find 2464 (history (S time)));apply (reference_control_stable_2464_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2465 (history time) = VM.find 2465 (history (S time)));apply (reference_control_stable_2465_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2466 (history time) = VM.find 2466 (history (S time)));apply (reference_control_stable_2466_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2469 (history time) = VM.find 2469 (history (S time)));apply (reference_control_stable_2469_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2470 (history time) = VM.find 2470 (history (S time)));apply (reference_control_stable_2470_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2473 (history time) = VM.find 2473 (history (S time)));apply (reference_control_stable_2473_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2476 (history time) = VM.find 2476 (history (S time)));apply (reference_control_stable_2476_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2477 (history time) = VM.find 2477 (history (S time)));apply (reference_control_stable_2477_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2478 (history time) = VM.find 2478 (history (S time)));apply (reference_control_stable_2478_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2479 (history time) = VM.find 2479 (history (S time)));apply (reference_control_stable_2479_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2480 (history time) = VM.find 2480 (history (S time)));apply (reference_control_stable_2480_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2481 (history time) = VM.find 2481 (history (S time)));apply (reference_control_stable_2481_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2482 (history time) = VM.find 2482 (history (S time)));apply (reference_control_stable_2482_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2483 (history time) = VM.find 2483 (history (S time)));apply (reference_control_stable_2483_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2484 (history time) = VM.find 2484 (history (S time)));apply (reference_control_stable_2484_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2487 (history time) = VM.find 2487 (history (S time)));apply (reference_control_stable_2487_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2488 (history time) = VM.find 2488 (history (S time)));apply (reference_control_stable_2488_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2491 (history time) = VM.find 2491 (history (S time)));apply (reference_control_stable_2491_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2492 (history time) = VM.find 2492 (history (S time)));apply (reference_control_stable_2492_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2495 (history time) = VM.find 2495 (history (S time)));apply (reference_control_stable_2495_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2496 (history time) = VM.find 2496 (history (S time)));apply (reference_control_stable_2496_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2499 (history time) = VM.find 2499 (history (S time)));apply (reference_control_stable_2499_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2500 (history time) = VM.find 2500 (history (S time)));apply (reference_control_stable_2500_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2503 (history time) = VM.find 2503 (history (S time)));apply (reference_control_stable_2503_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2504 (history time) = VM.find 2504 (history (S time)));apply (reference_control_stable_2504_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2507 (history time) = VM.find 2507 (history (S time)));apply (reference_control_stable_2507_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2508 (history time) = VM.find 2508 (history (S time)));apply (reference_control_stable_2508_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2511 (history time) = VM.find 2511 (history (S time)));apply (reference_control_stable_2511_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2512 (history time) = VM.find 2512 (history (S time)));apply (reference_control_stable_2512_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2515 (history time) = VM.find 2515 (history (S time)));apply (reference_control_stable_2515_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2516 (history time) = VM.find 2516 (history (S time)));apply (reference_control_stable_2516_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2519 (history time) = VM.find 2519 (history (S time)));apply (reference_control_stable_2519_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2520 (history time) = VM.find 2520 (history (S time)));apply (reference_control_stable_2520_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2521 (history time) = VM.find 2521 (history (S time)));apply (reference_control_stable_2521_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2522 (history time) = VM.find 2522 (history (S time)));apply (reference_control_stable_2522_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2523 (history time) = VM.find 2523 (history (S time)));apply (reference_control_stable_2523_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2524 (history time) = VM.find 2524 (history (S time)));apply (reference_control_stable_2524_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2525 (history time) = VM.find 2525 (history (S time)));apply (reference_control_stable_2525_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2526 (history time) = VM.find 2526 (history (S time)));apply (reference_control_stable_2526_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2527 (history time) = VM.find 2527 (history (S time)));apply (reference_control_stable_2527_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2528 (history time) = VM.find 2528 (history (S time)));apply (reference_control_stable_2528_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2529 (history time) = VM.find 2529 (history (S time)));apply (reference_control_stable_2529_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2530 (history time) = VM.find 2530 (history (S time)));apply (reference_control_stable_2530_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2531 (history time) = VM.find 2531 (history (S time)));apply (reference_control_stable_2531_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2532 (history time) = VM.find 2532 (history (S time)));apply (reference_control_stable_2532_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2533 (history time) = VM.find 2533 (history (S time)));apply (reference_control_stable_2533_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2534 (history time) = VM.find 2534 (history (S time)));apply (reference_control_stable_2534_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2535 (history time) = VM.find 2535 (history (S time)));apply (reference_control_stable_2535_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2536 (history time) = VM.find 2536 (history (S time)));apply (reference_control_stable_2536_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2537 (history time) = VM.find 2537 (history (S time)));apply (reference_control_stable_2537_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2538 (history time) = VM.find 2538 (history (S time)));apply (reference_control_stable_2538_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2539 (history time) = VM.find 2539 (history (S time)));apply (reference_control_stable_2539_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2540 (history time) = VM.find 2540 (history (S time)));apply (reference_control_stable_2540_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2541 (history time) = VM.find 2541 (history (S time)));apply (reference_control_stable_2541_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2542 (history time) = VM.find 2542 (history (S time)));apply (reference_control_stable_2542_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2543 (history time) = VM.find 2543 (history (S time)));apply (reference_control_stable_2543_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2544 (history time) = VM.find 2544 (history (S time)));apply (reference_control_stable_2544_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2545 (history time) = VM.find 2545 (history (S time)));apply (reference_control_stable_2545_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2546 (history time) = VM.find 2546 (history (S time)));apply (reference_control_stable_2546_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2547 (history time) = VM.find 2547 (history (S time)));apply (reference_control_stable_2547_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2548 (history time) = VM.find 2548 (history (S time)));apply (reference_control_stable_2548_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2549 (history time) = VM.find 2549 (history (S time)));apply (reference_control_stable_2549_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2550 (history time) = VM.find 2550 (history (S time)));apply (reference_control_stable_2550_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2551 (history time) = VM.find 2551 (history (S time)));apply (reference_control_stable_2551_history inputs path history limit reset Resets Steps time (S time));lia|].
 destruct i as [|i];[change (VM.find 2552 (history time) = VM.find 2552 (history (S time)));apply (reference_control_stable_2552_history inputs path history limit reset Resets Steps time (S time));lia|].
 lia.
Qed.
Theorem reference_immediate_value_history i inputs path history limit reset time width word :
 (i < 304)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories (reference_immediate_expression i) (history time) (history time) = Some (Gval (Fuint width) word)) ->
 VM.find (reference_immediate_node i) (history time) = Some (Gval (Fuint width) word).
Proof.
 intros Bound Resets Steps Lower Upper Eval.
 rewrite (reference_immediate_same_history i inputs path history limit reset time Bound Resets Steps Lower Upper).
 eapply (reference_redirect_ground_step (reference_immediate_offsets i) (reference_immediate_nodes i) _ (reference_immediate_expression i));
 [unfold reference_immediate_offsets,reference_immediate_nodes;destruct (nth 2%nat reference_immediate_groups i) as [|[|g]];[exact reference_control_0_positions|exact reference_control_1_positions|exact reference_control_2_positions]
 |unfold reference_immediate_offsets;destruct (nth 2%nat reference_immediate_groups i) as [|[|g]];[exact reference_control_0_safety|exact reference_control_1_safety|exact reference_control_2_safety]
 |apply reference_immediate_member;exact Bound|exact Eval|apply Steps;lia].
Qed.
(* Branch and JAL composition. *)
Require Import ReferenceLoadImmediate ReferenceControlExpressions DUTRedirectDecode.
Theorem immediate_stable_mux_fallback invalid old current count width word prefix (node guard yes:nat->VarOrder.T) :
 size word = width ->
 (forall n, (n < count)%coq_nat -> VM.find (node n) old = VM.find (node n) current) ->
 (forall n, (n < count)%coq_nat -> forall value,
   (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories
    (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (guard n)))
     (@Eref VarOrder.T (@Eid VarOrder.T (yes n)))
     (@Eref VarOrder.T (@Eid VarOrder.T (match n with O => prefix | S before => node before end)))) old old = Some (Gval (Fuint width) value)) ->
   VM.find (node n) current = Some (Gval (Fuint width) value)) ->
 (forall n, (n < count)%coq_nat -> VM.find (guard n) old = Some (Gval (Fuint 1) [::false])) ->
 (forall n, (n < count)%coq_nat -> exists value, VM.find (yes n) old = Some value /\ type_of_val value = Gtyp (Fuint width)) ->
 VM.find prefix old = Some (Gval (Fuint width) word) ->
 forall n, (n < count)%coq_nat -> VM.find (node n) old = Some (Gval (Fuint width) word).
Proof.
 intros Size Stable Node Guard YesType Source n. induction n as [|n IH];intro Upper.
 - rewrite (Stable 0%nat Upper). apply (Node 0%nat Upper word). intro site.
   destruct (YesType 0%nat Upper) as [other [Other Typed]].
   eapply (immediate_selected_mux _ _ _ _ _ _ _ word other false);[exact Size|exact(Guard 0%nat Upper)|exact Source|exact Other|exact Typed].
 - pose proof(IH ltac:(lia))as Previous. rewrite(Stable(S n)Upper). apply(Node(S n)Upper word). intro site.
   destruct(YesType(S n)Upper)as[other[Other Typed]].
   eapply(immediate_selected_mux _ _ _ _ _ _ _ word other false);[exact Size|exact(Guard(S n)Upper)|exact Previous|exact Other|exact Typed].
Qed.
Lemma reference_immediate_rank_bound i : (i<304)%coq_nat -> (reference_immediate_rank i<=100)%coq_nat.
Proof. do 304 (destruct i as[|i];[vm_compute;lia|]);lia. Qed.
Theorem reference_immediate_typed_history i invalid history limit time :
 (i<304)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<=limit)%coq_nat ->
 exists value,VM.find(reference_immediate_node i)(history time)=Some value /\type_of_val value=Gtyp(Fuint(reference_immediate_width i)).
Proof.
 intros Bound Steps Source Lower Upper. eapply(reference_immediate_types_history invalid history limit 200 Steps Source i Bound time);[|exact Upper].
 pose proof(reference_immediate_rank_bound i Bound);lia.
Qed.
Theorem reference_jal_raw_fields_history inputs path history limit reset time instruction :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find 2360(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction))) /\
 VM.find 2450(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction))) /\
 VM.find 2455(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction))) /\
 VM.find 2461(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction))).
Proof.
 intros Resets Steps Lower Upper Source.
 assert(V2358:VM.find 2358(history time)=Some(Gval(Fuint 31)(take 31 instruction))).
 { eapply(reference_immediate_value_history 147 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2358 (history time)(history time)=Some(Gval(Fuint 31)(take 31 instruction))).
 cbn[reference_control_expr_2358 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn. reflexivity. }
 assert(V2359:VM.find 2359(history time)=Some(Gval(Fuint 21)(take 21 instruction))).
 { eapply(reference_immediate_value_history 148 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2359 (history time)(history time)=Some(Gval(Fuint 21)(take 21 instruction))).
 cbn[reference_control_expr_2359 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2358. cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn. reflexivity. }
 assert(V2360:VM.find 2360(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 149 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2360 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 cbn[reference_control_expr_2360 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2359. cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn. reflexivity. }
 assert(V2450:VM.find 2450(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 { eapply(reference_immediate_value_history 225 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2450 (history time)(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2450 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn. reflexivity. }
 assert(V2454:VM.find 2454(history time)=Some(Gval(Fuint 20)(take 20 instruction))).
 { eapply(reference_immediate_value_history 229 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2454 (history time)(history time)=Some(Gval(Fuint 20)(take 20 instruction))).
 cbn[reference_control_expr_2454 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2359. cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn. reflexivity. }
 assert(V2455:VM.find 2455(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))).
 { eapply(reference_immediate_value_history 230 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2455 (history time)(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))).
 cbn[reference_control_expr_2455 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2454. cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn. reflexivity. }
 assert(V2461:VM.find 2461(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))).
 { eapply(reference_immediate_value_history 236 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2461 (history time)(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))).
 cbn[reference_control_expr_2461 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2358. cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn. reflexivity. }
 repeat split;assumption.
Qed.
(* Selected JAL fields. *)
Theorem reference_jal_selected_fields_history inputs path history limit reset time instruction :
 size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 2357(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall guard,List.In guard [::2004;1998;1992;1986;1980;1974] ->VM.find guard(history time)=Some(Gval(Fuint 1)[::false])) ->
VM.find 2369(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction))) /\
 VM.find 2453(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction))) /\
 VM.find 2458(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction))) /\
 VM.find 2464(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction))).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Jal Branch.
 destruct(reference_jal_raw_fields_history inputs path history limit reset time instruction Resets Steps Lower Upper ltac:(apply Source;lia))as[V2360[V2450[V2455 V2461]]].
 assert(TypedSource:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)).
 { intros t L U;exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 assert(V2361:VM.find 2361(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 150 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2361 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 cbn[reference_control_expr_2361 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Jal;cbn;rewrite V2360.
 change(adapt_hvalue_as_type(Gval(Fuint 1)(drop 20(take 21 instruction)))(Gtyp(Fuint 1))=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))). apply dut_decode_adapt. rewrite size_drop size_take Size;reflexivity. }
 assert(V2362:VM.find 2362(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 151 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2362 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 destruct(reference_immediate_typed_history 146 _ history limit time ltac:(lia) Steps TypedSource Lower ltac:(lia))as[other[Other Typed]].
 change(VM.find 2355(history time)=Some other)in Other. change(type_of_val other=Gtyp(Fuint 1))in Typed.
 eapply(immediate_selected_mux _ _ _ _ _ _ _ (drop 20(take 21 instruction)) other false);[rewrite size_drop size_take Size;reflexivity|apply Branch;vm_compute;tauto|exact V2361|exact Other|exact Typed]. }
 assert(V2363:VM.find 2363(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 152 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2363 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 destruct(reference_immediate_typed_history 142 _ history limit time ltac:(lia) Steps TypedSource Lower ltac:(lia))as[other[Other Typed]].
 change(VM.find 2351(history time)=Some other)in Other. change(type_of_val other=Gtyp(Fuint 1))in Typed.
 eapply(immediate_selected_mux _ _ _ _ _ _ _ (drop 20(take 21 instruction)) other false);[rewrite size_drop size_take Size;reflexivity|apply Branch;vm_compute;tauto|exact V2362|exact Other|exact Typed]. }
 assert(V2364:VM.find 2364(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 153 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2364 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 destruct(reference_immediate_typed_history 138 _ history limit time ltac:(lia) Steps TypedSource Lower ltac:(lia))as[other[Other Typed]].
 change(VM.find 2347(history time)=Some other)in Other. change(type_of_val other=Gtyp(Fuint 1))in Typed.
 eapply(immediate_selected_mux _ _ _ _ _ _ _ (drop 20(take 21 instruction)) other false);[rewrite size_drop size_take Size;reflexivity|apply Branch;vm_compute;tauto|exact V2363|exact Other|exact Typed]. }
 assert(V2365:VM.find 2365(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 154 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2365 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 destruct(reference_immediate_typed_history 134 _ history limit time ltac:(lia) Steps TypedSource Lower ltac:(lia))as[other[Other Typed]].
 change(VM.find 2343(history time)=Some other)in Other. change(type_of_val other=Gtyp(Fuint 1))in Typed.
 eapply(immediate_selected_mux _ _ _ _ _ _ _ (drop 20(take 21 instruction)) other false);[rewrite size_drop size_take Size;reflexivity|apply Branch;vm_compute;tauto|exact V2364|exact Other|exact Typed]. }
 assert(V2366:VM.find 2366(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 155 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2366 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 destruct(reference_immediate_typed_history 130 _ history limit time ltac:(lia) Steps TypedSource Lower ltac:(lia))as[other[Other Typed]].
 change(VM.find 2339(history time)=Some other)in Other. change(type_of_val other=Gtyp(Fuint 1))in Typed.
 eapply(immediate_selected_mux _ _ _ _ _ _ _ (drop 20(take 21 instruction)) other false);[rewrite size_drop size_take Size;reflexivity|apply Branch;vm_compute;tauto|exact V2365|exact Other|exact Typed]. }
 assert(V2367:VM.find 2367(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 156 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2367 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 destruct(reference_immediate_typed_history 126 _ history limit time ltac:(lia) Steps TypedSource Lower ltac:(lia))as[other[Other Typed]].
 change(VM.find 2335(history time)=Some other)in Other. change(type_of_val other=Gtyp(Fuint 1))in Typed.
 eapply(immediate_selected_mux _ _ _ _ _ _ _ (drop 20(take 21 instruction)) other false);[rewrite size_drop size_take Size;reflexivity|apply Branch;vm_compute;tauto|exact V2366|exact Other|exact Typed]. }
 assert(V2368:VM.find 2368(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 157 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2368 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 cbn[reference_control_expr_2368 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite V2367.
 change(adapt_hvalue_as_type(Gval(Fuint 1)(drop 20(take 21 instruction)))(Gtyp(Fuint 1))=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))). apply dut_decode_adapt. rewrite size_drop size_take Size;reflexivity. }
 assert(V2369:VM.find 2369(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 { eapply(reference_immediate_value_history 158 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2369 (history time)(history time)=Some(Gval(Fuint 1)(drop 20(take 21 instruction)))).
 exact V2368. }
 assert(V2451:VM.find 2451(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 { eapply(reference_immediate_value_history 226 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2451 (history time)(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2451 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Jal;cbn;rewrite V2450.
 change(adapt_hvalue_as_type(Gval(Fuint 1)(drop 31(take 32 instruction)))(Gtyp(Fuint 1))=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))). apply dut_decode_adapt. rewrite size_drop size_take Size;reflexivity. }
 assert(V2452:VM.find 2452(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 { eapply(reference_immediate_value_history 227 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2452 (history time)(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 cbn[reference_control_expr_2452 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite V2451.
 change(adapt_hvalue_as_type(Gval(Fuint 1)(drop 31(take 32 instruction)))(Gtyp(Fuint 1))=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))). apply dut_decode_adapt. rewrite size_drop size_take Size;reflexivity. }
 assert(V2453:VM.find 2453(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 { eapply(reference_immediate_value_history 228 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2453 (history time)(history time)=Some(Gval(Fuint 1)(drop 31(take 32 instruction)))).
 exact V2452. }
 assert(V2456:VM.find 2456(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))).
 { eapply(reference_immediate_value_history 231 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2456 (history time)(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))).
 cbn[reference_control_expr_2456 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Jal;cbn;rewrite V2455.
 change(adapt_hvalue_as_type(Gval(Fuint 8)(drop 12(take 20 instruction)))(Gtyp(Fuint 8))=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))). apply dut_decode_adapt. rewrite size_drop size_take Size;reflexivity. }
 assert(V2457:VM.find 2457(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))).
 { eapply(reference_immediate_value_history 232 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2457 (history time)(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))).
 cbn[reference_control_expr_2457 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite V2456.
 change(adapt_hvalue_as_type(Gval(Fuint 8)(drop 12(take 20 instruction)))(Gtyp(Fuint 8))=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))). apply dut_decode_adapt. rewrite size_drop size_take Size;reflexivity. }
 assert(V2458:VM.find 2458(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))).
 { eapply(reference_immediate_value_history 233 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2458 (history time)(history time)=Some(Gval(Fuint 8)(drop 12(take 20 instruction)))).
 exact V2457. }
 assert(V2462:VM.find 2462(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))).
 { eapply(reference_immediate_value_history 237 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2462 (history time)(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))).
 cbn[reference_control_expr_2462 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Jal;cbn;rewrite V2461.
 change(adapt_hvalue_as_type(Gval(Fuint 10)(drop 21(take 31 instruction)))(Gtyp(Fuint 10))=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))). apply dut_decode_adapt. rewrite size_drop size_take Size;reflexivity. }
 assert(V2463:VM.find 2463(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))).
 { eapply(reference_immediate_value_history 238 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2463 (history time)(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))).
 cbn[reference_control_expr_2463 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite V2462.
 change(adapt_hvalue_as_type(Gval(Fuint 10)(drop 21(take 31 instruction)))(Gtyp(Fuint 10))=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))). apply dut_decode_adapt. rewrite size_drop size_take Size;reflexivity. }
 assert(V2464:VM.find 2464(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))).
 { eapply(reference_immediate_value_history 239 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_2464 (history time)(history time)=Some(Gval(Fuint 10)(drop 21(take 31 instruction)))).
 exact V2463. }
 repeat split;assumption.
Qed.
(* JAL assembly. *)
Require Import ReferenceLoadSemantics ReferenceControlNodeCongruence1.
Theorem reference_jal_assembly_history inputs path history limit reset time sign middle bit low :
 size sign=1%nat ->size middle=8%nat ->size bit=1%nat ->size low=10%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 2453(history time)=Some(Gval(Fuint 1)sign) ->
 VM.find 2458(history time)=Some(Gval(Fuint 8)middle) ->
 VM.find 2369(history time)=Some(Gval(Fuint 1)bit) ->
 VM.find 2464(history time)=Some(Gval(Fuint 10)low) ->
 VM.find 2470(history time)=Some(Gval(Fuint 32)(sext_to 32(([::false]++low)++(bit++(middle++sign))))).
Proof.
 intros SignSize MiddleSize BitSize LowSize Resets Steps Lower Upper Sign Middle Bit Low.
 set(payload:=([::false]++low)++(bit++(middle++sign))).
 assert(Size:size payload=21%nat)by(unfold payload;repeat rewrite size_cat;rewrite SignSize MiddleSize BitSize LowSize;reflexivity).
 assert(V2459:VM.find 2459(history time)=Some(Gval(Fuint 9)(middle++sign))).
 { eapply(reference_immediate_value_history 234 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2459(history time)(history time)=Some(Gval(Fuint 9)(middle++sign))).
 cbn[reference_control_expr_2459 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Sign Middle. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity. }
 assert(V2460:VM.find 2460(history time)=Some(Gval(Fuint 10)(bit++(middle++sign)))).
 { eapply(reference_immediate_value_history 235 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2460(history time)(history time)=Some(Gval(Fuint 10)(bit++(middle++sign)))).
 cbn[reference_control_expr_2460 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2459 Bit. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity. }
 assert(V2465:VM.find 2465(history time)=Some(Gval(Fuint 11)([::false]++low))).
 { eapply(reference_immediate_value_history 240 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2465(history time)(history time)=Some(Gval(Fuint 11)([::false]++low))).
 cbn[reference_control_expr_2465 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Low. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity. }
 assert(V2466:VM.find 2466(history time)=Some(Gval(Fuint 21)(payload))).
 { eapply(reference_immediate_value_history 241 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2466(history time)(history time)=Some(Gval(Fuint 21)(payload))).
 cbn[reference_control_expr_2466 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2460 V2465. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity. }
 assert(V2467:VM.find 2467(history time)=Some(Gval(Fuint 1)([::msb payload]))).
 { rewrite(reference_control_stable_2467_history inputs path history limit reset Resets Steps time(S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2467 reference_control_expr_2467);[exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2467| |apply Steps;lia].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2467(history time)(history time)=Some(Gval(Fuint 1)([::msb payload]))).
 cbn[reference_control_expr_2467 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2466. change(Some(Gval(Fuint 1)(drop(21-1)%nat(take 21 payload)))=Some(Gval(Fuint 1)[::msb payload])). rewrite(reference_load_sign_bit 21 payload Size(eq_refl true));reflexivity. }
 assert(V2468:VM.find 2468(history time)=Some(Gval(Fuint 1)([::msb payload]))).
 { rewrite(reference_control_stable_2468_history inputs path history limit reset Resets Steps time(S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2468 reference_control_expr_2468);[exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2468| |apply Steps;lia].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2468(history time)(history time)=Some(Gval(Fuint 1)([::msb payload]))).
 cbn[reference_control_expr_2468 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2467;destruct(msb payload);reflexivity. }
 assert(V2469:VM.find 2469(history time)=Some(Gval(Fuint 11)(nseq 11(msb payload)))).
 { eapply(reference_immediate_value_history 242 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2469(history time)(history time)=Some(Gval(Fuint 11)(nseq 11(msb payload)))).
 cbn[reference_control_expr_2469 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2468;destruct(msb payload);reflexivity. }
 assert(V2470:VM.find 2470(history time)=Some(Gval(Fuint 32)(sext_to 32 payload))).
 { eapply(reference_immediate_value_history 243 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2470(history time)(history time)=Some(Gval(Fuint 32)(sext_to 32 payload))).
 cbn[reference_control_expr_2470 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V2469 V2466. unfold eval_binop;try rewrite immediate_cat_no_absorbing. change(Some(Gval(Fuint 32)(payload++nseq 11(msb payload)))=Some(Gval(Fuint 32)(sext_to 32 payload))). unfold sext_to,sext;rewrite Size;reflexivity. }
 exact V2470.
Qed.
(* Final immediate composition. *)
Require Import DUTImmediateModes.
Lemma dut_j_immediate_canonical instruction : size instruction=32%nat ->
 dut_j_immediate instruction=sext_to 32(([::false]++drop 21(take 31 instruction))++(drop 20(take 21 instruction)++(drop 12(take 20 instruction)++drop 31(take 32 instruction)))).
Proof.
 intro Size. do 32(let b:=fresh "b" in destruct instruction as[|b instruction];[discriminate Size|];cbn[size]in Size).
 destruct instruction;[reflexivity|discriminate Size].
Qed.
Definition jal_final_guard n : VarOrder.T :=nth 0 [::2010;2004;1998;1992;1986;1980;1974;1970;1966;1962;1958;1886;1951;1946;1941;1937;1933;1929] n.
Definition jal_final_yes n : VarOrder.T :=nth 0 [::2449;2445;2437;2429;2421;2413;2405;2317;2313;2309;2305;2301;2297;2292;2287;2260;2256;2252] n.
Definition jal_final_index n :=nth 0%nat [::284%nat;285%nat;286%nat;287%nat;288%nat;289%nat;290%nat;291%nat;292%nat;293%nat;294%nat;295%nat;296%nat;297%nat;298%nat;299%nat;300%nat;301%nat] n.
Definition jal_final_yes_index n :=nth 0%nat [::224%nat;222%nat;216%nat;210%nat;204%nat;198%nat;192%nat;108%nat;106%nat;104%nat;102%nat;100%nat;98%nat;95%nat;92%nat;67%nat;65%nat;63%nat] n.
Definition jal_final_node n : VarOrder.T :=2533+N.of_nat n.
Lemma jal_final_metadata n : (n<18)%coq_nat ->
 (jal_final_index n<304)%coq_nat /\(jal_final_yes_index n<304)%coq_nat /\
 reference_immediate_node(jal_final_index n)=jal_final_node n /\
 reference_immediate_node(jal_final_yes_index n)=jal_final_yes n /\
 reference_immediate_width(jal_final_yes_index n)=32%nat /\
 reference_immediate_expression(jal_final_index n)=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T(jal_final_guard n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(jal_final_yes n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(match n with O=>2532|S before=>jal_final_node before end))).
Proof. do 18(destruct n as[|n];[vm_compute;intuition lia|]);lia. Qed.
Theorem reference_jal_final_history inputs path history limit reset time word :
 size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 2357(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<18)%coq_nat ->VM.find(jal_final_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2470(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Jal Guards Selected.
 assert(Start:VM.find 2532(history time)=Some(Gval(Fuint 32)word)).
 { eapply(reference_immediate_value_history 283 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2532(history time)(history time)=Some(Gval(Fuint 32)word)).
 destruct(reference_immediate_typed_history 282 _ history limit time ltac:(lia) Steps Source Lower ltac:(lia))as[other[Other Typed]].
 change(VM.find 2531(history time)=Some other)in Other. change(type_of_val other=Gtyp(Fuint 32))in Typed.
 eapply(immediate_selected_mux _ _ _ _ _ _ _ word other true);[exact Size|exact Jal|exact Selected|exact Other|exact Typed]. }
 assert(Final:VM.find 2550(history time)=Some(Gval(Fuint 32)word)).
 { change(VM.find(jal_final_node 17)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_fallback (formal_invalid_policy inputs path)(history time)(history time)18 32 word 2532 jal_final_node jal_final_guard jal_final_yes);[exact Size|intros;reflexivity| |exact Guards| |exact Start|lia].
 - intros n Bound value Eval. destruct(jal_final_metadata n Bound)as[IB[YB[Node[Yes[Width Expr]]]]]. rewrite <-Node.
   eapply(reference_immediate_value_history (jal_final_index n) inputs path history limit reset time);[exact IB|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;rewrite Expr;apply Eval.
 - intros n Bound. destruct(jal_final_metadata n Bound)as[IB[YB[Node[Yes[Width Expr]]]]].
   pose proof(reference_immediate_typed_history (jal_final_yes_index n) _ history limit time YB Steps Source Lower ltac:(lia))as Typed. rewrite Yes Width in Typed;exact Typed. }
 assert(EnabledValue:VM.find 2551(history time)=Some(Gval(Fuint 32)word)).
 { eapply(load_imm_aux_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Final.
 change(adapt_hvalue_as_type(Gval(Fuint 32)word)(Gtyp(Fuint 32))=Some(Gval(Fuint 32)word)). apply dut_decode_adapt;exact Size. }
 eapply(load_imm_aux_value 28 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact EnabledValue.
Qed.
(* JAL complete history. *)
Theorem reference_jal_immediate_history inputs path history limit reset time instruction :
 size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 2357(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<18)%coq_nat ->VM.find(jal_final_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)(dut_j_immediate instruction)).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Jal Guards.
 assert(Branch:forall guard,List.In guard[::2004;1998;1992;1986;1980;1974] ->VM.find guard(history time)=Some(Gval(Fuint 1)[::false])).
 { intros guard Member. cbn in Member. destruct Member as[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
 [exact(Guards 1%nat ltac:(lia))|exact(Guards 2%nat ltac:(lia))|exact(Guards 3%nat ltac:(lia))|exact(Guards 4%nat ltac:(lia))|exact(Guards 5%nat ltac:(lia))|exact(Guards 6%nat ltac:(lia))]. }
 destruct(reference_jal_selected_fields_history inputs path history limit reset time instruction Size Resets Steps Source Lower Upper Enabled Jal Branch)as[Bit[Sign[Middle Low]]].
 pose proof(reference_jal_assembly_history inputs path history limit reset time (drop 31(take 32 instruction))(drop 12(take 20 instruction))(drop 20(take 21 instruction))(drop 21(take 31 instruction))
 ltac:(rewrite size_drop size_take Size;reflexivity) ltac:(rewrite size_drop size_take Size;reflexivity)
 ltac:(rewrite size_drop size_take Size;reflexivity) ltac:(rewrite size_drop size_take Size;reflexivity)
 Resets Steps Lower Upper Sign Middle Bit Low)as Value.
 rewrite <-(dut_j_immediate_canonical instruction Size)in Value.
 eapply(reference_jal_final_history inputs path history limit reset time);[exact(dut_imm_result_size 3 instruction ltac:(lia) Size)|exact Resets|exact Steps| |exact Lower|exact Upper|exact Enabled|exact Jal|exact Guards|exact Value].
 intros t L U;exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity].
Qed.
Require Import ReferenceIllegalObserved JointUpdateBoundaryHistory RFScalarControl ReferenceInstructionDecode FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete LoadPipelineClassification LoadTypeCorrespondence ReferenceMemoryRequest MemoryRequestObservedSemantics.
Lemma jal_reference_enabled_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)127=111 ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset Instruction Jal.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Late Nop]]. destruct bit.
 - specialize(Nop(Logic.eq_refl _)). rewrite Nop in Instruction. inversion Instruction;subst instruction. vm_compute in Jal;discriminate.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late).
Qed.
Lemma jal_final_guard_decoder n : (n<18)%coq_nat ->jal_final_guard n=reference_instruction_guard(Nat.add 22 n).
Proof. do 18(destruct n as[|n];[reflexivity|]);lia. Qed.
Theorem reference_jal_immediate_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)127=111 ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(dut_j_immediate instruction)).
Proof.
 intros Observe Legal Reset Instruction Jal.
 pose proof(jal_reference_enabled_observed memory inputs k observed instruction Observe Legal Reset Instruction Jal)as Enabled.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Inst:forall t,(t<=9259)%coq_nat ->VM.find 7750(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite <-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Instruction. }
 assert(Enable:forall t,(195<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::true])).
 { intros t Lower Upper. rewrite(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat ltac:(lia)ltac:(lia)Upper ltac:(lia)) Last;exact Enabled. }
 assert(Source:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)).
 { intros t Lower Upper. exact(memory_reference_instruction_history _ history 9259 195 instruction true Size Steps Inst Enable t Lower Upper). }
 assert(Decode:forall row,(row<48)%coq_nat ->VM.find(reference_instruction_guard row)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb row 21])).
 { intros row Row.
 pose proof(reference_instruction_decode_history (formal_invalid_policy(generated_observation_input inputs k)nil)(fun t=>history(Nat.add 9248 t))2 instruction row Row
 ltac:(intros i I;destruct i as[|[|i]];[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia])
 ltac:(intros i I;destruct i as[|[|[|i]]];[apply Source;vm_compute;lia|apply Source;vm_compute;lia|apply Source;vm_compute;lia|lia])
 2 ltac:(lia)ltac:(lia))as Value.
 change(VM.find(reference_instruction_guard row)(history 9250%nat)=Some(Gval(Fuint 1)[::N.eqb(reference_instruction_code row)(N.land(to_N instruction)(reference_instruction_mask row))]))in Value.
 rewrite(rf_reference_decode_onehot instruction 21 row ltac:(lia) Row Jal)in Value;exact Value. }
 assert(Guards:forall n,(n<18)%coq_nat ->VM.find(jal_final_guard n)(history 9250%nat)=Some(Gval(Fuint 1)[::false])).
 { intros n Bound. rewrite(jal_final_guard_decoder n Bound). rewrite(Decode(Nat.add 22 n)ltac:(lia)).
 rewrite(proj2(Nat.eqb_neq(Nat.add 22 n)21)ltac:(lia));reflexivity. }
 pose proof(reference_jal_immediate_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)
 (Enable 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))(Decode 21%nat ltac:(lia))Guards)as Value.
 rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)) Last in Value;exact Value.
Qed.
