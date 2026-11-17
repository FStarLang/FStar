module TcDiamond

(* Typeclass hierarchies with many diamonds, where the search without
   caching takes exponential time (see issue #2612). Each test below needs
   about 2^40 steps without the cache, far above the resolution budget, and
   only O(40) with it. Exceeding the budget (warning 400) is an error here,
   so a cut search does not go unnoticed. *)

#set-options "--warn_error @400"

open FStar.Tactics.Typeclasses

(* 1. Superclass diamonds, as in an algebraic hierarchy: each [d(k+1)]
   extends both [l k] and [r k], which both extend [d k]. *)

class d0 (a:Type) = { op0 : a -> a -> a }
class l0 (a:Type) = { [@@@tcinstance] l0_super : d0 a }
class r0 (a:Type) = { [@@@tcinstance] r0_super : d0 a }
class d1 (a:Type) = { [@@@tcinstance] d1_l : l0 a; [@@@tcinstance] d1_r : r0 a }
class l1 (a:Type) = { [@@@tcinstance] l1_super : d1 a }
class r1 (a:Type) = { [@@@tcinstance] r1_super : d1 a }
class d2 (a:Type) = { [@@@tcinstance] d2_l : l1 a; [@@@tcinstance] d2_r : r1 a }
class l2 (a:Type) = { [@@@tcinstance] l2_super : d2 a }
class r2 (a:Type) = { [@@@tcinstance] r2_super : d2 a }
class d3 (a:Type) = { [@@@tcinstance] d3_l : l2 a; [@@@tcinstance] d3_r : r2 a }
class l3 (a:Type) = { [@@@tcinstance] l3_super : d3 a }
class r3 (a:Type) = { [@@@tcinstance] r3_super : d3 a }
class d4 (a:Type) = { [@@@tcinstance] d4_l : l3 a; [@@@tcinstance] d4_r : r3 a }
class l4 (a:Type) = { [@@@tcinstance] l4_super : d4 a }
class r4 (a:Type) = { [@@@tcinstance] r4_super : d4 a }
class d5 (a:Type) = { [@@@tcinstance] d5_l : l4 a; [@@@tcinstance] d5_r : r4 a }
class l5 (a:Type) = { [@@@tcinstance] l5_super : d5 a }
class r5 (a:Type) = { [@@@tcinstance] r5_super : d5 a }
class d6 (a:Type) = { [@@@tcinstance] d6_l : l5 a; [@@@tcinstance] d6_r : r5 a }
class l6 (a:Type) = { [@@@tcinstance] l6_super : d6 a }
class r6 (a:Type) = { [@@@tcinstance] r6_super : d6 a }
class d7 (a:Type) = { [@@@tcinstance] d7_l : l6 a; [@@@tcinstance] d7_r : r6 a }
class l7 (a:Type) = { [@@@tcinstance] l7_super : d7 a }
class r7 (a:Type) = { [@@@tcinstance] r7_super : d7 a }
class d8 (a:Type) = { [@@@tcinstance] d8_l : l7 a; [@@@tcinstance] d8_r : r7 a }
class l8 (a:Type) = { [@@@tcinstance] l8_super : d8 a }
class r8 (a:Type) = { [@@@tcinstance] r8_super : d8 a }
class d9 (a:Type) = { [@@@tcinstance] d9_l : l8 a; [@@@tcinstance] d9_r : r8 a }
class l9 (a:Type) = { [@@@tcinstance] l9_super : d9 a }
class r9 (a:Type) = { [@@@tcinstance] r9_super : d9 a }
class d10 (a:Type) = { [@@@tcinstance] d10_l : l9 a; [@@@tcinstance] d10_r : r9 a }
class l10 (a:Type) = { [@@@tcinstance] l10_super : d10 a }
class r10 (a:Type) = { [@@@tcinstance] r10_super : d10 a }
class d11 (a:Type) = { [@@@tcinstance] d11_l : l10 a; [@@@tcinstance] d11_r : r10 a }
class l11 (a:Type) = { [@@@tcinstance] l11_super : d11 a }
class r11 (a:Type) = { [@@@tcinstance] r11_super : d11 a }
class d12 (a:Type) = { [@@@tcinstance] d12_l : l11 a; [@@@tcinstance] d12_r : r11 a }
class l12 (a:Type) = { [@@@tcinstance] l12_super : d12 a }
class r12 (a:Type) = { [@@@tcinstance] r12_super : d12 a }
class d13 (a:Type) = { [@@@tcinstance] d13_l : l12 a; [@@@tcinstance] d13_r : r12 a }
class l13 (a:Type) = { [@@@tcinstance] l13_super : d13 a }
class r13 (a:Type) = { [@@@tcinstance] r13_super : d13 a }
class d14 (a:Type) = { [@@@tcinstance] d14_l : l13 a; [@@@tcinstance] d14_r : r13 a }
class l14 (a:Type) = { [@@@tcinstance] l14_super : d14 a }
class r14 (a:Type) = { [@@@tcinstance] r14_super : d14 a }
class d15 (a:Type) = { [@@@tcinstance] d15_l : l14 a; [@@@tcinstance] d15_r : r14 a }
class l15 (a:Type) = { [@@@tcinstance] l15_super : d15 a }
class r15 (a:Type) = { [@@@tcinstance] r15_super : d15 a }
class d16 (a:Type) = { [@@@tcinstance] d16_l : l15 a; [@@@tcinstance] d16_r : r15 a }
class l16 (a:Type) = { [@@@tcinstance] l16_super : d16 a }
class r16 (a:Type) = { [@@@tcinstance] r16_super : d16 a }
class d17 (a:Type) = { [@@@tcinstance] d17_l : l16 a; [@@@tcinstance] d17_r : r16 a }
class l17 (a:Type) = { [@@@tcinstance] l17_super : d17 a }
class r17 (a:Type) = { [@@@tcinstance] r17_super : d17 a }
class d18 (a:Type) = { [@@@tcinstance] d18_l : l17 a; [@@@tcinstance] d18_r : r17 a }
class l18 (a:Type) = { [@@@tcinstance] l18_super : d18 a }
class r18 (a:Type) = { [@@@tcinstance] r18_super : d18 a }
class d19 (a:Type) = { [@@@tcinstance] d19_l : l18 a; [@@@tcinstance] d19_r : r18 a }
class l19 (a:Type) = { [@@@tcinstance] l19_super : d19 a }
class r19 (a:Type) = { [@@@tcinstance] r19_super : d19 a }
class d20 (a:Type) = { [@@@tcinstance] d20_l : l19 a; [@@@tcinstance] d20_r : r19 a }
class l20 (a:Type) = { [@@@tcinstance] l20_super : d20 a }
class r20 (a:Type) = { [@@@tcinstance] r20_super : d20 a }
class d21 (a:Type) = { [@@@tcinstance] d21_l : l20 a; [@@@tcinstance] d21_r : r20 a }
class l21 (a:Type) = { [@@@tcinstance] l21_super : d21 a }
class r21 (a:Type) = { [@@@tcinstance] r21_super : d21 a }
class d22 (a:Type) = { [@@@tcinstance] d22_l : l21 a; [@@@tcinstance] d22_r : r21 a }
class l22 (a:Type) = { [@@@tcinstance] l22_super : d22 a }
class r22 (a:Type) = { [@@@tcinstance] r22_super : d22 a }
class d23 (a:Type) = { [@@@tcinstance] d23_l : l22 a; [@@@tcinstance] d23_r : r22 a }
class l23 (a:Type) = { [@@@tcinstance] l23_super : d23 a }
class r23 (a:Type) = { [@@@tcinstance] r23_super : d23 a }
class d24 (a:Type) = { [@@@tcinstance] d24_l : l23 a; [@@@tcinstance] d24_r : r23 a }
class l24 (a:Type) = { [@@@tcinstance] l24_super : d24 a }
class r24 (a:Type) = { [@@@tcinstance] r24_super : d24 a }
class d25 (a:Type) = { [@@@tcinstance] d25_l : l24 a; [@@@tcinstance] d25_r : r24 a }
class l25 (a:Type) = { [@@@tcinstance] l25_super : d25 a }
class r25 (a:Type) = { [@@@tcinstance] r25_super : d25 a }
class d26 (a:Type) = { [@@@tcinstance] d26_l : l25 a; [@@@tcinstance] d26_r : r25 a }
class l26 (a:Type) = { [@@@tcinstance] l26_super : d26 a }
class r26 (a:Type) = { [@@@tcinstance] r26_super : d26 a }
class d27 (a:Type) = { [@@@tcinstance] d27_l : l26 a; [@@@tcinstance] d27_r : r26 a }
class l27 (a:Type) = { [@@@tcinstance] l27_super : d27 a }
class r27 (a:Type) = { [@@@tcinstance] r27_super : d27 a }
class d28 (a:Type) = { [@@@tcinstance] d28_l : l27 a; [@@@tcinstance] d28_r : r27 a }
class l28 (a:Type) = { [@@@tcinstance] l28_super : d28 a }
class r28 (a:Type) = { [@@@tcinstance] r28_super : d28 a }
class d29 (a:Type) = { [@@@tcinstance] d29_l : l28 a; [@@@tcinstance] d29_r : r28 a }
class l29 (a:Type) = { [@@@tcinstance] l29_super : d29 a }
class r29 (a:Type) = { [@@@tcinstance] r29_super : d29 a }
class d30 (a:Type) = { [@@@tcinstance] d30_l : l29 a; [@@@tcinstance] d30_r : r29 a }
class l30 (a:Type) = { [@@@tcinstance] l30_super : d30 a }
class r30 (a:Type) = { [@@@tcinstance] r30_super : d30 a }
class d31 (a:Type) = { [@@@tcinstance] d31_l : l30 a; [@@@tcinstance] d31_r : r30 a }
class l31 (a:Type) = { [@@@tcinstance] l31_super : d31 a }
class r31 (a:Type) = { [@@@tcinstance] r31_super : d31 a }
class d32 (a:Type) = { [@@@tcinstance] d32_l : l31 a; [@@@tcinstance] d32_r : r31 a }
class l32 (a:Type) = { [@@@tcinstance] l32_super : d32 a }
class r32 (a:Type) = { [@@@tcinstance] r32_super : d32 a }
class d33 (a:Type) = { [@@@tcinstance] d33_l : l32 a; [@@@tcinstance] d33_r : r32 a }
class l33 (a:Type) = { [@@@tcinstance] l33_super : d33 a }
class r33 (a:Type) = { [@@@tcinstance] r33_super : d33 a }
class d34 (a:Type) = { [@@@tcinstance] d34_l : l33 a; [@@@tcinstance] d34_r : r33 a }
class l34 (a:Type) = { [@@@tcinstance] l34_super : d34 a }
class r34 (a:Type) = { [@@@tcinstance] r34_super : d34 a }
class d35 (a:Type) = { [@@@tcinstance] d35_l : l34 a; [@@@tcinstance] d35_r : r34 a }
class l35 (a:Type) = { [@@@tcinstance] l35_super : d35 a }
class r35 (a:Type) = { [@@@tcinstance] r35_super : d35 a }
class d36 (a:Type) = { [@@@tcinstance] d36_l : l35 a; [@@@tcinstance] d36_r : r35 a }
class l36 (a:Type) = { [@@@tcinstance] l36_super : d36 a }
class r36 (a:Type) = { [@@@tcinstance] r36_super : d36 a }
class d37 (a:Type) = { [@@@tcinstance] d37_l : l36 a; [@@@tcinstance] d37_r : r36 a }
class l37 (a:Type) = { [@@@tcinstance] l37_super : d37 a }
class r37 (a:Type) = { [@@@tcinstance] r37_super : d37 a }
class d38 (a:Type) = { [@@@tcinstance] d38_l : l37 a; [@@@tcinstance] d38_r : r37 a }
class l38 (a:Type) = { [@@@tcinstance] l38_super : d38 a }
class r38 (a:Type) = { [@@@tcinstance] r38_super : d38 a }
class d39 (a:Type) = { [@@@tcinstance] d39_l : l38 a; [@@@tcinstance] d39_r : r38 a }
class l39 (a:Type) = { [@@@tcinstance] l39_super : d39 a }
class r39 (a:Type) = { [@@@tcinstance] r39_super : d39 a }
class d40 (a:Type) = { [@@@tcinstance] d40_l : l39 a; [@@@tcinstance] d40_r : r39 a }

(* Going down from the top of the hierarchy. *)
let down (#a:Type) {| d40 a |} (x y : a) : a = op0 x y

(* A failing search explores every path from [d0 b] up to [d40 b], and
   finds that the local instance is [d40 a]. With the cache, each [dk b]
   fails once. *)
[@@expect_failure [228]]
let down_fail (#a #b:Type) {| d40 a |} (x y : b) : b = op0 x y

(* 2. Backtracking over global instances: every level has an instance that
   fails after solving the level below, and one that succeeds. The result
   for each level is reused after the failure. *)
class base (a:Type) = { base_val : a }
class bad (a:Type) = { bad_val : a }
class c0 (a:Type) = { c0_val : a }
instance c0_base (a:Type) {| base a |} : c0 a = { c0_val = base_val }

class c1 (a:Type) = { c1_val : a }
instance c1_good (a:Type) {| c0 a |} : c1 a = { c1_val = c0_val }
instance c1_bad (a:Type) {| c0 a |} {| bad a |} : c1 a = { c1_val = bad_val }
instance c1_bad' (a:Type) {| c0 a |} {| bad a |} : c1 a = { c1_val = bad_val }
class c2 (a:Type) = { c2_val : a }
instance c2_good (a:Type) {| c1 a |} : c2 a = { c2_val = c1_val }
instance c2_bad (a:Type) {| c1 a |} {| bad a |} : c2 a = { c2_val = bad_val }
instance c2_bad' (a:Type) {| c1 a |} {| bad a |} : c2 a = { c2_val = bad_val }
class c3 (a:Type) = { c3_val : a }
instance c3_good (a:Type) {| c2 a |} : c3 a = { c3_val = c2_val }
instance c3_bad (a:Type) {| c2 a |} {| bad a |} : c3 a = { c3_val = bad_val }
instance c3_bad' (a:Type) {| c2 a |} {| bad a |} : c3 a = { c3_val = bad_val }
class c4 (a:Type) = { c4_val : a }
instance c4_good (a:Type) {| c3 a |} : c4 a = { c4_val = c3_val }
instance c4_bad (a:Type) {| c3 a |} {| bad a |} : c4 a = { c4_val = bad_val }
instance c4_bad' (a:Type) {| c3 a |} {| bad a |} : c4 a = { c4_val = bad_val }
class c5 (a:Type) = { c5_val : a }
instance c5_good (a:Type) {| c4 a |} : c5 a = { c5_val = c4_val }
instance c5_bad (a:Type) {| c4 a |} {| bad a |} : c5 a = { c5_val = bad_val }
instance c5_bad' (a:Type) {| c4 a |} {| bad a |} : c5 a = { c5_val = bad_val }
class c6 (a:Type) = { c6_val : a }
instance c6_good (a:Type) {| c5 a |} : c6 a = { c6_val = c5_val }
instance c6_bad (a:Type) {| c5 a |} {| bad a |} : c6 a = { c6_val = bad_val }
instance c6_bad' (a:Type) {| c5 a |} {| bad a |} : c6 a = { c6_val = bad_val }
class c7 (a:Type) = { c7_val : a }
instance c7_good (a:Type) {| c6 a |} : c7 a = { c7_val = c6_val }
instance c7_bad (a:Type) {| c6 a |} {| bad a |} : c7 a = { c7_val = bad_val }
instance c7_bad' (a:Type) {| c6 a |} {| bad a |} : c7 a = { c7_val = bad_val }
class c8 (a:Type) = { c8_val : a }
instance c8_good (a:Type) {| c7 a |} : c8 a = { c8_val = c7_val }
instance c8_bad (a:Type) {| c7 a |} {| bad a |} : c8 a = { c8_val = bad_val }
instance c8_bad' (a:Type) {| c7 a |} {| bad a |} : c8 a = { c8_val = bad_val }
class c9 (a:Type) = { c9_val : a }
instance c9_good (a:Type) {| c8 a |} : c9 a = { c9_val = c8_val }
instance c9_bad (a:Type) {| c8 a |} {| bad a |} : c9 a = { c9_val = bad_val }
instance c9_bad' (a:Type) {| c8 a |} {| bad a |} : c9 a = { c9_val = bad_val }
class c10 (a:Type) = { c10_val : a }
instance c10_good (a:Type) {| c9 a |} : c10 a = { c10_val = c9_val }
instance c10_bad (a:Type) {| c9 a |} {| bad a |} : c10 a = { c10_val = bad_val }
instance c10_bad' (a:Type) {| c9 a |} {| bad a |} : c10 a = { c10_val = bad_val }
class c11 (a:Type) = { c11_val : a }
instance c11_good (a:Type) {| c10 a |} : c11 a = { c11_val = c10_val }
instance c11_bad (a:Type) {| c10 a |} {| bad a |} : c11 a = { c11_val = bad_val }
instance c11_bad' (a:Type) {| c10 a |} {| bad a |} : c11 a = { c11_val = bad_val }
class c12 (a:Type) = { c12_val : a }
instance c12_good (a:Type) {| c11 a |} : c12 a = { c12_val = c11_val }
instance c12_bad (a:Type) {| c11 a |} {| bad a |} : c12 a = { c12_val = bad_val }
instance c12_bad' (a:Type) {| c11 a |} {| bad a |} : c12 a = { c12_val = bad_val }
class c13 (a:Type) = { c13_val : a }
instance c13_good (a:Type) {| c12 a |} : c13 a = { c13_val = c12_val }
instance c13_bad (a:Type) {| c12 a |} {| bad a |} : c13 a = { c13_val = bad_val }
instance c13_bad' (a:Type) {| c12 a |} {| bad a |} : c13 a = { c13_val = bad_val }
class c14 (a:Type) = { c14_val : a }
instance c14_good (a:Type) {| c13 a |} : c14 a = { c14_val = c13_val }
instance c14_bad (a:Type) {| c13 a |} {| bad a |} : c14 a = { c14_val = bad_val }
instance c14_bad' (a:Type) {| c13 a |} {| bad a |} : c14 a = { c14_val = bad_val }
class c15 (a:Type) = { c15_val : a }
instance c15_good (a:Type) {| c14 a |} : c15 a = { c15_val = c14_val }
instance c15_bad (a:Type) {| c14 a |} {| bad a |} : c15 a = { c15_val = bad_val }
instance c15_bad' (a:Type) {| c14 a |} {| bad a |} : c15 a = { c15_val = bad_val }
class c16 (a:Type) = { c16_val : a }
instance c16_good (a:Type) {| c15 a |} : c16 a = { c16_val = c15_val }
instance c16_bad (a:Type) {| c15 a |} {| bad a |} : c16 a = { c16_val = bad_val }
instance c16_bad' (a:Type) {| c15 a |} {| bad a |} : c16 a = { c16_val = bad_val }
class c17 (a:Type) = { c17_val : a }
instance c17_good (a:Type) {| c16 a |} : c17 a = { c17_val = c16_val }
instance c17_bad (a:Type) {| c16 a |} {| bad a |} : c17 a = { c17_val = bad_val }
instance c17_bad' (a:Type) {| c16 a |} {| bad a |} : c17 a = { c17_val = bad_val }
class c18 (a:Type) = { c18_val : a }
instance c18_good (a:Type) {| c17 a |} : c18 a = { c18_val = c17_val }
instance c18_bad (a:Type) {| c17 a |} {| bad a |} : c18 a = { c18_val = bad_val }
instance c18_bad' (a:Type) {| c17 a |} {| bad a |} : c18 a = { c18_val = bad_val }
class c19 (a:Type) = { c19_val : a }
instance c19_good (a:Type) {| c18 a |} : c19 a = { c19_val = c18_val }
instance c19_bad (a:Type) {| c18 a |} {| bad a |} : c19 a = { c19_val = bad_val }
instance c19_bad' (a:Type) {| c18 a |} {| bad a |} : c19 a = { c19_val = bad_val }
class c20 (a:Type) = { c20_val : a }
instance c20_good (a:Type) {| c19 a |} : c20 a = { c20_val = c19_val }
instance c20_bad (a:Type) {| c19 a |} {| bad a |} : c20 a = { c20_val = bad_val }
instance c20_bad' (a:Type) {| c19 a |} {| bad a |} : c20 a = { c20_val = bad_val }
class c21 (a:Type) = { c21_val : a }
instance c21_good (a:Type) {| c20 a |} : c21 a = { c21_val = c20_val }
instance c21_bad (a:Type) {| c20 a |} {| bad a |} : c21 a = { c21_val = bad_val }
instance c21_bad' (a:Type) {| c20 a |} {| bad a |} : c21 a = { c21_val = bad_val }
class c22 (a:Type) = { c22_val : a }
instance c22_good (a:Type) {| c21 a |} : c22 a = { c22_val = c21_val }
instance c22_bad (a:Type) {| c21 a |} {| bad a |} : c22 a = { c22_val = bad_val }
instance c22_bad' (a:Type) {| c21 a |} {| bad a |} : c22 a = { c22_val = bad_val }
class c23 (a:Type) = { c23_val : a }
instance c23_good (a:Type) {| c22 a |} : c23 a = { c23_val = c22_val }
instance c23_bad (a:Type) {| c22 a |} {| bad a |} : c23 a = { c23_val = bad_val }
instance c23_bad' (a:Type) {| c22 a |} {| bad a |} : c23 a = { c23_val = bad_val }
class c24 (a:Type) = { c24_val : a }
instance c24_good (a:Type) {| c23 a |} : c24 a = { c24_val = c23_val }
instance c24_bad (a:Type) {| c23 a |} {| bad a |} : c24 a = { c24_val = bad_val }
instance c24_bad' (a:Type) {| c23 a |} {| bad a |} : c24 a = { c24_val = bad_val }
class c25 (a:Type) = { c25_val : a }
instance c25_good (a:Type) {| c24 a |} : c25 a = { c25_val = c24_val }
instance c25_bad (a:Type) {| c24 a |} {| bad a |} : c25 a = { c25_val = bad_val }
instance c25_bad' (a:Type) {| c24 a |} {| bad a |} : c25 a = { c25_val = bad_val }
class c26 (a:Type) = { c26_val : a }
instance c26_good (a:Type) {| c25 a |} : c26 a = { c26_val = c25_val }
instance c26_bad (a:Type) {| c25 a |} {| bad a |} : c26 a = { c26_val = bad_val }
instance c26_bad' (a:Type) {| c25 a |} {| bad a |} : c26 a = { c26_val = bad_val }
class c27 (a:Type) = { c27_val : a }
instance c27_good (a:Type) {| c26 a |} : c27 a = { c27_val = c26_val }
instance c27_bad (a:Type) {| c26 a |} {| bad a |} : c27 a = { c27_val = bad_val }
instance c27_bad' (a:Type) {| c26 a |} {| bad a |} : c27 a = { c27_val = bad_val }
class c28 (a:Type) = { c28_val : a }
instance c28_good (a:Type) {| c27 a |} : c28 a = { c28_val = c27_val }
instance c28_bad (a:Type) {| c27 a |} {| bad a |} : c28 a = { c28_val = bad_val }
instance c28_bad' (a:Type) {| c27 a |} {| bad a |} : c28 a = { c28_val = bad_val }
class c29 (a:Type) = { c29_val : a }
instance c29_good (a:Type) {| c28 a |} : c29 a = { c29_val = c28_val }
instance c29_bad (a:Type) {| c28 a |} {| bad a |} : c29 a = { c29_val = bad_val }
instance c29_bad' (a:Type) {| c28 a |} {| bad a |} : c29 a = { c29_val = bad_val }
class c30 (a:Type) = { c30_val : a }
instance c30_good (a:Type) {| c29 a |} : c30 a = { c30_val = c29_val }
instance c30_bad (a:Type) {| c29 a |} {| bad a |} : c30 a = { c30_val = bad_val }
instance c30_bad' (a:Type) {| c29 a |} {| bad a |} : c30 a = { c30_val = bad_val }
class c31 (a:Type) = { c31_val : a }
instance c31_good (a:Type) {| c30 a |} : c31 a = { c31_val = c30_val }
instance c31_bad (a:Type) {| c30 a |} {| bad a |} : c31 a = { c31_val = bad_val }
instance c31_bad' (a:Type) {| c30 a |} {| bad a |} : c31 a = { c31_val = bad_val }
class c32 (a:Type) = { c32_val : a }
instance c32_good (a:Type) {| c31 a |} : c32 a = { c32_val = c31_val }
instance c32_bad (a:Type) {| c31 a |} {| bad a |} : c32 a = { c32_val = bad_val }
instance c32_bad' (a:Type) {| c31 a |} {| bad a |} : c32 a = { c32_val = bad_val }
class c33 (a:Type) = { c33_val : a }
instance c33_good (a:Type) {| c32 a |} : c33 a = { c33_val = c32_val }
instance c33_bad (a:Type) {| c32 a |} {| bad a |} : c33 a = { c33_val = bad_val }
instance c33_bad' (a:Type) {| c32 a |} {| bad a |} : c33 a = { c33_val = bad_val }
class c34 (a:Type) = { c34_val : a }
instance c34_good (a:Type) {| c33 a |} : c34 a = { c34_val = c33_val }
instance c34_bad (a:Type) {| c33 a |} {| bad a |} : c34 a = { c34_val = bad_val }
instance c34_bad' (a:Type) {| c33 a |} {| bad a |} : c34 a = { c34_val = bad_val }
class c35 (a:Type) = { c35_val : a }
instance c35_good (a:Type) {| c34 a |} : c35 a = { c35_val = c34_val }
instance c35_bad (a:Type) {| c34 a |} {| bad a |} : c35 a = { c35_val = bad_val }
instance c35_bad' (a:Type) {| c34 a |} {| bad a |} : c35 a = { c35_val = bad_val }
class c36 (a:Type) = { c36_val : a }
instance c36_good (a:Type) {| c35 a |} : c36 a = { c36_val = c35_val }
instance c36_bad (a:Type) {| c35 a |} {| bad a |} : c36 a = { c36_val = bad_val }
instance c36_bad' (a:Type) {| c35 a |} {| bad a |} : c36 a = { c36_val = bad_val }
class c37 (a:Type) = { c37_val : a }
instance c37_good (a:Type) {| c36 a |} : c37 a = { c37_val = c36_val }
instance c37_bad (a:Type) {| c36 a |} {| bad a |} : c37 a = { c37_val = bad_val }
instance c37_bad' (a:Type) {| c36 a |} {| bad a |} : c37 a = { c37_val = bad_val }
class c38 (a:Type) = { c38_val : a }
instance c38_good (a:Type) {| c37 a |} : c38 a = { c38_val = c37_val }
instance c38_bad (a:Type) {| c37 a |} {| bad a |} : c38 a = { c38_val = bad_val }
instance c38_bad' (a:Type) {| c37 a |} {| bad a |} : c38 a = { c38_val = bad_val }
class c39 (a:Type) = { c39_val : a }
instance c39_good (a:Type) {| c38 a |} : c39 a = { c39_val = c38_val }
instance c39_bad (a:Type) {| c38 a |} {| bad a |} : c39 a = { c39_val = bad_val }
instance c39_bad' (a:Type) {| c38 a |} {| bad a |} : c39 a = { c39_val = bad_val }
class c40 (a:Type) = { c40_val : a }
instance c40_good (a:Type) {| c39 a |} : c40 a = { c40_val = c39_val }
instance c40_bad (a:Type) {| c39 a |} {| bad a |} : c40 a = { c40_val = bad_val }
instance c40_bad' (a:Type) {| c39 a |} {| bad a |} : c40 a = { c40_val = bad_val }

instance base_int : base int = { base_val = 42 }

let up : int = c40_val

let _ = assert_norm (up == 42)

(* No instance at the bottom: every combination of instances fails. *)
[@@expect_failure [228]]
let up_fail : bool = c40_val
