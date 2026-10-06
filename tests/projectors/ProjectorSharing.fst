module ProjectorSharing

(* Call-by-need sharing when a primitive projector/discriminator reduction
   exposes a constructor.

   When the weak-head evaluation of a projectee exposes a constructor, its
   arguments are still unevaluated closures on the normalizer's stack, and
   [rebuild] selects the requested one directly rather than closing all of
   them.  Any [MemoLazy] cells passed on the way -- the thunks of let-bound
   variables whose forcing exposed the projectee -- have to be filled in by
   that same code, since the usual [MemoLazy] handling is bypassed.

   The subtle case, and the one these tests pin down, is a let-bound
   *partial* application of a constructor.  Such a thunk's value is the
   constructor applied to the arguments above its [MemoLazy] frame, which is
   a strict *prefix* of the constructor's arguments -- the rest are supplied
   below that frame, by the projection site.  Filling every such cell with
   the fully saturated application instead makes the first projection's
   arguments leak into every later one. *)

noeq type r2 = | Mkr2 : int -> int -> r2
noeq type r3 = | Mkr3 : int -> int -> int -> r3
noeq type s  = | S1 : int -> s | S2 : int -> s

#push-options "--no_smt"

(* A. A let-bound partial application, projected twice.  This is the case
      that regressed: [p]'s thunk was filled with [Mkr2 1 5], so the second
      projection saw [Mkr2 1 5 99] and returned 5 -- yielding 104 -> 10. *)
let _ = assert_norm ((let p = Mkr2 1 in Mkr2?._1 (p 5) + Mkr2?._1 (p 99)) == 104)

(* B. The same term with no let-binding, hence no [MemoLazy] frame at all.
      This kept working throughout, and is here to keep the contrast. *)
let _ = assert_norm ((Mkr2?._1 ((Mkr2 1) 5) + Mkr2?._1 ((Mkr2 1) 99)) == 104)

(* C. A let-bound partial application projected only once: the cell is
      filled, but never read back. *)
let _ = assert_norm ((let p = Mkr2 1 in Mkr2?._1 (p 5)) == 5)

(* D. A let-bound *saturated* constructor, projected twice.  Here the
      [MemoLazy] frame sits above every [Arg], so the prefix is the whole
      argument list and sharing was always correct. *)
let _ = assert_norm ((let p = Mkr2 1 5 in Mkr2?._0 p + Mkr2?._1 p) == 6)

(* E. Two levels of nested partial application, each let-bound and reused,
      so that two cells with *different* prefixes are filled at once. *)
let _ = assert_norm ((let p1 = Mkr3 1 in
                      let p2 = p1 2 in
                      Mkr3?._2 (p2 5) + Mkr3?._2 (p2 99)
                        + Mkr3?._1 (p2 7) + Mkr3?._0 (p1 5 6)) == 107)

(* F. One partial application saturated at three different projections. *)
let _ = assert_norm ((let p = Mkr3 1 in
                      Mkr3?._1 (p 5 0) + Mkr3?._2 (p 8 9) + Mkr3?._0 (p 4 5)) == 15)

(* G. Discriminators over a let-bound partial application. *)
let _ = assert_norm ((let q = S1 in S1? (q 5) && S2? (q 3)) == false)
let _ = assert_norm ((let q = S1 in S1? (q 5) && S1? (q 3)) == true)

#pop-options

(* H. Projecting a field of the wrong constructor must stay stuck, rather
      than picking up a value shared through the projectee's thunk.  Stated
      as a failure, since "does not reduce" has no positive form: were the
      cell to be misfilled, [S2?._0 (q 7)] could yield the 5 belonging to
      the sibling [S1] application and this assertion would go through.

      Two errors are expected, both #19: the assertion itself, which gets
      stuck at [5 + (S1 7)._0], and the [S2? _] precondition of [S2?._0],
      which is of course not provable of an [S1].  This case sits outside
      the [--no_smt] block so that both surface as #19 rather than #298. *)
[@@expect_failure [19; 19]]
let _ = assert_norm ((let q = S1 in S1?._0 (q 5) + S2?._0 (q 7)) == 12)

#push-options "--no_smt"

(* I. A single cell read back several times, at the same saturation. *)
let _ = assert_norm ((let p = Mkr3 1 in
                      Mkr3?._2 (p 2 5) + Mkr3?._2 (p 2 50) + Mkr3?._1 (p 2 60)) == 57)

#pop-options

(* The same cases once more, under the ambient SMT encoding rather than
   [assert_norm], since projectors reduce there too. *)
let _ = assert ((let p = Mkr2 1 in Mkr2?._1 (p 5) + Mkr2?._1 (p 99)) == 104)
let _ = assert ((let q = S1 in S1? (q 5) && S2? (q 3)) == false)
