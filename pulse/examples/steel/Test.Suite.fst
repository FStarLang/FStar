module Test.Suite

open Steel.RST
module A = Steel.Array
module U32 = FStar.UInt32
module P = LowStar.Permissions

open FStar.Algebra.CommMonoid.Equiv
open FStar.Tactics
open FStar.Tactics.CanonCommMonoidSimple.Equiv

inline_for_extraction noextract let resolve_split () : Tac unit =
  apply_lemma (quote can_be_split_into_star);
  canon_monoid Steel.Tactics.req Steel.Tactics.rm

inline_for_extraction noextract let resolve_res_eq () : Tac unit =
  refine_intro ();
  flip ();
  canon_monoid Steel.Tactics.req Steel.Tactics.rm

(**** Tactics unit testing *)

assume val r1 : resource
assume val r2 : resource
assume val r3 : resource
assume val r4 : resource
assume val r5 : resource

let _ =
  assert_by_tactic ((r1 <*> r2) `can_be_split_into` (r1, r2)) resolve_split

let assert_delta_equal
  (outer: resource)
  (inner: resource)
  (delta: resource)
  : Lemma
    (requires (with_tactic resolve_split (squash (outer `can_be_split_into` (inner, delta)))))
    (ensures (True))
  = ()

let _ =
  assert_delta_equal (r1 <*> r2) r1 r2

let _ =
  assert_delta_equal (r1 <*> r2 <*> r3 <*> r4 <*> r5) (r2 <*> r4) (r1 <*> r3 <*> r5)

[@expect_failure]
let _ =
  assert_delta_equal (r1 <*> r2 <*> r3 <*> r4 <*> r5) (r2 <*> r4) (r1 <*> r5)

let _ =
  assert_delta_equal (r1 <*> ((r2 <*> r3) <*> r4) <*> r5) (r4 <*> r2) (r3 <*> r1 <*> r5)

let _ =
  assert_delta_equal (r1 <*> ((r2 <*> r3) <*> r4 <*> r5)) (r2 <*> r4) ((r1 <*> r3) <*> r5)

let _ =
  assert_delta_equal ((r1 <*> r2) <*> (r3 <*> r4 <*> r5)) (r2 <*> r4) (r1 <*> (r3 <*> r5))

let _ =
  assert_delta_equal (r1 <*> (r2 <*> r3) <*> (r4 <*> r5)) (r2 <*> r4) (r1 <*> r3 <*> r5)


(**** Frame and unification unit testing *)

let test1 (b1 b2 b3: A.array U32.t) : RST unit
  (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun _ -> A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let x = rst_frame
    (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
    (fun _ -> A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3 )
    (fun _ -> A.index b1 0ul)
  in
  ()

//TODO: cannot infer inv for resource list when order is changed, should be solved with
//effect layering
[@expect_failure]
let test2 (b1 b2 b3: A.array U32.t) : RST unit
  (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun _ -> A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let x = rst_frame
    (A.array_resource b2 <*> A.array_resource b1 <*> A.array_resource b3)
    (fun _ -> A.array_resource b2 <*> A.array_resource b1 <*> A.array_resource b3 )
    (fun _ -> A.index b1 0ul)
  in
  ()

//TODO: fix, unable to infer invariant equivalence for AC rewriting (should be OK when we have effect layering)
[@expect_failure]
let test3 (b1 b2 b3: A.array U32.t) : RST unit
  (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun _ -> A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let x = rst_frame
    (A.array_resource b2 <*> A.array_resource b1 <*> A.array_resource b3)
    (fun _ -> A.array_resource b2 <*> A.array_resource b1 <*> A.array_resource b3 )
    (fun _ -> A.index b2 0ul)
  in
  ()

//TODO: How to infer can_be_split_into_intro_by_tactic automatically ?
let test4 (b1 b2 b3: A.array U32.t) : RST unit
  (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun _ -> A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun h ->
    can_be_split_into_intro_by_tactic (A.array_resource b1)
      (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
      (A.array_resource b2 <*> A.array_resource b3) ();
    P.allows_write (A.get_rperm b1 (focus_rmem h #(A.array_resource b2 <*> A.array_resource b3) (A.array_resource b1)))
  )
  (fun _ _ _ -> True)
  =
  let x = rst_frame
    (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
    (fun _ -> A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3 )
    (fun _ -> A.index b1 0ul)
  in
  rst_frame
    (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
    (fun _ -> A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3 )
    (fun _ -> A.upd b1 0ul x)

//TODO: fix, unification fails with the last argument of upd
[@expect_failure]
let test5 (b1 : A.array U32.t) : RST unit
  (A.array_resource b1)
  (fun _ -> A.array_resource b1)
  (fun h -> P.allows_write (A.get_rperm b1 h))
  (fun _ _ _ -> True)
  =
  let x = rst_frame
    (A.array_resource b1)
    (fun _ -> A.array_resource b1 )
    (fun _ -> A.index b1 0ul)
  in
  rst_frame
    (A.array_resource b1)
    (fun _ -> A.array_resource b1)
    (fun _ -> A.upd b1 0ul U32.(x +%^ 1ul))

//TODO: fix, the delta on the pre and post should not necessarily be syntactically the same. More generally, the tactic should infer one delta from the pre, another from the post, then check their equality in normalized form
[@expect_failure]
let test6 (b1 b2 b3: A.array U32.t) : RST unit
  (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun _ -> A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
  (fun _ -> True)
  (fun _ _ _ -> True)
  =
  let x = rst_frame
    (A.array_resource b1 <*> A.array_resource b2 <*> A.array_resource b3)
    (fun _ -> A.array_resource b1 <*> A.array_resource b3 <*> A.array_resource b2)
    (fun _ -> A.index b1 0ul)
  in
  ()
