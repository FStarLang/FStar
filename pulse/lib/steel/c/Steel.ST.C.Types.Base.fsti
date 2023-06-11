module Steel.ST.C.Types.Base
open Steel.ST.Util

module P = Steel.FractionalPermission

/// Helper to compose two permissions into one
val prod_perm (p1 p2: P.perm) : Pure P.perm
  (requires True)
  (ensures (fun p ->
    ((p1 `P.lesser_equal_perm` P.full_perm /\ p2 `P.lesser_equal_perm` P.full_perm) ==>
    p `P.lesser_equal_perm` P.full_perm) /\
    p.v == (let open FStar.Real in p1.v *. p2.v)
  ))

[@@noextract_to "krml"] // proof-only
val typedef (t: Type0) : Type0

inline_for_extraction [@@noextract_to "krml"]
let typeof (#t: Type0) (td: typedef t) : Tot Type0 = t

val fractionable (#t: Type0) (td: typedef t) (x: t) : GTot prop

val mk_fraction (#t: Type0) (td: typedef t) (x: t) (p: P.perm) : Ghost t
  (requires (fractionable td x))
  (ensures (fun y -> p `P.lesser_equal_perm` P.full_perm ==> fractionable td y))

val mk_fraction_full (#t: Type0) (td: typedef t) (x: t) : Lemma
  (requires (fractionable td x))
  (ensures (mk_fraction td x P.full_perm == x))
  [SMTPat (mk_fraction td x P.full_perm)]

val mk_fraction_compose (#t: Type0) (td: typedef t) (x: t) (p1 p2: P.perm) : Lemma
  (requires (fractionable td x /\ p1 `P.lesser_equal_perm` P.full_perm /\ p2 `P.lesser_equal_perm` P.full_perm))
  (ensures (mk_fraction td (mk_fraction td x p1) p2 == mk_fraction td x (p1 `prod_perm` p2)))

val full (#t: Type0) (td: typedef t) (v: t) : GTot prop

val uninitialized (#t: Type0) (td: typedef t) : Ghost t
  (requires True)
  (ensures (fun y -> full td y /\ fractionable td y))

val unknown (#t: Type0) (td: typedef t) : Ghost t
  (requires True)
  (ensures (fun y -> fractionable td y))

val full_not_unknown
  (#t: Type)
  (td: typedef t)
  (v: t)
: Lemma
  (requires (full td v))
  (ensures (~ (v == unknown td)))
  [SMTPat (full td v)]

val mk_fraction_unknown (#t: Type0) (td: typedef t) (p: P.perm) : Lemma
  (ensures (mk_fraction td (unknown td) p == unknown td))

val mk_fraction_eq_unknown (#t: Type0) (td: typedef t) (v: t) (p: P.perm) : Lemma
  (requires (fractionable td v /\ mk_fraction td v p == unknown td))
  (ensures (v == unknown td))


// To be extracted as: void*

// FIXME: Currently, Karamel does not directly support
// void*. examples/steel/arraystructs currently has a stopgap in
// lib/steel_c.h, whose contents should be moved to krmllib.h, unless
// direct support for void* is added to Karamel.

[@@noextract_to "krml"] // primitive
val void_ptr : Type0
 
// To be extracted as: NULL
[@@noextract_to "krml"] // primitive
val void_null: void_ptr

// To be extracted as: *t
[@@noextract_to "krml"] // primitive
let ptr_gen (t: Type) : Tot Type0 = void_ptr
[@@noextract_to "krml"] // primitive
let null_gen (t: Type) : Tot (ptr_gen t) = void_null

inline_for_extraction [@@noextract_to "krml"] // primitive
let ptr (#t: Type) (td: typedef t) : Tot Type0 = ptr_gen t
inline_for_extraction [@@noextract_to "krml"] // primitive
let null (#t: Type) (td: typedef t) : Tot (ptr td) = null_gen t

inline_for_extraction [@@noextract_to "krml"]
let ref (#t: Type) (td: typedef t) : Tot Type0 = (p: ptr td { ~ (p == null td) })

val pts_to (#t: Type) (#td: typedef t) (r: ref td) ([@@@smt_fallback] v: Ghost.erased t) : vprop

let pts_to_or_null
  (#t: Type) (#td: typedef t) (p: ptr td) (v: Ghost.erased t) : vprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (p == null _)
  then emp
  else pts_to p v

[@@noextract_to "krml"] // primitive
val is_null
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
: STAtomicBase bool false opened Unobservable
    (pts_to_or_null p v)
    (fun _ -> pts_to_or_null p v)
    (True)
    (fun res -> res == true <==> p == null _)

let assert_null
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
: STGhost unit opened
    (pts_to_or_null p v)
    (fun _ -> emp)
    (p == null _)
    (fun _ -> True)
= rewrite (pts_to_or_null p v) emp

let assert_not_null
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
: STGhost (squash (~ (p == null _))) opened
    (pts_to_or_null p v)
    (fun _ -> pts_to p v)
    (~ (p == null _))
    (fun _ -> True)
= rewrite (pts_to_or_null p v) (pts_to p v)

val ref_equiv
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: Tot vprop

val pts_to_equiv
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
  (v: Ghost.erased t)
: STGhostT unit opened
    (ref_equiv r1 r2 `star` pts_to r1 v)
    (fun _ -> ref_equiv r1 r2 `star` pts_to r2 v)

val freeable
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
: Tot vprop

val freeable_dup
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
: STGhostT unit opened
    (freeable r)
    (fun _ -> freeable r `star` freeable r)

val freeable_equiv
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
: STGhostT unit opened
    (ref_equiv r1 r2 `star` freeable r1)
    (fun _ -> ref_equiv r1 r2 `star` freeable r2)

let freeable_or_null
  (#t: Type)
  (#td: typedef t)
  (r: ptr td)
: Tot vprop
= if FStar.StrongExcludedMiddle.strong_excluded_middle (r == null _)
  then emp
  else freeable r

(*
let freeable_or_null_dup
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ptr td)
: SteelGhostT vprop opened
    (freeable_or_null r)
    (fun _ -> freeable_or_null r `star` freeable_or_null r)
= if FStar.StrongExcludedMiddle.strong_excluded_middle (r == null _)
  then ()
  else freeable r
*)

[@@noextract_to "krml"] // primitive
val alloc
  (#t: Type)
  (td: typedef t)
: STT (ptr td)
    emp
    (fun p -> pts_to_or_null p (uninitialized td) `star` freeable_or_null p)

[@@noextract_to "krml"] // primitive
val free
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: ST unit
    (pts_to r v `star` freeable r)
    (fun _ -> emp)
    (
      full td v
    )
    (fun _ -> True)

val mk_fraction_split_gen
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p p1 p2: P.perm) : STGhost unit opened
  (pts_to r (mk_fraction td v p))
  (fun _ -> pts_to r (mk_fraction td v p1) `star` pts_to r (mk_fraction td v p2))
  (p == p1 `P.sum_perm` p2 /\ p `P.lesser_equal_perm` P.full_perm)
  (fun _ -> True)

let mk_fraction_split
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: ref td) (v: Ghost.erased t { fractionable td v }) (p1 p2: P.perm) : STGhost unit opened
  (pts_to r v)
  (fun _ -> pts_to r (mk_fraction td v p1) `star` pts_to r (mk_fraction td v p2))
  (P.full_perm == p1 `P.sum_perm` p2)
  (fun _ -> True)
= mk_fraction_full td v;
  rewrite (pts_to _ _) (pts_to _ _);
  mk_fraction_split_gen r v P.full_perm p1 p2

val mk_fraction_join
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p1 p2: P.perm)
: STGhostT unit opened
  (pts_to r (mk_fraction td v p1) `star` pts_to r (mk_fraction td v p2))
  (fun _ -> pts_to r (mk_fraction td v (p1 `P.sum_perm` p2)))

val fractional_permissions_theorem
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (v1: t { fractionable td v1 })
  (v2: t { fractionable td v2 })
  (p1 p2: P.perm)
  (r: ref td)
: STGhost unit opened
    (pts_to r (mk_fraction td v1 p1) `star` pts_to r (mk_fraction td v2 p2))
    (fun _ -> pts_to r (mk_fraction td v1 p1) `star` pts_to r (mk_fraction td v2 p2))
    (full td v1 /\ full td v2)
    (fun _ -> v1 == v2 /\ (p1 `P.sum_perm` p2) `P.lesser_equal_perm` P.full_perm)

[@@noextract_to "krml"] // primitive
val copy
  (#t: Type)
  (#td: typedef t)
  (#v_src: Ghost.erased t { full td v_src /\ fractionable td v_src })
  (#p_src: P.perm)
  (#v_dst: Ghost.erased t { full td v_dst })
  (src: ref td)
  (dst: ref td)
: STT unit
    (pts_to src (mk_fraction td v_src p_src) `star` pts_to dst v_dst)
    (fun _ -> pts_to src (mk_fraction td v_src p_src) `star` pts_to dst v_src)

val norm_field_attr : unit

noextract
let norm_field_steps = [
  delta_attr [`%norm_field_attr];
  iota; zeta; primops;
]
