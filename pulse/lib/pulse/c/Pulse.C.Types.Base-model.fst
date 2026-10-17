module Pulse.C.Types.Base
#lang-pulse

(* Model implementation of Pulse.C.Types.Base: verified, but never extracted.
   A typedef is modeled as a record of its pure operations (fractions, full,
   uninitialized, unknown values) together with their laws. Pointers are
   natural numbers (0 is null), and `alloc` always returns null, so all
   points-to style predicates on non-null references can be modeled as
   `pure False`. *)

open Pulse.Lib.Pervasives

let prod_perm p1 p2 =
  let open FStar.Real in
  p1 *. p2

noeq
type typedef (t: Type0) : Type0 = {
  td_fractionable: t -> prop;
  td_mk_fraction: (x: t) -> (p: perm) -> Pure t
    (requires (td_fractionable x))
    (ensures (fun y -> p <=. 1.0R ==> td_fractionable y));
  td_mk_fraction_full: (x: t) -> Lemma
    (requires (td_fractionable x))
    (ensures (td_mk_fraction x 1.0R == x));
  td_mk_fraction_compose: (x: t) -> (p1: perm) -> (p2: perm) -> Lemma
    (requires (td_fractionable x /\ p1 <=. 1.0R /\ p2 <=. 1.0R))
    (ensures (td_mk_fraction (td_mk_fraction x p1) p2 == td_mk_fraction x (p1 `prod_perm` p2)));
  td_full: t -> prop;
  td_uninitialized: (y: t { td_full y /\ td_fractionable y });
  td_unknown: (y: t { td_fractionable y });
  td_full_not_unknown: (v: t) -> Lemma
    (requires (td_full v))
    (ensures (~ (v == td_unknown)));
  td_mk_fraction_unknown: (p: perm) -> Lemma
    (td_mk_fraction td_unknown p == td_unknown);
  td_mk_fraction_eq_unknown: (v: t) -> (p: perm) -> Lemma
    (requires (td_fractionable v /\ td_mk_fraction v p == td_unknown))
    (ensures (v == td_unknown));
}

let fractionable td x = td.td_fractionable x

let mk_fraction td x p = td.td_mk_fraction x p

let mk_fraction_full td x = td.td_mk_fraction_full x

let mk_fraction_compose td x p1 p2 = td.td_mk_fraction_compose x p1 p2

let full td v = td.td_full v

let uninitialized td = td.td_uninitialized

let unknown td = td.td_unknown

let full_not_unknown td v = td.td_full_not_unknown v

let mk_fraction_unknown td p = td.td_mk_fraction_unknown p

let mk_fraction_eq_unknown td v p = td.td_mk_fraction_eq_unknown v p

let void_ptr = nat

let void_null = 0

let ptr_gen _ = nat

let null_gen _ = 0

let ghost_void_ptr_of_ptr_gen x = x

let ghost_ptr_gen_of_void_ptr x _ = x

let ghost_void_ptr_of_ptr_gen_of_void_ptr _ _ = ()

let ghost_ptr_gen_of_void_ptr_of_ptr_gen _ = ()

let pts_to _ _ = pure False

fn is_null
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (p: ptr td)
requires pts_to_or_null p v
returns res: bool
ensures pts_to_or_null p v ** pure (res == true <==> p == null _)
{
  let p' : nat = p;
  (p' = 0)
}

fn void_ptr_of_ptr (#t: Type) (#td: typedef t) (#v: Ghost.erased t) (x: ptr td)
requires pts_to_or_null x v
returns y: void_ptr
ensures pts_to_or_null x v ** pure (y == ghost_void_ptr_of_ptr_gen x)
{
  let y : nat = x;
  y
}

fn ptr_of_void_ptr (#t: Type) (#td: typedef t) (#v: Ghost.erased t) (x: void_ptr)
requires pts_to_or_null #t #td (ghost_ptr_gen_of_void_ptr x t) v
returns y: ptr td
ensures pts_to_or_null y v ** pure (y == ghost_ptr_gen_of_void_ptr x t)
{
  let y : nat = x;
  rewrite (pts_to_or_null #t #td (ghost_ptr_gen_of_void_ptr x t) v)
    as (pts_to_or_null #t #td y v);
  y
}

let ref_equiv _ _ = pure False

ghost
fn pts_to_equiv
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
  (v: Ghost.erased t)
requires ref_equiv r1 r2 ** pts_to r1 v
ensures ref_equiv r1 r2 ** pts_to r2 v
{
  unfold (pts_to r1 v);
  unreachable ()
}

let freeable _ = emp

ghost
fn freeable_dup
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
requires freeable r
ensures freeable r ** freeable r
{
  unfold (freeable r);
  fold (freeable r);
  fold (freeable r)
}

ghost
fn freeable_equiv
  (#t: Type)
  (#td: typedef t)
  (r1 r2: ref td)
requires ref_equiv r1 r2 ** freeable r1
ensures ref_equiv r1 r2 ** freeable r2
{
  unfold (ref_equiv r1 r2);
  unreachable ()
}

fn alloc
  (#t: Type)
  (td: typedef t)
requires emp
returns p: ptr td
ensures pts_to_or_null p (uninitialized td) ** freeable_or_null p
{
  let p : ptr td = null_gen t;
  rewrite emp as (pts_to_or_null p (uninitialized td));
  rewrite emp as (freeable_or_null p);
  p
}

fn free
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
requires pts_to r v ** freeable r ** pure (full td v)
ensures emp
{
  unfold (pts_to r v);
  unreachable ()
}

ghost
fn mk_fraction_split_gen
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p p1 p2: perm)
requires pts_to r (mk_fraction td v p) ** pure (p == p1 +. p2 /\ p <=. 1.0R)
ensures pts_to r (mk_fraction td v p1) ** pts_to r (mk_fraction td v p2)
{
  unfold (pts_to r (mk_fraction td v p));
  unreachable ()
}

ghost
fn mk_fraction_split
  (#t: Type) (#td: typedef t) (r: ref td) (v: Ghost.erased t { fractionable td v }) (p1 p2: perm)
requires pts_to r v ** pure (1.0R == p1 +. p2)
ensures pts_to r (mk_fraction td v p1) ** pts_to r (mk_fraction td v p2)
{
  unfold (pts_to r v);
  unreachable ()
}

ghost
fn mk_fraction_join
  (#t: Type) (#td: typedef t) (r: ref td) (v: t { fractionable td v }) (p1 p2: perm)
requires pts_to r (mk_fraction td v p1) ** pts_to r (mk_fraction td v p2)
ensures pts_to r (mk_fraction td v (p1 +. p2))
{
  unfold (pts_to r (mk_fraction td v p1));
  unreachable ()
}

ghost
fn fractional_permissions_theorem
  (#t: Type)
  (#td: typedef t)
  (v1: t { fractionable td v1 })
  (v2: t { fractionable td v2 })
  (p1 p2: perm)
  (r: ref td)
requires pts_to r (mk_fraction td v1 p1) ** pts_to r (mk_fraction td v2 p2) ** pure (full td v1 /\ full td v2)
ensures pts_to r (mk_fraction td v1 p1) ** pts_to r (mk_fraction td v2 p2) ** pure (v1 == v2 /\ (p1 +. p2) <=. 1.0R)
{
  unfold (pts_to r (mk_fraction td v1 p1));
  unreachable ()
}

fn copy
  (#t: Type)
  (#td: typedef t)
  (#v_src: Ghost.erased t { full td v_src /\ fractionable td v_src })
  (#p_src: perm)
  (#v_dst: Ghost.erased t { full td v_dst })
  (src: ref td)
  (dst: ref td)
requires pts_to src (mk_fraction td v_src p_src) ** pts_to dst v_dst
ensures pts_to src (mk_fraction td v_src p_src) ** pts_to dst v_src
{
  unfold (pts_to dst v_dst);
  unreachable ()
}

let norm_field_attr = ()
