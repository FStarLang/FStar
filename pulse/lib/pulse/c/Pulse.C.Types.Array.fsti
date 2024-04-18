module Pulse.C.Types.Array
open Pulse.Lib.Pervasives
include Pulse.C.Types.Base
open Pulse.C.Typenat

module SZ = FStar.SizeT

// To be extracted as: t[tn]
// Per the C standard, base array types must be of nonzero size
inline_for_extraction [@@noextract_to "krml"]
let array_size_t = (n: SZ.t { SZ.v n > 0 })
val base_array_t ([@@@strictly_positive] t: Type0) (tn: Type0 (* using Typenat (or Typestring for `#define`d constants) *)) (n: array_size_t) : Type0
inline_for_extraction [@@noextract_to "krml"]
let base_array_index_t (n: array_size_t) : Tot eqtype =
  Pulse.C.Types.Array.Base.array_domain (Ghost.hide n)
[@@noextract_to "krml"]
val base_array0 (#t: Type0) (tn: Type0) (td: typedef t) (n: array_size_t) : Tot (typedef (base_array_t t tn n))

inline_for_extraction
[@@noextract_to "krml"] // proof-only
let base_array (#t: Type0) (#tn: Type0) (td: typedef t) (n: nat {SZ.fits n /\ n > 0}) (# [solve_nat_t_of_nat ()] prf: squash (norm norm_typenat (nat_t_of_nat n == tn))) : Tot (typedef (base_array_t t tn (SZ.uint_to_t n)))
= base_array0 tn td (SZ.uint_to_t n)

val base_array_index (#t: Type0) (#tn: Type0) (#n: array_size_t) (a: base_array_t t tn n) (i: base_array_index_t n) : GTot t
val base_array_eq (#t: Type0) (#tn: Type0) (#n: array_size_t) (a1 a2: base_array_t t tn n) : Ghost prop
  (requires True)
  (ensures (fun y ->
    (y <==> (a1 == a2)) /\
    (y <==> (forall (i: base_array_index_t n) . base_array_index a1 i == base_array_index a2 i))
  ))
val mk_base_array (#t: Type) (tn: Type0) (n: array_size_t) (v: Seq.seq t) : Ghost (base_array_t t tn n)
  (requires (
    Seq.length v == SZ.v n
  ))
  (ensures (fun y -> True))
val mk_base_array_index (#t: Type) (tn: Type) (n: array_size_t) (v: Seq.seq t) (i: base_array_index_t n) : Lemma
  (requires (Seq.length v == SZ.v n))
  (ensures (
    Seq.length v == SZ.v n /\
    base_array_index (mk_base_array tn n v) i == Seq.index v (SZ.v i)
  ))
  [SMTPat (base_array_index (mk_base_array tn n v) i)]

let mk_base_array_inj  (#t: Type) (tn: Type0) (n: array_size_t) (v1 v2: Seq.seq t) : Lemma
  (requires (
    Seq.length v1 == SZ.v n /\
    Seq.length v2 == SZ.v n /\
    mk_base_array tn n v1 == mk_base_array tn n v2
  ))
  (ensures (v1 == v2))
  [SMTPat (mk_base_array tn n v1); SMTPat (mk_base_array tn n v2)]
= assert (forall (i: nat) . i < SZ.v n ==> base_array_index (mk_base_array tn n v1) (SZ.uint_to_t i) == base_array_index (mk_base_array tn n v2) (SZ.uint_to_t i));
  assert (v1 `Seq.equal` v2)
val base_array_fractionable (#t: Type) (#tn: Type0) (#n: array_size_t) (a: base_array_t t tn n) (td: typedef t) : Lemma
  (
    fractionable (base_array0 tn td n) a <==>
      (forall (i: base_array_index_t n) . fractionable td (base_array_index a i))
  )
  [SMTPat (fractionable (base_array0 tn td n) a)]
val base_array_mk_fraction   (#t: Type) (#tn: Type0) (#n: array_size_t) (a: base_array_t t tn n) (td: typedef t) (p: perm) (i: base_array_index_t n) : Lemma
  (requires (
    fractionable (base_array0 tn td n) a
  ))
  (ensures (
    fractionable (base_array0 tn td n) a /\
    base_array_index (mk_fraction (base_array0 tn td n) a p) i == mk_fraction td (base_array_index a i) p
  ))
  [SMTPat (base_array_index (mk_fraction (base_array0 tn td n) a p) i)]

val base_array_index_unknown (#t: Type) (tn: Type0) (n: array_size_t) (td: typedef t) (i: base_array_index_t n) : Lemma
  (base_array_index (unknown (base_array0 tn td n)) i == unknown td)
  [SMTPat (base_array_index (unknown (base_array0 tn td n)) i)]

val base_array_index_uninitialized (#t: Type) (tn: Type0) (n: array_size_t) (td: typedef t) (i: base_array_index_t n) : Lemma
  (base_array_index (uninitialized (base_array0 tn td n)) i == uninitialized td)
  [SMTPat (base_array_index (uninitialized (base_array0 tn td n)) i)]

val base_array_index_full (#t: Type) (#tn: Type0) (#n: array_size_t) (td: typedef t) (x: base_array_t t tn n) : Lemma
  (full (base_array0 tn td n) x <==> (forall (i: base_array_index_t n) . full td (base_array_index x i)))
  [SMTPat (full (base_array0 tn td n) x)]

val has_base_array_cell
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: Tot vprop

val has_base_array_cell_post
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: stt_ghost unit emp_inames
    (has_base_array_cell r i r')
    (fun _ -> has_base_array_cell r i r' ** pure (
      SZ.v i < SZ.v n
    ))

val has_base_array_cell_dup
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: stt_ghost unit emp_inames
    (has_base_array_cell r i r')
    (fun _ -> has_base_array_cell r i r' ** has_base_array_cell r i r')

val has_base_array_cell_inj
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r1 r2: ref td)
: stt_ghost unit emp_inames
    (has_base_array_cell r i r1 ** has_base_array_cell r i r2)
    (fun _ -> has_base_array_cell r i r1 ** has_base_array_cell r i r2 ** ref_equiv r1 r2)

val has_base_array_cell_equiv_from
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r1 r2: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: stt_ghost unit emp_inames
    (has_base_array_cell r1 i r' ** ref_equiv r1 r2)
    (fun _ -> has_base_array_cell r2 i r' ** ref_equiv r1 r2)

val has_base_array_cell_equiv_to
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r1 r2: ref td)
: stt_ghost unit emp_inames
    (has_base_array_cell r i r1 ** ref_equiv r1 r2)
    (fun _ -> has_base_array_cell r i r2 ** ref_equiv r1 r2)

// contrary to array fields, one is not supposed to take an array cell directly from a base array. one should use arrays instead

// To be extracted to: t*  (array type decays to pointer type)

// We still want to prove that cutting off some cell range on the
// right-hand end of an array won't change the C pointer to which an
// array extracts to. This is why we separately introduce `array_ref`
// to represent the "base+offset" pointer, and `array` which holds the
// ghost length of an array.

[@@noextract_to "krml"] // primitive
val array_void_ptr : Type0
[@@noextract_to "krml"] // primitive
let array_ptr_gen ([@@@unused] t: Type0) : Tot Type0 = array_void_ptr
inline_for_extraction [@@noextract_to "krml"] // primitive
let array_ptr (#t: Type) (td: typedef t) = array_ptr_gen t
[@@noextract_to "krml"] // primitive
val null_array_void_ptr: array_void_ptr
[@@noextract_to "krml"] // primitive
let null_array_ptr (#t: Type) (td: typedef t) : Tot (array_ptr td) = null_array_void_ptr
val g_array_ptr_is_null (#t: Type) (#td: typedef t) (a: array_ptr td) : Ghost bool
  (requires True)
  (ensures (fun y -> y == true <==> a == null_array_ptr td))
inline_for_extraction [@@noextract_to "krml"]
let array_ref (#t: Type) (td: typedef t) = (a: array_ptr td { g_array_ptr_is_null a == false })

(*
val array_ref_base_size_type (#t: Type) (#td: typedef t) (a: array_ref td) : GTot Type0
*)
val array_ref_base_size (#t: Type) (#td: typedef t) (a: array_ptr td) : Ghost SZ.t
  (requires True)
  (ensures (fun y -> SZ.v y == 0 <==> a == null_array_ptr td))
val has_array_ref_base (#t: Type) (#td: typedef t) (a: array_ref td) (#ty: Type) (r: ref (base_array0 ty td (array_ref_base_size a))) : GTot prop
val has_array_ref_base_inj (#t: Type) (#td: typedef t) (a: array_ref td) (#ty: Type) (r1 r2: ref (base_array0 ty td (array_ref_base_size a))) : Lemma
  (requires (has_array_ref_base a r1 /\ has_array_ref_base a r2))
  (ensures (r1 == r2))
val array_ref_offset (#t: Type) (#td: typedef t) (a: array_ptr td) : Ghost SZ.t
  (requires True)
  (ensures (fun y -> SZ.v y <= SZ.v (array_ref_base_size a)))
val array_ref_base_offset_inj (#t: Type) (#td: typedef t) (#ty: Type) (a1: array_ref td) (r1: ref (base_array0 ty td (array_ref_base_size a1))) (a2: array_ref td) (r2: ref (base_array0 ty td (array_ref_base_size a2))) : Lemma
  (requires (
    array_ref_base_size a1 == array_ref_base_size a2 /\
    has_array_ref_base a1 r1 /\
    has_array_ref_base a2 r2 /\
    r1 == coerce_eq () r2 /\
    array_ref_offset a1 == array_ref_offset a2
  ))
  (ensures (a1 == a2))

inline_for_extraction [@@noextract_to "krml"]
let array_len_t (#t: Type) (#td: typedef t) (r: array_ptr td) : Tot Type0 =
  (len: Ghost.erased SZ.t { SZ.v (array_ref_offset r) + SZ.v len <= SZ.v (array_ref_base_size r) })

inline_for_extraction [@@noextract_to "krml"]
let array_or_null (#t: Type) (td: typedef t) : Tot Type0 = (r: array_ptr td & array_len_t r)

inline_for_extraction [@@noextract_to "krml"]
let array_ptr_of (#t: Type) (#td: typedef t) (ar: array_or_null td) : Tot (array_ptr td) =
  match ar with
  | (| a, _ |) -> a

let array_len_of (#t: Type) (#td: typedef t) (ar: array_or_null td) : Tot (array_len_t (array_ptr_of ar)) =
  match ar with
  | (| _, a |) -> a

inline_for_extraction [@@noextract_to "krml"]
let mk_array_or_null (#t: Type) (#td: typedef t) (a: array_ptr td) (len: array_len_t a) : Tot (array_or_null td) =
  (| a, len |)

let g_array_is_null (#t: Type) (#td: typedef t) (a: array_or_null td) : GTot bool =
  g_array_ptr_is_null (array_ptr_of a)

inline_for_extraction [@@noextract_to "krml"]
let array (#t: Type) (td: typedef t) : Tot Type0 = (a: array_or_null td { g_array_is_null a == false })

inline_for_extraction [@@noextract_to "krml"]
let array_ref_of (#t: Type) (#td: typedef t) (ar: array td) : Tot (array_ref td) =
  array_ptr_of ar

inline_for_extraction [@@noextract_to "krml"]
let mk_array (#t: Type) (#td: typedef t) (a: array_ref td) (len: array_len_t a) : Tot (array td) =
  mk_array_or_null a len

let array_length
  (#t: Type)
  (#td: typedef t)
  (a: array td)
: GTot nat
= SZ.v (dsnd a)

val array_pts_to
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
: Tot vprop

let array_pts_to_or_null
  (#t: Type)
  (#td: typedef t)
  (r: array_or_null td)
  (v: Ghost.erased (Seq.seq t))
: Tot vprop
= if g_array_is_null r
  then emp
  else array_pts_to r v

[@@noextract_to "krml"] // primitive
val array_ptr_is_null
  (#t: Type)
//  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: array_ptr td)
  (len: array_len_t r)
// : STAtomicBase bool false opened Unobservable
: stt bool
    (array_pts_to_or_null (mk_array_or_null r len) v)
    (fun b -> array_pts_to_or_null (mk_array_or_null r len) v ** pure (
      b == g_array_is_null (mk_array_or_null r len)
    ))

#set-options "--print_implicits"

inline_for_extraction [@@noextract_to "krml"]
```pulse
fn array_is_null
  (#t: Type)
//  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: array_or_null td)
// : STAtomicBase bool false opened Unobservable
requires
    (array_pts_to_or_null r v)
returns b: bool
ensures
    (array_pts_to_or_null r v ** pure (
      b == g_array_is_null r
    ))
{
  let a = array_ptr_of r;
  let len : array_len_t a = array_len_of r;
  rewrite (array_pts_to_or_null r v)
    as (array_pts_to_or_null (mk_array_or_null a len) v);
  let res = array_ptr_is_null a len;
  rewrite (array_pts_to_or_null (mk_array_or_null a len) v)
    as (array_pts_to_or_null r v);
  res
}
```
val array_pts_to_length
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
: stt_ghost unit emp_inames
    (array_pts_to r v)
    (fun _ -> array_pts_to r v ** pure (
      Seq.length v == SZ.v (dsnd r)
    ))

#set-options "--print_implicits"

let has_array_of_base
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (a: array td)
: GTot prop
=   let (| al, len |) = a in
    array_ref_base_size al == n /\
    has_array_ref_base al #tn r /\
    array_ref_offset al == 0sz /\
    Ghost.reveal len == n

let has_array_of_base_inj
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (a1 a2: array td)
: Lemma
  (requires (
      has_array_of_base #t #tn #n #td r a1 /\
      has_array_of_base #t #tn #n #td r a2
  ))
  (ensures (a1 == a2))
= let (| ar1, _ |) = a1 in
  let (| ar2, _ |) = a2 in
  array_ref_base_offset_inj #t #td #tn ar1 r ar2 r

let seq_of_base_array
  (#t: Type)
  (#tn: Type)
  (#n: array_size_t)
  (v: base_array_t t tn n)
: GTot (Seq.lseq t (SZ.v n))
= Seq.init_ghost (SZ.v n) (fun i -> base_array_index v (SZ.uint_to_t i))

val ghost_array_of_base_focus
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
  (a: array td)
: stt_ghost unit emp_inames
    (pts_to r v ** pure (
      has_array_of_base r a
    ))
    (fun _ -> array_pts_to a (seq_of_base_array v))

val ghost_array_of_base
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
: stt_ghost (a: Ghost.erased (array td) { has_array_of_base r a })
    emp_inames
    (pts_to r v)
    (fun a -> array_pts_to a (seq_of_base_array v))

let array_ref_of_base_post
  (#t: Type)
  (#tn: Type0)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
  (a: array_ref td)
  (ar: array td)
: GTot prop
=
       array_ptr_of ar == a /\
        array_ref_base_size a == Ghost.reveal n /\
        array_ref_offset a == 0sz /\
        has_array_of_base r ar /\
        Ghost.reveal (dsnd ar) == Ghost.reveal n
 
// to be extracted to just r
[@@noextract_to "krml"] // primitive
val array_ref_of_base
  (#t: Type)
  (#tn: Type0)
//  (#opened: _)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
//: STAtomicBase (array_ref td) false opened Unobservable
: stt (array_ref td)
    (pts_to r v)
    (fun a -> exists* (ar: array td) .
      array_pts_to ar (seq_of_base_array v) ** pure (
      array_ref_of_base_post v r a ar
    ))

inline_for_extraction [@@noextract_to "krml"]
```pulse
fn array_of_base
  (#t: Type)
  (#tn: Type0)
//  (#opened: _)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
// : STAtomicBase (a: array td { has_array_of_base r a }) false opened Unobservable
requires
    (pts_to r v)
returns
    a: (a: array td { has_array_of_base r a })
ensures
    (array_pts_to a (seq_of_base_array v))
{
  let al = array_ref_of_base r;
  with ga . assert (array_pts_to #t #td ga (seq_of_base_array v));
  let a = mk_array_or_null al (Ghost.hide (n <: SZ.t));
  rewrite (array_pts_to ga (seq_of_base_array v))
    as (array_pts_to a (seq_of_base_array v));
  a
}
```

val unarray_of_base
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: ref (base_array0 tn td n))
  (a: array td)
: stt_ghost (Ghost.erased (base_array_t t tn n))
    emp_inames
    (array_pts_to a v ** pure (
      has_array_of_base r a
    ))
    (fun v' -> pts_to r v' ** pure (
      Ghost.reveal v `Seq.equal` seq_of_base_array v'
    ))

val freeable_array
  (#t: Type)
  (#td: typedef t)
  (a: array td)
: Tot vprop

let freeable_or_null_array
  (#t: Type)
  (#td: typedef t)
  (a: array_or_null td)
: Tot vprop
= if g_array_is_null a
  then emp
  else freeable_array a

[@@noextract_to "krml"] // primitive
val array_ptr_alloc
  (#t: Type)
  (td: typedef t)
  (sz: SZ.t { SZ.v sz > 0 })
: stt (array_ptr td)
    emp
    (fun a ->
      exists* (ar: array_or_null td) (s: Seq.seq t) .
      freeable_or_null_array ar **
      array_pts_to_or_null ar s ** pure (
      array_ptr_of ar == a /\
      (g_array_is_null ar == false ==> array_length ar == SZ.v sz) /\
      Ghost.reveal s `Seq.equal` FStar.Seq.create (SZ.v sz) (uninitialized td)
    ))

inline_for_extraction [@@noextract_to "krml"]
```pulse
fn array_alloc
  (#t: Type)
  (td: typedef t)
  (sz: SZ.t { SZ.v sz > 0 })
requires
    emp
returns ar: array_or_null td
ensures
    (
      freeable_or_null_array ar ** (
      exists* s .
      array_pts_to_or_null ar s ** pure (
      (g_array_is_null ar == false ==> array_length ar == SZ.v sz) /\
      Ghost.reveal s == FStar.Seq.create (SZ.v sz) (uninitialized td)
    )))
{
  let a : array_ptr td = array_ptr_alloc td sz;
  with ar' s . assert (freeable_or_null_array ar' ** array_pts_to_or_null #_ #td ar' s);
  let len: array_len_t a = array_len_of ar';
  let ar = mk_array_or_null a len;
  rewrite (array_pts_to_or_null ar' s)
    as (array_pts_to_or_null ar s);
  rewrite (freeable_or_null_array ar')
    as (freeable_or_null_array ar);
  ar
}
```

let full_seq (#t: Type) (td: typedef t) (v: Seq.seq t) : GTot prop =
  forall (i: nat { i < Seq.length v }) . {:pattern (Seq.index v i)} full td (Seq.index v i)

let full_seq_seq_of_base_array
  (#t: Type0) (tn: Type0) (td: typedef t) (#n: array_size_t)
  (b: base_array_t t tn n)
: Lemma
  (ensures (full_seq td (seq_of_base_array b) <==> full (base_array0 tn td n) b))
  [SMTPat (full_seq td (seq_of_base_array b))]
= assert (forall (i: base_array_index_t n) . base_array_index b i == Seq.index (seq_of_base_array b) (SZ.v i))

[@@noextract_to "krml"] // primitive
val array_ref_free
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array_ref td)
  (n: array_len_t a)
: stt unit
    (freeable_array (mk_array a n) ** array_pts_to (mk_array a n) s ** pure (
      full_seq td s
    ))
    (fun _ -> emp)

inline_for_extraction [@@noextract_to "krml"]
```pulse
fn array_free
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
requires
    (freeable_array a ** array_pts_to a s ** pure (
      full_seq td s
    ))
ensures emp
{
  let al = array_ptr_of a;
  let n: array_len_t al = array_len_of a;
  rewrite (freeable_array a) as (freeable_array (mk_array al n));
  rewrite (array_pts_to a s) as (array_pts_to (mk_array al n) s);
  array_ref_free al n
}
```

(*
val has_array_of_ref
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (a: array td)
: Tot vprop

val has_array_of_ref_post
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (a: array td)
: STGhost unit opened
    (has_array_of_ref r a)
    (fun _ -> has_array_of_ref r a)
    (True)
    (fun _ ->
      let (| al, len |) = a in
      array_ref_base_size al == 1sz /\
      array_ref_offset al == 0sz /\
      Ghost.reveal len == 1sz
    )

// val has_array_of_ref_inj
//   (#t: Type)
//   (#td: typedef t)
//   (r: ref td)
//   (a1 a2: array td)
// : Lemma
//     (requires (
//       has_array_of_ref r a1 /\
//       has_array_of_ref r a2
//     ))
//     (ensures a1 == a2)

val ghost_array_of_ref_focus
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
  (a: array td)
: stt_ghost unit opened
    (pts_to r v ** has_array_of_ref r a)
    (fun _ -> has_array_of_ref r a ** array_pts_to a (Seq.create 1 (Ghost.reveal v)))

val ghost_array_of_ref
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: stt_ghost (Ghost.erased (array td)) opened
    (pts_to r v)
    (fun a -> array_pts_to a (Seq.create 1 (Ghost.reveal v)) ** has_array_of_ref r a)

// to be extracted to just r
[@@noextract_to "krml"] // primitive
val array_ref_of_ref
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: stt (a: array_ref td { array_ref_base_size a == 1sz /\ array_ref_offset a == 0sz })
    (pts_to r v)
    (fun a -> array_pts_to (| a, Ghost.hide 1sz |) (Seq.create 1 (Ghost.reveal v)) ** has_array_of_ref r (| a, Ghost.hide 1sz |))

inline_for_extraction [@@noextract_to "krml"]
let array_of_ref
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: stt (array td)
    (pts_to r v)
    (fun a -> array_pts_to a (Seq.create 1 (Ghost.reveal v)) ** has_array_of_ref r a)
= let al = array_ref_of_ref r in
  let a : array td = (| al, Ghost.hide 1sz |) in
  rewrite (array_pts_to _ _) (array_pts_to _ _);
  rewrite (has_array_of_ref _ _) (has_array_of_ref r a);
  return a

val unarray_of_ref
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (r: ref td)
  (a: array td)
: stt_ghost (squash (Seq.length s == 1)) opened
    (array_pts_to a s ** has_array_of_ref r a)
    (fun _ -> pts_to r (Seq.index s 0) ** has_array_of_ref r a)
*)

val has_array_cell
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: Tot vprop
(*
= SZ.v i < SZ.v (dsnd a) /\
  has_base_array_cell (array_ref_base (array_ptr_of a)) (array_ref_offset (array_ptr_of a) `SZ.add` i) r
*)

val has_array_cell_post
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r': ref td)
: stt_ghost unit emp_inames
    (has_array_cell a i r')
    (fun _ -> has_array_cell a i r' ** pure (
      SZ.v i < SZ.v (dsnd a)
    ))

val has_array_cell_has_base_array_cell
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
  (#ty: Type)
  (br: ref (base_array0 ty td (array_ref_base_size (array_ptr_of a))))
: stt_ghost (Ghost.erased SZ.t) emp_inames
    (has_array_cell a i r ** pure (
      has_array_ref_base (array_ptr_of a) br
    ))
    (fun j -> has_base_array_cell br j r ** pure (
      SZ.v j == SZ.v (array_ref_offset (array_ptr_of a)) + SZ.v i
    ))

val has_base_array_cell_has_array_cell
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
  (#ty: Type)
  (br: ref (base_array0 ty td (array_ref_base_size (array_ptr_of a))))
: stt_ghost (Ghost.erased SZ.t) emp_inames
    (has_base_array_cell br i r ** pure (
      has_array_ref_base (array_ptr_of a) br /\
      SZ.v i >= SZ.v (array_ref_offset (array_ptr_of a)) /\
      SZ.v i < SZ.v (array_ref_offset (array_ptr_of a)) + SZ.v (dsnd a)
    ))
    (fun j -> has_array_cell a j r ** pure (
      SZ.v i == SZ.v (array_ref_offset (array_ptr_of a)) + SZ.v j
    ))

val has_array_cell_inj
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r1 r2: ref td)
: stt_ghost unit emp_inames
    (
      has_array_cell a i r1 **
      has_array_cell a i r2
    )
    (fun _ ->
      has_array_cell a i r1 **
      has_array_cell a i r2 **
      ref_equiv r1 r2
    )
// = has_base_array_cell_inj (array_ref_base (array_ptr_of a)) (array_ref_offset (array_ptr_of a) `SZ.add` i) r1 r2

(*
val has_array_cell_array_of_ref
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: ref td)
  (a: array td)
: SteelGhostT unit opened
    (has_array_of_ref r a)
    (fun _ -> has_array_of_ref r a ** has_array_cell a 0sz r)
*)

val ghost_array_cell_focus
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: stt_ghost (squash (SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a)))
    emp_inames
    (array_pts_to a s ** has_array_cell a i r)
    (fun _ -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) ** pts_to r (Seq.index s (SZ.v i)) ** has_array_cell a i r)

val ghost_array_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: stt_ghost (r: Ghost.erased (ref td) { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) })
    emp_inames
    (array_pts_to a s ** pure (
      SZ.v i < Seq.length s \/ SZ.v i < SZ.v (dsnd a)
    ))
    (fun r -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) ** pts_to r (Seq.index s (SZ.v i)) ** has_array_cell a i r)

[@@noextract_to "krml"] // primitive
val array_ref_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array_ref td)
  (len: array_len_t a)
  (i: SZ.t)
: stt (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v len })
    (array_pts_to (mk_array a len) s ** pure (
      SZ.v i < Seq.length s \/ SZ.v i < SZ.v len
    ))
    (fun r -> array_pts_to (mk_array a len) (Seq.upd s (SZ.v i) (unknown td)) ** pts_to r (Seq.index s (SZ.v i)) ** has_array_cell (mk_array a len) i r)

inline_for_extraction [@@noextract_to "krml"]
```pulse
fn array_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
requires
    (array_pts_to a s ** pure (
      SZ.v i < Seq.length s \/ SZ.v i < SZ.v (dsnd a)
    ))
returns r: (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) })
ensures
    (array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) ** pts_to r (Seq.index s (SZ.v i)) ** has_array_cell a i r)
{
  let al = array_ptr_of a;
  let len = array_len_of a;
  rewrite (array_pts_to a s) as (array_pts_to (mk_array al len) s);
  let r = array_ref_cell al len i;
  rewrite (array_pts_to (mk_array al len) (Seq.upd s (SZ.v i) (unknown td))) as (array_pts_to a (Seq.upd s (SZ.v i) (unknown td)));
  rewrite (has_array_cell (mk_array al len) i r) as (has_array_cell a i r);
  r
}
```

val unarray_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (#v: Ghost.erased t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: stt_ghost (squash (SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a)))
    emp_inames
    (array_pts_to a s ** pts_to r v ** has_array_cell a i r ** pure (
      SZ.v i < Seq.length s ==> Seq.index s (SZ.v i) == unknown td
    ))
    (fun _ -> array_pts_to a (Seq.upd s (SZ.v i) v) ** has_array_cell a i r)

val array_ref_shift
  (#t: Type)
  (#td: typedef t)
  (a: array_ref td)
  (i: SZ.t)
: Ghost (array_ref td)
    (requires (SZ.v (array_ref_offset a) + SZ.v i <= SZ.v (array_ref_base_size a)))
    (ensures (fun y -> 
      array_ref_base_size y == array_ref_base_size a /\
      (forall ty r . has_array_ref_base a #ty r ==> has_array_ref_base y #ty (coerce_eq () r)) /\
      array_ref_offset y == array_ref_offset a `SZ.add` i
    ))

val array_ref_shift_zero
  (#t: Type)
  (#td: typedef t)
  (a: array_ref td)
: Lemma
    (ensures (
      array_ref_shift a 0sz == a
    ))

val array_ref_shift_assoc
  (#t: Type)
  (#td: typedef t)
  (a: array_ref td)
  (i1 i2: SZ.t)
: Lemma
    (requires (SZ.v (array_ref_offset a) + SZ.v i1 + SZ.v i2 <= SZ.v (array_ref_base_size a)))
    (ensures (
      array_ref_shift a (SZ.add i1 i2) == array_ref_shift (array_ref_shift a i1) i2
    ))

inline_for_extraction [@@noextract_to "krml"]
let array_split_l
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
: Pure (array td)
   (requires (SZ.v i <= SZ.v (dsnd a)))
   (ensures (fun _ -> True))
= let (| al, _ |) = a in
  (| al, Ghost.hide i |)

let array_split_r
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
: Ghost (array td)
   (requires (SZ.v i <= SZ.v (dsnd a)))
   (ensures (fun _ -> True))
= let (| al, len |) = a in
  (| array_ref_shift al i, Ghost.hide (len `SZ.sub` i) |)

val ghost_array_split
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: stt_ghost (squash (SZ.v i <= SZ.v (dsnd a) /\ Seq.length s == SZ.v (dsnd a)))
    emp_inames
    (array_pts_to a s ** pure (
      SZ.v i <= SZ.v (dsnd a) \/ SZ.v i <= Seq.length s
    ))
    (fun _ -> array_pts_to (array_split_l a i) (Seq.slice s 0 (SZ.v i)) **
      array_pts_to (array_split_r a i) (Seq.slice s (SZ.v i) (Seq.length s)))

let array_ref_split_post
  (#t: Type)
  (#td: typedef t)
  (s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
  (sl sr: Ghost.erased (Seq.seq t))
: GTot prop
= SZ.v i <= array_length a /\ Seq.length s == array_length a /\
  Ghost.reveal sl == Seq.slice s 0 (SZ.v i) /\
  Ghost.reveal sr == Seq.slice s (SZ.v i) (Seq.length s)

[@@noextract_to "krml"] // primitive
val array_ref_split
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (al: array_ref td)
  (len: array_len_t al)
  (i: SZ.t { SZ.v i <= SZ.v len })
: stt (array_ref td)
    (array_pts_to (mk_array al len) s)
    (fun ar -> exists* sl sr .
      array_pts_to (array_split_l (mk_array al len) i) sl **
      array_pts_to (array_split_r (mk_array al len) i) sr **
      pure (
        array_ref_split_post s (mk_array al len) i sl sr /\
        SZ.v i <= SZ.v len /\ SZ.v i <= Seq.length s /\
        ar == array_ptr_of (array_split_r (mk_array al len) i)
    ))

inline_for_extraction [@@noextract_to "krml"]
```pulse
fn array_split
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t { SZ.v i <= array_length a })
requires
  (array_pts_to a s)
returns a': array td
ensures
  (exists* sl sr .
    array_pts_to (array_split_l a i) sl **
    array_pts_to a' sr **
    pure (
      array_ref_split_post s a i sl sr /\
      SZ.v i <= array_length a /\ SZ.v i <= Seq.length s /\
      a' == array_split_r a i
  ))
{
  let al = array_ptr_of a;
  let len = array_len_of a;
  rewrite (array_pts_to a s) as (array_pts_to (mk_array al len) s);
  let ar = array_ref_split al len i;
  with sl sr . assert (
      array_pts_to (array_split_l (mk_array al len) i) sl **
      array_pts_to (array_split_r (mk_array al len) i) sr
  );
  let a' = mk_array ar (Ghost.hide (len `SZ.sub` i));
  rewrite (array_pts_to (array_split_l (mk_array al len) i) sl)
    as (array_pts_to (array_split_l a i) sl);
  rewrite (array_pts_to (array_split_r (mk_array al len) i) sr)
    as (array_pts_to a' sr);
  a'
}
```

val array_join
  (#t: Type)
  (#td: typedef t)
  (#sl #sr: Ghost.erased (Seq.seq t))
  (a al ar: array td)
  (i: SZ.t)
: stt_ghost unit emp_inames
    (array_pts_to al sl ** array_pts_to ar sr ** pure (
      SZ.v i <= SZ.v (dsnd a) /\
      al == array_split_l a i /\
      ar == array_split_r a i
    ))
    (fun _ -> array_pts_to a (sl `Seq.append` sr))

let fractionable_seq (#t: Type) (td: typedef t) (s: Seq.seq t) : GTot prop =
  forall (i: nat). i < Seq.length s ==> fractionable td (Seq.index s i)

let mk_fraction_seq (#t: Type) (td: typedef t) (s: Seq.seq t) (p: perm) : Ghost (Seq.seq t)
  (requires (fractionable_seq td s))
  (ensures (fun _ -> True))
= Seq.init_ghost (Seq.length s) (fun i -> mk_fraction td (Seq.index s i) p)

let mk_fraction_seq_full (#t: Type0) (td: typedef t) (x: Seq.seq t) : Lemma
  (requires (fractionable_seq td x))
  (ensures (mk_fraction_seq td x 1.0R == x))
  [SMTPat (mk_fraction_seq td x 1.0R)]
= assert (mk_fraction_seq td x 1.0R `Seq.equal` x)

val mk_fraction_seq_split_gen
  (#t: Type) (#td: typedef t) (r: array td) (v: Seq.seq t { fractionable_seq td v }) (p p1 p2: perm)
: stt_ghost unit emp_inames
  (array_pts_to r (mk_fraction_seq td v p) ** pure (
    p == p1 +. p2 /\ (p <=. 1.0R \/ Seq.length v == 0)
  ))
  (fun _ -> array_pts_to r (mk_fraction_seq td v p1) ** array_pts_to r (mk_fraction_seq td v p2))

val mk_fraction_seq_split
  (#t: Type) (#td: typedef t) (r: array td) (v: Ghost.erased (Seq.seq t) { fractionable_seq td v }) (p1 p2: perm)
: stt_ghost unit emp_inames
  (array_pts_to r v ** pure (
    1.0R == p1 +. p2
  ))
  (fun _ -> array_pts_to r (mk_fraction_seq td v p1) ** array_pts_to r (mk_fraction_seq td v p2))
(*
= mk_fraction_seq_full td v;
  rewrite (array_pts_to _ _) (array_pts_to _ _);
  mk_fraction_seq_split_gen r v 1.0R p1 p2
*)

val mk_fraction_seq_join
  (#t: Type) (#td: typedef t) (r: array td) (v: Seq.seq t { fractionable_seq td v }) (p1 p2: perm)
: stt_ghost unit emp_inames
  (array_pts_to r (mk_fraction_seq td v p1) ** array_pts_to r (mk_fraction_seq td v p2))
  (fun _ -> array_pts_to r (mk_fraction_seq td v (p1 +. p2)))

val array_fractional_permissions_theorem
  (#t: Type)
  (#td: typedef t)
  (v1: Seq.seq t { fractionable_seq td v1 })
  (v2: Seq.seq t { fractionable_seq td v2 })
  (p1 p2: perm)
  (r: array td)
: stt_ghost unit emp_inames
    (array_pts_to r (mk_fraction_seq td v1 p1) ** array_pts_to r (mk_fraction_seq td v2 p2) ** pure (
      full_seq td v1 /\ full_seq td v2
    ))
    (fun _ -> array_pts_to r (mk_fraction_seq td v1 p1) ** array_pts_to r (mk_fraction_seq td v2 p2) ** pure (
      v1 == v2 /\ (array_length r > 0 ==> (p1 +. p2) <=. 1.0R)
    ))

let fractionable_seq_seq_of_base_array
  (#t: Type0) (tn: Type0) (td: typedef t) (#n: array_size_t)
  (b: base_array_t t tn n)
: Lemma
  (ensures (fractionable_seq td (seq_of_base_array b) <==> fractionable (base_array0 tn td n) b))
  [SMTPat (fractionable_seq td (seq_of_base_array b))]
= assert (forall (i: base_array_index_t n) . base_array_index b i == Seq.index (seq_of_base_array b) (SZ.v i))

let array_blit_post
  (#t:_) (#td: typedef t) (s0 s1:Ghost.erased (Seq.seq t))
  (src:array td)
  (idx_src: SZ.t)
  (dst:array td)
  (idx_dst: SZ.t)
  (len: SZ.t)
  (s1' : Ghost.erased (Seq.seq t))
: GTot prop
=
  SZ.v idx_src + SZ.v len <= array_length src /\
  SZ.v idx_dst + SZ.v len <= array_length dst /\
  array_length src == Seq.length s0 /\
  array_length dst == Seq.length s1 /\
  Seq.length s1' == Seq.length s1 /\
  Seq.slice s1' (SZ.v idx_dst) (SZ.v idx_dst + SZ.v len) `Seq.equal`
    Seq.slice s0 (SZ.v idx_src) (SZ.v idx_src + SZ.v len) /\
  Seq.slice s1' 0 (SZ.v idx_dst) `Seq.equal`
    Seq.slice s1 0 (SZ.v idx_dst) /\
  Seq.slice s1' (SZ.v idx_dst + SZ.v len) (array_length dst) `Seq.equal`
    Seq.slice s1 (SZ.v idx_dst + SZ.v len) (array_length dst)

[@@noextract_to "krml"] //primitive
val array_blit_ptr
  (#t: Type)
  (#td: typedef t)
  (#v_src: Ghost.erased (Seq.seq t) { full_seq td v_src /\ fractionable_seq td v_src })
  (#p_src: perm)
  (#v_dst: Ghost.erased (Seq.seq t) { full_seq td v_dst })
  (src_ptr: array_ref td)
  (src_len: array_len_t src_ptr)
  (idx_src: SZ.t)
  (dst_ptr: array_ref td)
  (dst_len: array_len_t dst_ptr)
  (idx_dst: SZ.t)
  (len: SZ.t)
: stt (Ghost.erased (Seq.seq t))
    (array_pts_to (mk_array src_ptr src_len) (mk_fraction_seq td v_src p_src) ** array_pts_to (mk_array dst_ptr dst_len) v_dst ** pure (
        SZ.v idx_src + SZ.v len <= SZ.v src_len /\
        SZ.v idx_dst + SZ.v len <= SZ.v dst_len
    ))
    (fun v_dst' -> array_pts_to (mk_array src_ptr src_len) (mk_fraction_seq td v_src p_src) **
      array_pts_to (mk_array dst_ptr dst_len) v_dst' ** pure (
        array_blit_post v_src v_dst (mk_array src_ptr src_len) idx_src (mk_array dst_ptr dst_len) idx_dst len v_dst'
    ))

inline_for_extraction [@@noextract_to "krml"]
```pulse
fn array_blit
  (#t: Type)
  (#td: typedef t)
  (#v_src: Ghost.erased (Seq.seq t) { full_seq td v_src /\ fractionable_seq td v_src })
  (#p_src: perm)
  (#v_dst: Ghost.erased (Seq.seq t) { full_seq td v_dst })
  (src: array td)
  (idx_src: SZ.t)
  (dst: array td)
  (idx_dst: SZ.t)
  (len: SZ.t)
requires
    (array_pts_to src (mk_fraction_seq td v_src p_src) ** array_pts_to dst v_dst ** pure (
        SZ.v idx_src + SZ.v len <= array_length src /\
        SZ.v idx_dst + SZ.v len <= array_length dst
    ))
returns v_dst': (Ghost.erased (Seq.seq t))
ensures
    (array_pts_to src (mk_fraction_seq td v_src p_src) **
      array_pts_to dst v_dst' ** pure (
        array_blit_post v_src v_dst src idx_src dst idx_dst len v_dst'
    ))
{
  let a_src = array_ref_of src;
  let len_src : array_len_t a_src = array_len_of src;
  rewrite (array_pts_to src (mk_fraction_seq td v_src p_src))
    as (array_pts_to (mk_array a_src len_src) (mk_fraction_seq td v_src p_src));
  let a_dst = array_ref_of dst;
  let len_dst : array_len_t a_dst = array_len_of dst;
  rewrite (array_pts_to dst v_dst)
    as (array_pts_to (mk_array a_dst len_dst) v_dst);
  let v_dst' = array_blit_ptr a_src len_src idx_src a_dst len_dst idx_dst len;
  rewrite (array_pts_to (mk_array a_src len_src) (mk_fraction_seq td v_src p_src))
    as (array_pts_to src (mk_fraction_seq td v_src p_src));
  rewrite (array_pts_to (mk_array a_dst len_dst) v_dst')
    as (array_pts_to dst v_dst');
  v_dst'
}
```

inline_for_extraction [@@noextract_to "krml"]
```pulse
fn array_memcpy
  (#t: Type)
  (#td: typedef t)
  (#v_src: Ghost.erased (Seq.seq t) { full_seq td v_src /\ fractionable_seq td v_src })
  (#p_src: perm)
  (#v_dst: Ghost.erased (Seq.seq t) { full_seq td v_dst })
  (src: array td)
  (dst: array td)
  (len: SZ.t { SZ.v len == array_length src /\ array_length src == array_length dst })
requires
    (array_pts_to src (mk_fraction_seq td v_src p_src) ** array_pts_to dst v_dst)
ensures
    (array_pts_to src (mk_fraction_seq td v_src p_src) ** array_pts_to dst v_src)
{
  let v_dst' = array_blit src 0sz dst 0sz len;
  rewrite (array_pts_to dst v_dst')
    as (array_pts_to dst v_src);
}
```
