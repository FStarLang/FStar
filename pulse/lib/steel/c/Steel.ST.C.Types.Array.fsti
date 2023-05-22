module Steel.ST.C.Types.Array
open Steel.ST.Util
include Steel.ST.C.Types.Base
open Steel.C.Typenat

module P = Steel.FractionalPermission
module SZ = FStar.SizeT

// To be extracted as: t[tn]
// Per the C standard, base array types must be of nonzero size
inline_for_extraction [@@noextract_to "krml"]
let array_size_t = (n: SZ.t { SZ.v n > 0 })
val base_array_t ([@@@strictly_positive] t: Type0) (tn: Type0 (* using Typenat (or Typestring for `#define`d constants) *)) (n: array_size_t) : Type0
inline_for_extraction [@@noextract_to "krml"] // MUST be syntactically equal to Steel.C.Model.Array.array_domain
let base_array_index_t (n: array_size_t) : Tot eqtype = (i: SZ.t { SZ.v i < SZ.v n })
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
val base_array_mk_fraction   (#t: Type) (#tn: Type0) (#n: array_size_t) (a: base_array_t t tn n) (td: typedef t) (p: P.perm) (i: base_array_index_t n) : Lemma
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
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: STGhost unit opened
    (has_base_array_cell r i r')
    (fun _ -> has_base_array_cell r i r')
    (True)
    (fun _ -> SZ.v i < SZ.v n)

val has_base_array_cell_dup
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: STGhostT unit opened
    (has_base_array_cell r i r')
    (fun _ -> has_base_array_cell r i r' `star` has_base_array_cell r i r')

val has_base_array_cell_inj
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r1 r2: ref td)
: STGhostT unit opened
    (has_base_array_cell r i r1 `star` has_base_array_cell r i r2)
    (fun _ -> has_base_array_cell r i r1 `star` has_base_array_cell r i r2 `star` ref_equiv r1 r2)

val has_base_array_cell_equiv_from
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r1 r2: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
: STGhostT unit opened
    (has_base_array_cell r1 i r' `star` ref_equiv r1 r2)
    (fun _ -> has_base_array_cell r2 i r' `star` ref_equiv r1 r2)

val has_base_array_cell_equiv_to
  (#opened: _)
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r1 r2: ref td)
: STGhostT unit opened
    (has_base_array_cell r i r1 `star` ref_equiv r1 r2)
    (fun _ -> has_base_array_cell r i r2 `star` ref_equiv r1 r2)

// contrary to array fields, one is not supposed to take an array cell directly from a base array. one should use arrays instead

// To be extracted to: t*  (array type decays to pointer type)

// We still want to prove that cutting off some cell range on the
// right-hand end of an array won't change the C pointer to which an
// array extracts to. This is why we separately introduce `array_ref`
// to represent the "base+offset" pointer, and `array` which holds the
// ghost length of an array.

[@@noextract_to "krml"] // primitive
val array_ptr_gen ([@@@strictly_positive] t: Type0) : Tot Type0
inline_for_extraction [@@noextract_to "krml"] // primitive
let array_ptr (#t: Type) (td: typedef t) = array_ptr_gen t
[@@noextract_to "krml"] // primitive
val null_array_ptr (#t: Type) (td: typedef t) : Tot (array_ptr td)
val g_array_ptr_is_null (#t: Type) (#td: typedef t) (a: array_ptr td) : Ghost bool
  (requires True)
  (ensures (fun y -> y == true <==> a == null_array_ptr _))
inline_for_extraction [@@noextract_to "krml"]
let array_ref (#t: Type) (td: typedef t) = (a: array_ptr td { g_array_ptr_is_null a == false })

(*
val array_ref_base_size_type (#t: Type) (#td: typedef t) (a: array_ref td) : GTot Type0
*)
val array_ref_base_size (#t: Type) (#td: typedef t) (a: array_ptr td) : Ghost SZ.t
  (requires True)
  (ensures (fun y -> SZ.v y == 0 <==> a == null_array_ptr _))
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

let g_array_is_null (#t: Type) (#td: typedef t) (a: array_or_null td) : GTot bool =
  g_array_ptr_is_null (array_ptr_of a)

inline_for_extraction [@@noextract_to "krml"]
let array (#t: Type) (td: typedef t) : Tot Type0 = (a: array_or_null td { g_array_is_null a == false })

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
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: array_ptr td)
  (len: array_len_t r)
: STAtomicBase bool false opened Unobservable
    (array_pts_to_or_null (| r, len |) v)
    (fun _ -> array_pts_to_or_null (| r, len |) v)
    (True)
    (fun b -> b == g_array_is_null (| r, len |))

inline_for_extraction [@@noextract_to "krml"]
let array_is_null
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: array_or_null td)
: STAtomicBase bool false opened Unobservable
    (array_pts_to_or_null r v)
    (fun _ -> array_pts_to_or_null r v)
    (True)
    (fun b -> b == g_array_is_null r)
= let a = array_ptr_of r in
  let len : array_len_t a = dsnd r in
  rewrite (array_pts_to_or_null _ _) (array_pts_to_or_null (| a, len |) v);
  let res = array_ptr_is_null a len in
  rewrite (array_pts_to_or_null _ _) (array_pts_to_or_null r v);
  return res

val array_pts_to_length
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
: STGhost unit opened
    (array_pts_to r v)
    (fun _ -> array_pts_to r v)
    (True)
    (fun _ -> Seq.length v == SZ.v (dsnd r))

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
  (#opened: _)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
  (a: array td)
: STGhost unit opened
    (pts_to r v)
    (fun _ -> array_pts_to a (seq_of_base_array v))
    (has_array_of_base r a)
    (fun _ -> True)

val ghost_array_of_base
  (#t: Type)
  (#tn: Type0)
  (#opened: _)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
: STGhostT (a: Ghost.erased (array td) { has_array_of_base r a }) opened
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
  (#opened: _)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
: STAtomicBase (array_ref td) false opened Unobservable
    (pts_to r v)
    (fun a -> exists_ (fun (ar: array td) ->
      array_pts_to ar (seq_of_base_array v) `star` pure (
      array_ref_of_base_post v r a ar
    )))
    (True)
    (fun _ -> True)

inline_for_extraction [@@noextract_to "krml"]
let array_of_base
  (#t: Type)
  (#tn: Type0)
  (#opened: _)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
: STAtomicBase (a: array td { has_array_of_base r a }) false opened Unobservable
    (pts_to r v)
    (fun a -> array_pts_to a (seq_of_base_array v))
    (True)
    (fun _ -> True)
= let al = array_ref_of_base r in
  let _ = elim_exists () in
  elim_pure _;
  let a = (| al, Ghost.hide (n <: SZ.t) |) in
  rewrite (array_pts_to _ _) (array_pts_to _ _);
  return a

val unarray_of_base
  (#t: Type)
  (#tn: Type0)
  (#opened: _)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: ref (base_array0 tn td n))
  (a: array td)
: STGhost (Ghost.erased (base_array_t t tn n)) opened
    (array_pts_to a v)
    (fun v' -> pts_to r v')
    (
      has_array_of_base r a
    )
    (fun v' -> Ghost.reveal v `Seq.equal` seq_of_base_array v')

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
: STT (array_ptr td)
    emp
    (fun a ->
      exists_ (fun (ar: array_or_null td) -> exists_ (fun (s: Seq.seq t) ->
      freeable_or_null_array ar `star`
      array_pts_to_or_null ar s `star` pure (
      array_ptr_of ar == a /\
      (g_array_is_null ar == false ==> array_length ar == SZ.v sz) /\
      Ghost.reveal s `Seq.equal` FStar.Seq.create (SZ.v sz) (uninitialized td)
    ))))

inline_for_extraction [@@noextract_to "krml"]
let array_alloc
  (#t: Type)
  (td: typedef t)
  (sz: SZ.t { SZ.v sz > 0 })
: STT (array_or_null td)
    emp
    (fun ar ->
      freeable_or_null_array ar `star`
      exists_ (fun s ->
      array_pts_to_or_null ar s `star` pure (
      (g_array_is_null ar == false ==> array_length ar == SZ.v sz) /\
      Ghost.reveal s == FStar.Seq.create (SZ.v sz) (uninitialized td)
    )))
= let a : array_ptr td = array_ptr_alloc td sz in
  let ar' : Ghost.erased (array_or_null td) = elim_exists () in
  let s = elim_exists () in
  elim_pure _;
  let len : array_len_t a = dsnd ar' in
  let ar = (| a, len |) in
  rewrite (array_pts_to_or_null _ _) (array_pts_to_or_null ar s);
  rewrite (freeable_or_null_array _) (freeable_or_null_array ar);
  noop ();
  return ar

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
: ST unit
    (freeable_array (| a, n |) `star` array_pts_to (| a, n |) s)
    (fun _ -> emp)
    (full_seq td s)
    (fun _ -> True)

inline_for_extraction [@@noextract_to "krml"]
let array_free
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
: ST unit
    (freeable_array a `star` array_pts_to a s)
    (fun _ -> emp)
    (full_seq td s)
    (fun _ -> True)
= let al = array_ptr_of a in
  let n: array_len_t al = dsnd a in
  rewrite (freeable_array _) (freeable_array (| al, n |));
  rewrite (array_pts_to _ _) (array_pts_to (| al, n |) s);
  array_ref_free al n

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
: STGhostT unit opened
    (pts_to r v `star` has_array_of_ref r a)
    (fun _ -> has_array_of_ref r a `star` array_pts_to a (Seq.create 1 (Ghost.reveal v)))

val ghost_array_of_ref
  (#t: Type)
  (#opened: _)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: STGhostT (Ghost.erased (array td)) opened
    (pts_to r v)
    (fun a -> array_pts_to a (Seq.create 1 (Ghost.reveal v)) `star` has_array_of_ref r a)

// to be extracted to just r
[@@noextract_to "krml"] // primitive
val array_ref_of_ref
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: STT (a: array_ref td { array_ref_base_size a == 1sz /\ array_ref_offset a == 0sz })
    (pts_to r v)
    (fun a -> array_pts_to (| a, Ghost.hide 1sz |) (Seq.create 1 (Ghost.reveal v)) `star` has_array_of_ref r (| a, Ghost.hide 1sz |))

inline_for_extraction [@@noextract_to "krml"]
let array_of_ref
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased t)
  (r: ref td)
: STT (array td)
    (pts_to r v)
    (fun a -> array_pts_to a (Seq.create 1 (Ghost.reveal v)) `star` has_array_of_ref r a)
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
: STGhostT (squash (Seq.length s == 1)) opened
    (array_pts_to a s `star` has_array_of_ref r a)
    (fun _ -> pts_to r (Seq.index s 0) `star` has_array_of_ref r a)
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
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r': ref td)
: STGhost unit opened
    (has_array_cell a i r')
    (fun _ -> has_array_cell a i r')
    (True)
    (fun _ -> SZ.v i < SZ.v (dsnd a))

val has_array_cell_has_base_array_cell
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
  (#ty: Type)
  (br: ref (base_array0 ty td (array_ref_base_size (array_ptr_of a))))
: STGhost (Ghost.erased SZ.t) opened
    (has_array_cell a i r)
    (fun j -> has_base_array_cell br j r)
    (has_array_ref_base (array_ptr_of a) br)
    (fun j ->
      SZ.v j == SZ.v (array_ref_offset (array_ptr_of a)) + SZ.v i
    )

val has_base_array_cell_has_array_cell
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
  (#ty: Type)
  (br: ref (base_array0 ty td (array_ref_base_size (array_ptr_of a))))
: STGhost (Ghost.erased SZ.t) opened
    (has_base_array_cell br i r)
    (fun j -> has_array_cell a j r)
    (has_array_ref_base (array_ptr_of a) br /\
      SZ.v i >= SZ.v (array_ref_offset (array_ptr_of a)) /\
      SZ.v i < SZ.v (array_ref_offset (array_ptr_of a)) + SZ.v (dsnd a)
    )
    (fun j ->
      SZ.v i == SZ.v (array_ref_offset (array_ptr_of a)) + SZ.v j
    )

val has_array_cell_inj
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r1 r2: ref td)
: STGhostT unit opened
    (
      has_array_cell a i r1 `star`
      has_array_cell a i r2
    )
    (fun _ ->
      has_array_cell a i r1 `star`
      has_array_cell a i r2 `star`
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
    (fun _ -> has_array_of_ref r a `star` has_array_cell a 0sz r)
*)

val ghost_array_cell_focus
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: STGhostT (squash (SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a))) opened
    (array_pts_to a s `star` has_array_cell a i r)
    (fun _ -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell a i r)

val ghost_array_cell
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: STGhost (r: Ghost.erased (ref td) { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) }) opened
    (array_pts_to a s)
    (fun r -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell a i r)
    (
      (SZ.v i < Seq.length s \/ SZ.v i < SZ.v (dsnd a))
    )
    (fun _ -> True)

[@@noextract_to "krml"] // primitive
val array_ref_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array_ref td)
  (len: array_len_t a)
  (i: SZ.t)
: ST (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v len })
    (array_pts_to (| a, len |) s)
    (fun r -> array_pts_to (| a, len |) (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell (| a, len |) i r)
    (
      (SZ.v i < Seq.length s \/ SZ.v i < SZ.v len)
    )
    (fun _ -> True)

inline_for_extraction [@@noextract_to "krml"]
let array_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: ST (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) })
    (array_pts_to a s)
    (fun r -> array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) `star` pts_to r (Seq.index s (SZ.v i)) `star` has_array_cell a i r)
    (
      (SZ.v i < Seq.length s \/ SZ.v i < SZ.v (dsnd a))
    )
    (fun _ -> True)
= let (| al, len |) = a in
  rewrite (array_pts_to _ _) (array_pts_to _ s);
  let r = array_ref_cell al len i in
  rewrite (array_pts_to _ _) (array_pts_to _ _);
  rewrite (has_array_cell _ _ _) (has_array_cell a i r);
  return r

val unarray_cell
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (#v: Ghost.erased t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
: STGhost (squash (SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a))) opened
    (array_pts_to a s `star` pts_to r v `star` has_array_cell a i r)
    (fun _ -> array_pts_to a (Seq.upd s (SZ.v i) v) `star` has_array_cell a i r)
    (
      (SZ.v i < Seq.length s ==> Seq.index s (SZ.v i) == unknown td)
    )
    (fun _ -> True)

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
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: STGhost (squash (SZ.v i <= SZ.v (dsnd a) /\ Seq.length s == SZ.v (dsnd a))) opened
    (array_pts_to a s)
    (fun _ -> array_pts_to (array_split_l a i) (Seq.slice s 0 (SZ.v i)) `star`
      array_pts_to (array_split_r a i) (Seq.slice s (SZ.v i) (Seq.length s)))
    (SZ.v i <= SZ.v (dsnd a) \/ SZ.v i <= Seq.length s)
    (fun _ -> True)

[@@noextract_to "krml"] // primitive
val array_ref_split
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (al: array_ref td)
  (len: array_len_t al)
  (i: SZ.t)
: ST (ar: array_ref td { SZ.v i <= SZ.v len /\ Seq.length s == SZ.v len})
    (array_pts_to (| al, len |) s)
    (fun _ -> array_pts_to (array_split_l (| al, len |) i) (Seq.slice s 0 (SZ.v i)) `star`
      array_pts_to (array_split_r (| al, len |) i) (Seq.slice s (SZ.v i) (Seq.length s)))
    (SZ.v i <= SZ.v len \/ SZ.v i <= Seq.length s)
    (fun ar -> ar == array_ptr_of (array_split_r (| al, len |) i))

inline_for_extraction [@@noextract_to "krml"]
let array_split
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
: ST (a': array td {SZ.v i <= SZ.v (dsnd a) /\ Seq.length s == SZ.v (dsnd a)})
    (array_pts_to a s)
    (fun a' -> array_pts_to (array_split_l a i) (Seq.slice s 0 (SZ.v i)) `star`
      array_pts_to a' (Seq.slice s (SZ.v i) (Seq.length s)))
    (SZ.v i <= SZ.v (dsnd a) \/ SZ.v i <= Seq.length s)
    (fun a' -> a' == array_split_r a i)
= let (| al, len |) = a in
  rewrite (array_pts_to _ _) (array_pts_to _ s);
  let ar = array_ref_split al len i in
  let a' = (| ar, Ghost.hide (len `SZ.sub` i) |) in
  rewrite (array_pts_to (array_split_l _ _) _) (array_pts_to (array_split_l a _) _);
  rewrite (array_pts_to (array_split_r _ _) _) (array_pts_to a' _);
  return a'

val array_join
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (#sl #sr: Ghost.erased (Seq.seq t))
  (a al ar: array td)
  (i: SZ.t)
: STGhost unit opened
    (array_pts_to al sl `star` array_pts_to ar sr)
    (fun _ -> array_pts_to a (sl `Seq.append` sr))
    (
      SZ.v i <= SZ.v (dsnd a) /\
      al == array_split_l a i /\
      ar == array_split_r a i
    )
    (fun _ -> True)

let fractionable_seq (#t: Type) (td: typedef t) (s: Seq.seq t) : GTot prop =
  forall (i: nat). i < Seq.length s ==> fractionable td (Seq.index s i)

let mk_fraction_seq (#t: Type) (td: typedef t) (s: Seq.seq t) (p: P.perm) : Ghost (Seq.seq t)
  (requires (fractionable_seq td s))
  (ensures (fun _ -> True))
= Seq.init_ghost (Seq.length s) (fun i -> mk_fraction td (Seq.index s i) p)

let mk_fraction_seq_full (#t: Type0) (td: typedef t) (x: Seq.seq t) : Lemma
  (requires (fractionable_seq td x))
  (ensures (mk_fraction_seq td x P.full_perm == x))
  [SMTPat (mk_fraction_seq td x P.full_perm)]
= assert (mk_fraction_seq td x P.full_perm `Seq.equal` x)

val mk_fraction_seq_split_gen
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: array td) (v: Seq.seq t { fractionable_seq td v }) (p p1 p2: P.perm)
: STGhost unit opened
  (array_pts_to r (mk_fraction_seq td v p))
  (fun _ -> array_pts_to r (mk_fraction_seq td v p1) `star` array_pts_to r (mk_fraction_seq td v p2))
  (p == p1 `P.sum_perm` p2 /\ (p `P.lesser_equal_perm` P.full_perm \/ Seq.length v == 0))
  (fun _ -> True)

let mk_fraction_seq_split
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: array td) (v: Ghost.erased (Seq.seq t) { fractionable_seq td v }) (p1 p2: P.perm)
: STGhost unit opened
  (array_pts_to r v)
  (fun _ -> array_pts_to r (mk_fraction_seq td v p1) `star` array_pts_to r (mk_fraction_seq td v p2))
  (P.full_perm == p1 `P.sum_perm` p2)
  (fun _ -> True)
= mk_fraction_seq_full td v;
  rewrite (array_pts_to _ _) (array_pts_to _ _);
  mk_fraction_seq_split_gen r v P.full_perm p1 p2

val mk_fraction_seq_join
  (#opened: _)
  (#t: Type) (#td: typedef t) (r: array td) (v: Seq.seq t { fractionable_seq td v }) (p1 p2: P.perm)
: STGhostT unit opened
  (array_pts_to r (mk_fraction_seq td v p1) `star` array_pts_to r (mk_fraction_seq td v p2))
  (fun _ -> array_pts_to r (mk_fraction_seq td v (p1 `P.sum_perm` p2)))

val array_fractional_permissions_theorem
  (#opened: _)
  (#t: Type)
  (#td: typedef t)
  (v1: Seq.seq t { fractionable_seq td v1 })
  (v2: Seq.seq t { fractionable_seq td v2 })
  (p1 p2: P.perm)
  (r: array td)
: STGhost unit opened
    (array_pts_to r (mk_fraction_seq td v1 p1) `star` array_pts_to r (mk_fraction_seq td v2 p2))
    (fun _ -> array_pts_to r (mk_fraction_seq td v1 p1) `star` array_pts_to r (mk_fraction_seq td v2 p2))
    (full_seq td v1 /\ full_seq td v2)
    (fun _ -> v1 == v2 /\ (array_length r > 0 ==> (p1 `P.sum_perm` p2) `P.lesser_equal_perm` P.full_perm))
