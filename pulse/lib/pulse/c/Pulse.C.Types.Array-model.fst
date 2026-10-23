module Pulse.C.Types.Array
#lang-pulse

(* Model implementation of Pulse.C.Types.Array: verified, but never extracted.
   A base array value is a sequence of cell values, with all typedef
   operations defined pointwise. Array pointers record a base size and an
   offset; array allocation always returns null, so points-to style
   predicates can be modeled as `pure False`. *)

open Pulse.Lib.Pervasives
friend Pulse.C.Types.Base
open Pulse.C.Types.Base
open Pulse.C.Typenat
module SZ = FStar.SizeT

let base_array_t t tn n = Seq.lseq t (SZ.v n)

let idx_conv (n: array_size_t) (p: nat -> prop)
: Lemma
  ((forall (i: nat) . i < SZ.v n ==> p i) <==> (forall (i: base_array_index_t n) . p (SZ.v i)))
= introduce (forall (i: base_array_index_t n) . p (SZ.v i)) ==> (forall (i: nat) . i < SZ.v n ==> p i)
  with introduce forall (i: nat) . i < SZ.v n ==> p i
  with introduce _ ==> _
  with (
    SZ.fits_lte i (SZ.v n);
    let j : base_array_index_t n = SZ.uint_to_t i in
    assert (p (SZ.v j))
  )

let ba_fractionable (#t: Type0) (td: typedef t) (n: array_size_t) (a: Seq.lseq t (SZ.v n)) : prop =
  forall (i: nat) . i < SZ.v n ==> td.td_fractionable (Seq.index a i)

let ba_full (#t: Type0) (td: typedef t) (n: array_size_t) (a: Seq.lseq t (SZ.v n)) : prop =
  forall (i: nat) . i < SZ.v n ==> td.td_full (Seq.index a i)

let ba_mk_fraction (#t: Type0) (td: typedef t) (n: array_size_t) (a: Seq.lseq t (SZ.v n)) (p: perm)
: Pure (Seq.lseq t (SZ.v n))
  (requires (ba_fractionable td n a))
  (ensures (fun y ->
    (forall (i: nat) . i < SZ.v n ==> Seq.index y i == td.td_mk_fraction (Seq.index a i) p) /\
    (p <=. 1.0R ==> ba_fractionable td n y)))
= let f (i: nat { i < SZ.v n }) : Tot t = td.td_mk_fraction (Seq.index a i) p in
  Seq.init_index (SZ.v n) f;
  Seq.init #t (SZ.v n) f

let ba_mk_fraction' (#t: Type0) (td: typedef t) (n: array_size_t) (a: Seq.lseq t (SZ.v n)) (p: perm)
: Pure (Seq.lseq t (SZ.v n))
  (requires (ba_fractionable td n a))
  (ensures (fun y -> p <=. 1.0R ==> ba_fractionable td n y))
= ba_mk_fraction td n a p

let ba_uninitialized (#t: Type0) (td: typedef t) (n: array_size_t)
: Tot (y: Seq.lseq t (SZ.v n) { ba_full td n y /\ ba_fractionable td n y })
= Seq.create (SZ.v n) td.td_uninitialized

let ba_unknown (#t: Type0) (td: typedef t) (n: array_size_t)
: Tot (y: Seq.lseq t (SZ.v n) { ba_fractionable td n y })
= Seq.create (SZ.v n) td.td_unknown

let ba_mk_fraction_full (#t: Type0) (td: typedef t) (n: array_size_t) (a: Seq.lseq t (SZ.v n))
: Lemma
  (requires (ba_fractionable td n a))
  (ensures (ba_mk_fraction' td n a 1.0R == a))
= let aux (i: nat { i < SZ.v n }) : Lemma (Seq.index (ba_mk_fraction td n a 1.0R) i == Seq.index a i) =
    td.td_mk_fraction_full (Seq.index a i)
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_elim (ba_mk_fraction td n a 1.0R) a

let ba_mk_fraction_compose (#t: Type0) (td: typedef t) (n: array_size_t) (a: Seq.lseq t (SZ.v n)) (p1 p2: perm)
: Lemma
  (requires (ba_fractionable td n a /\ p1 <=. 1.0R /\ p2 <=. 1.0R))
  (ensures (ba_mk_fraction' td n (ba_mk_fraction' td n a p1) p2 == ba_mk_fraction' td n a (p1 `prod_perm` p2)))
= let a1 = ba_mk_fraction td n a p1 in
  let a12 = ba_mk_fraction td n a1 p2 in
  let a' = ba_mk_fraction td n a (p1 `prod_perm` p2) in
  let aux (i: nat { i < SZ.v n }) : Lemma (Seq.index a12 i == Seq.index a' i) =
    td.td_mk_fraction_compose (Seq.index a i) p1 p2
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_elim a12 a'

let ba_full_not_unknown (#t: Type0) (td: typedef t) (n: array_size_t) (v: Seq.lseq t (SZ.v n))
: Lemma
  (requires (ba_full td n v))
  (ensures (~ (v == ba_unknown td n)))
= td.td_full_not_unknown (Seq.index v 0)

let ba_mk_fraction_unknown (#t: Type0) (td: typedef t) (n: array_size_t) (p: perm)
: Lemma (ba_mk_fraction' td n (ba_unknown td n) p == ba_unknown td n)
= td.td_mk_fraction_unknown p;
  Seq.lemma_eq_elim (ba_mk_fraction td n (ba_unknown td n) p) (ba_unknown td n)

let ba_mk_fraction_eq_unknown (#t: Type0) (td: typedef t) (n: array_size_t) (v: Seq.lseq t (SZ.v n)) (p: perm)
: Lemma
  (requires (ba_fractionable td n v /\ ba_mk_fraction' td n v p == ba_unknown td n))
  (ensures (v == ba_unknown td n))
= let aux (i: nat { i < SZ.v n }) : Lemma (Seq.index v i == td.td_unknown) =
    assert (Seq.index (ba_mk_fraction td n v p) i == Seq.index (ba_unknown td n) i);
    td.td_mk_fraction_eq_unknown (Seq.index v i) p
  in
  Classical.forall_intro aux;
  Seq.lemma_eq_elim v (ba_unknown td n)

let base_array0 #t tn td n = {
  td_fractionable = ba_fractionable td n;
  td_mk_fraction = ba_mk_fraction' td n;
  td_mk_fraction_full = ba_mk_fraction_full td n;
  td_mk_fraction_compose = ba_mk_fraction_compose td n;
  td_full = ba_full td n;
  td_uninitialized = ba_uninitialized td n;
  td_unknown = ba_unknown td n;
  td_full_not_unknown = ba_full_not_unknown td n;
  td_mk_fraction_unknown = ba_mk_fraction_unknown td n;
  td_mk_fraction_eq_unknown = ba_mk_fraction_eq_unknown td n;
}

let base_array_index #t #tn #n a i = Seq.index a (SZ.v i)

let base_array_eq #t #tn #n a1 a2 =
  idx_conv n (fun i -> i < SZ.v n /\ Seq.index #t a1 i == Seq.index a2 i);
  if FStar.IndefiniteDescription.strong_excluded_middle (a1 == a2)
  then ()
  else begin
    introduce (forall (i: nat) . i < SZ.v n ==> Seq.index a1 i == Seq.index a2 i) ==> a1 == a2
    with Seq.lemma_eq_elim a1 a2
  end;
  a1 == a2

let mk_base_array #t tn n v = v

let mk_base_array_index #t tn n v i = ()

let base_array_fractionable #t #tn #n a td =
  idx_conv n (fun i -> i < SZ.v n /\ td.td_fractionable (Seq.index #t a i))

let base_array_mk_fraction #t #tn #n a td p i = ()

let base_array_index_unknown #t tn n td i = ()

let base_array_index_uninitialized #t tn n td i = ()

let base_array_index_full #t #tn #n td x =
  idx_conv n (fun i -> i < SZ.v n /\ td.td_full (Seq.index #t x i))

let has_base_array_cell _ _ _ = pure False

ghost
fn has_base_array_cell_post
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
requires has_base_array_cell r i r'
ensures has_base_array_cell r i r' ** pure (SZ.v i < SZ.v n)
{
  unfold (has_base_array_cell r i r');
  unreachable ()
}

ghost
fn has_base_array_cell_dup
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
requires has_base_array_cell r i r'
ensures has_base_array_cell r i r' ** has_base_array_cell r i r'
{
  unfold (has_base_array_cell r i r');
  unreachable ()
}

ghost
fn has_base_array_cell_inj
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r1 r2: ref td)
requires has_base_array_cell r i r1 ** has_base_array_cell r i r2
ensures has_base_array_cell r i r1 ** has_base_array_cell r i r2 ** ref_equiv r1 r2
{
  unfold (has_base_array_cell r i r1);
  unreachable ()
}

ghost
fn has_base_array_cell_equiv_from
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r1 r2: ref (base_array0 tn td n))
  (i: SZ.t)
  (r': ref td)
requires has_base_array_cell r1 i r' ** ref_equiv r1 r2
ensures has_base_array_cell r2 i r' ** ref_equiv r1 r2
{
  unfold (has_base_array_cell r1 i r');
  unreachable ()
}

ghost
fn has_base_array_cell_equiv_to
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (r: ref (base_array0 tn td n))
  (i: SZ.t)
  (r1 r2: ref td)
requires has_base_array_cell r i r1 ** ref_equiv r1 r2
ensures has_base_array_cell r i r2 ** ref_equiv r1 r2
{
  unfold (has_base_array_cell r i r1);
  unreachable ()
}

noeq
type array_void_ptr0 : Type0 =
| ANull: array_void_ptr0
| APtr:
    (size: SZ.t { SZ.v size > 0 }) ->
    (offset: SZ.t { SZ.v offset <= SZ.v size }) ->
    array_void_ptr0

let array_void_ptr = array_void_ptr0

let null_array_void_ptr = ANull

let g_array_ptr_is_null #t #td a = ANull? (a <: array_void_ptr0)

let array_ref_base_size #t #td a =
  match (a <: array_void_ptr0) with
  | ANull -> 0sz
  | APtr size _ -> size

let has_array_ref_base _ _ = False

let has_array_ref_base_inj _ _ _ = ()

let array_ref_offset #t #td a =
  match (a <: array_void_ptr0) with
  | ANull -> 0sz
  | APtr _ offset -> offset

let array_ref_base_offset_inj _ _ _ _ = ()

let array_pts_to _ _ = pure False

fn array_ptr_is_null
  (#t: Type)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: array_ptr td)
  (len: array_len_t r)
requires array_pts_to_or_null (mk_array_or_null r len) v
returns b: bool
ensures array_pts_to_or_null (mk_array_or_null r len) v ** pure (
      b == g_array_is_null (mk_array_or_null r len)
    )
{
  let r' : array_void_ptr0 = r;
  ANull? r'
}

ghost
fn array_pts_to_length
  (#t: Type)
  (#td: typedef t)
  (r: array td)
  (v: Ghost.erased (Seq.seq t))
requires array_pts_to r v
ensures array_pts_to r v ** pure (Seq.length v == SZ.v (dsnd r))
{
  unfold (array_pts_to r v);
  unreachable ()
}

ghost
fn ghost_array_of_base_focus
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
  (a: array td)
requires pts_to r v ** pure (has_array_of_base r a)
ensures array_pts_to a (seq_of_base_array v)
{
  unfold (pts_to r v);
  unreachable ()
}

ghost
fn ghost_array_of_base
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
requires pts_to r v
returns a: (a: Ghost.erased (array td) { has_array_of_base r a })
ensures array_pts_to a (seq_of_base_array v)
{
  unfold (pts_to r v);
  unreachable ()
}

fn array_ref_of_base
  (#t: Type)
  (#tn: Type0)
  (#n: Ghost.erased array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (base_array_t t tn n))
  (r: ref (base_array0 tn td n))
requires pts_to r v
returns a: array_ref td
ensures exists* (ar: array td) .
      array_pts_to ar (seq_of_base_array v) ** pure (
      array_ref_of_base_post v r a ar
    )
{
  unfold (pts_to r v);
  unreachable ()
}

ghost
fn unarray_of_base
  (#t: Type)
  (#tn: Type0)
  (#n: array_size_t)
  (#td: typedef t)
  (#v: Ghost.erased (Seq.seq t))
  (r: ref (base_array0 tn td n))
  (a: array td)
requires array_pts_to a v ** pure (has_array_of_base r a)
returns v': Ghost.erased (base_array_t t tn n)
ensures pts_to r v' ** pure (Ghost.reveal v `Seq.equal` seq_of_base_array v')
{
  unfold (array_pts_to a v);
  unreachable ()
}

let freeable_array _ = emp

fn array_ptr_alloc
  (#t: Type)
  (td: typedef t)
  (sz: SZ.t { SZ.v sz > 0 })
requires emp
returns a: array_ptr td
ensures exists* (ar: array_or_null td) (s: Seq.seq t) .
      freeable_or_null_array ar **
      array_pts_to_or_null ar s ** pure (
      array_ptr_of ar == a /\
      (g_array_is_null ar == false ==> array_length ar == SZ.v sz) /\
      Ghost.reveal s `Seq.equal` FStar.Seq.create (SZ.v sz) (uninitialized td)
    )
{
  let a : array_ptr td = null_array_ptr td;
  let ar : array_or_null td = mk_array_or_null a (Ghost.hide 0sz);
  let s : Ghost.erased (Seq.seq t) = Ghost.hide (Seq.create (SZ.v sz) (uninitialized td));
  rewrite emp as (freeable_or_null_array ar);
  rewrite emp as (array_pts_to_or_null ar s);
  a
}

fn array_ref_free
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array_ref td)
  (n: array_len_t a)
requires freeable_array (mk_array a n) ** array_pts_to (mk_array a n) s ** pure (full_seq td s)
ensures emp
{
  unfold (array_pts_to (mk_array a n) s);
  unreachable ()
}

let has_array_cell _ _ _ = pure False

ghost
fn has_array_cell_post
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r': ref td)
requires has_array_cell a i r'
ensures has_array_cell a i r' ** pure (SZ.v i < SZ.v (dsnd a))
{
  unfold (has_array_cell a i r');
  unreachable ()
}

ghost
fn has_array_cell_has_base_array_cell
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
  (#ty: Type)
  (br: ref (base_array0 ty td (array_ref_base_size (array_ptr_of a))))
requires has_array_cell a i r ** pure (has_array_ref_base (array_ptr_of a) br)
returns j: Ghost.erased SZ.t
ensures has_base_array_cell br j r ** pure (
      SZ.v j == SZ.v (array_ref_offset (array_ptr_of a)) + SZ.v i
    )
{
  unfold (has_array_cell a i r);
  unreachable ()
}

ghost
fn has_base_array_cell_has_array_cell
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
  (#ty: Type)
  (br: ref (base_array0 ty td (array_ref_base_size (array_ptr_of a))))
requires has_base_array_cell br i r ** pure (
      has_array_ref_base (array_ptr_of a) br /\
      SZ.v i >= SZ.v (array_ref_offset (array_ptr_of a)) /\
      SZ.v i < SZ.v (array_ref_offset (array_ptr_of a)) + SZ.v (dsnd a)
    )
returns j: Ghost.erased SZ.t
ensures has_array_cell a j r ** pure (
      SZ.v i == SZ.v (array_ref_offset (array_ptr_of a)) + SZ.v j
    )
{
  unfold (has_base_array_cell br i r);
  unreachable ()
}

ghost
fn has_array_cell_inj
  (#t: Type)
  (#td: typedef t)
  (a: array td)
  (i: SZ.t)
  (r1 r2: ref td)
requires has_array_cell a i r1 ** has_array_cell a i r2
ensures has_array_cell a i r1 ** has_array_cell a i r2 ** ref_equiv r1 r2
{
  unfold (has_array_cell a i r1);
  unreachable ()
}

ghost
fn ghost_array_cell_focus
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
  (r: ref td)
requires array_pts_to a s ** has_array_cell a i r
returns _: squash (SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a))
ensures array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) ** pts_to r (Seq.index s (SZ.v i)) ** has_array_cell a i r
{
  unfold (array_pts_to a s);
  unreachable ()
}

ghost
fn ghost_array_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
requires array_pts_to a s ** pure (SZ.v i < Seq.length s \/ SZ.v i < SZ.v (dsnd a))
returns r: (r: Ghost.erased (ref td) { SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a) })
ensures array_pts_to a (Seq.upd s (SZ.v i) (unknown td)) ** pts_to r (Seq.index s (SZ.v i)) ** has_array_cell a i r
{
  unfold (array_pts_to a s);
  unreachable ()
}

fn array_ref_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array_ref td)
  (len: array_len_t a)
  (i: SZ.t)
requires array_pts_to (mk_array a len) s ** pure (SZ.v i < Seq.length s \/ SZ.v i < SZ.v len)
returns r: (r: ref td { SZ.v i < Seq.length s /\ Seq.length s == SZ.v len })
ensures array_pts_to (mk_array a len) (Seq.upd s (SZ.v i) (unknown td)) ** pts_to r (Seq.index s (SZ.v i)) ** has_array_cell (mk_array a len) i r
{
  unfold (array_pts_to (mk_array a len) s);
  unreachable ()
}

ghost
fn unarray_cell
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (#v: Ghost.erased t)
  (a: array td)
  (i: SZ.t)
  (r: ref td)
requires array_pts_to a s ** pts_to r v ** has_array_cell a i r ** pure (
      SZ.v i < Seq.length s ==> Seq.index s (SZ.v i) == unknown td
    )
returns _: squash (SZ.v i < Seq.length s /\ Seq.length s == SZ.v (dsnd a))
ensures array_pts_to a (Seq.upd s (SZ.v i) v) ** has_array_cell a i r
{
  unfold (array_pts_to a s);
  unreachable ()
}

let array_ref_shift #t #td a i =
  let APtr size offset = (a <: array_void_ptr0) in
  SZ.fits_lte (SZ.v offset + SZ.v i) (SZ.v size);
  APtr size (offset `SZ.add` i)

let array_ref_shift_zero #t #td a = ()

let array_ref_shift_assoc #t #td a i1 i2 =
  let APtr size _ = (a <: array_void_ptr0) in
  SZ.fits_lte (SZ.v i1 + SZ.v i2) (SZ.v size)

ghost
fn ghost_array_split
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (a: array td)
  (i: SZ.t)
requires array_pts_to a s ** pure (SZ.v i <= SZ.v (dsnd a) \/ SZ.v i <= Seq.length s)
returns _: squash (SZ.v i <= SZ.v (dsnd a) /\ Seq.length s == SZ.v (dsnd a))
ensures array_pts_to (array_split_l a i) (Seq.slice s 0 (SZ.v i)) **
      array_pts_to (array_split_r a i) (Seq.slice s (SZ.v i) (Seq.length s))
{
  unfold (array_pts_to a s);
  unreachable ()
}

fn array_ref_split
  (#t: Type)
  (#td: typedef t)
  (#s: Ghost.erased (Seq.seq t))
  (al: array_ref td)
  (len: array_len_t al)
  (i: SZ.t { SZ.v i <= SZ.v len })
requires array_pts_to (mk_array al len) s
returns ar: array_ref td
ensures exists* sl sr .
      array_pts_to (array_split_l (mk_array al len) i) sl **
      array_pts_to (array_split_r (mk_array al len) i) sr **
      pure (
        array_ref_split_post s (mk_array al len) i sl sr /\
        SZ.v i <= SZ.v len /\ SZ.v i <= Seq.length s /\
        ar == array_ptr_of (array_split_r (mk_array al len) i)
    )
{
  unfold (array_pts_to (mk_array al len) s);
  unreachable ()
}

ghost
fn array_join
  (#t: Type)
  (#td: typedef t)
  (#sl #sr: Ghost.erased (Seq.seq t))
  (a al ar: array td)
  (i: SZ.t)
requires array_pts_to al sl ** array_pts_to ar sr ** pure (
      SZ.v i <= SZ.v (dsnd a) /\
      al == array_split_l a i /\
      ar == array_split_r a i
    )
ensures array_pts_to a (sl `Seq.append` sr)
{
  unfold (array_pts_to al sl);
  unreachable ()
}

ghost
fn mk_fraction_seq_split_gen
  (#t: Type) (#td: typedef t) (r: array td) (v: Seq.seq t { fractionable_seq td v }) (p p1 p2: perm)
requires array_pts_to r (mk_fraction_seq td v p) ** pure (
    p == p1 +. p2 /\ (p <=. 1.0R \/ Seq.length v == 0)
  )
ensures array_pts_to r (mk_fraction_seq td v p1) ** array_pts_to r (mk_fraction_seq td v p2)
{
  unfold (array_pts_to r (mk_fraction_seq td v p));
  unreachable ()
}

ghost
fn mk_fraction_seq_split
  (#t: Type) (#td: typedef t) (r: array td) (v: Ghost.erased (Seq.seq t) { fractionable_seq td v }) (p1 p2: perm)
requires array_pts_to r v ** pure (1.0R == p1 +. p2)
ensures array_pts_to r (mk_fraction_seq td v p1) ** array_pts_to r (mk_fraction_seq td v p2)
{
  unfold (array_pts_to r v);
  unreachable ()
}

ghost
fn mk_fraction_seq_join
  (#t: Type) (#td: typedef t) (r: array td) (v: Seq.seq t { fractionable_seq td v }) (p1 p2: perm)
requires array_pts_to r (mk_fraction_seq td v p1) ** array_pts_to r (mk_fraction_seq td v p2)
ensures array_pts_to r (mk_fraction_seq td v (p1 +. p2))
{
  unfold (array_pts_to r (mk_fraction_seq td v p1));
  unreachable ()
}

ghost
fn array_fractional_permissions_theorem
  (#t: Type)
  (#td: typedef t)
  (v1: Seq.seq t { fractionable_seq td v1 })
  (v2: Seq.seq t { fractionable_seq td v2 })
  (p1 p2: perm)
  (r: array td)
requires array_pts_to r (mk_fraction_seq td v1 p1) ** array_pts_to r (mk_fraction_seq td v2 p2) ** pure (
      full_seq td v1 /\ full_seq td v2
    )
ensures array_pts_to r (mk_fraction_seq td v1 p1) ** array_pts_to r (mk_fraction_seq td v2 p2) ** pure (
      v1 == v2 /\ (array_length r > 0 ==> (p1 +. p2) <=. 1.0R)
    )
{
  unfold (array_pts_to r (mk_fraction_seq td v1 p1));
  unreachable ()
}

fn array_blit_ptr
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
requires array_pts_to (mk_array src_ptr src_len) (mk_fraction_seq td v_src p_src) ** array_pts_to (mk_array dst_ptr dst_len) v_dst ** pure (
        SZ.v idx_src + SZ.v len <= SZ.v src_len /\
        SZ.v idx_dst + SZ.v len <= SZ.v dst_len
    )
returns v_dst': Ghost.erased (Seq.seq t)
ensures array_pts_to (mk_array src_ptr src_len) (mk_fraction_seq td v_src p_src) **
      array_pts_to (mk_array dst_ptr dst_len) v_dst' ** pure (
        array_blit_post v_src v_dst (mk_array src_ptr src_len) idx_src (mk_array dst_ptr dst_len) idx_dst len v_dst'
    )
{
  unfold (array_pts_to (mk_array dst_ptr dst_len) v_dst);
  unreachable ()
}
