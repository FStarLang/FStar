(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi, and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Monotonic.HyperHeap
open FStar.Map
open FStar.Preorder
open FStar.Monotonic.Heap
module Map = FStar.Map
open FStar.Ghost

abstract type rid = erased (list (int * int))

let reveal (r:rid) : GTot (list (int * int)) = reveal r

abstract let color (x:rid): GTot int =
  match reveal x with
  | [] -> 0
  | (c, _)::_ -> c

type t = Map.t rid heap

let has_eq_rid (u:unit) :
  Lemma (requires True)
        (ensures hasEq rid)
  = ()

assume HasEq_rid: hasEq rid //TODO: we just proved this above, but we need to expose it as an argument-free SMT lemma, which isn't supported yet

(* AR: see issue#1262 *)
abstract let root :rid = let x:rid = hide [] in x

//is this SMTPat bad ?
val lemma_root_has_color_zero: r:rid{r == root}
                               -> Lemma (requires True) (ensures (color r = 0))
                                 [SMTPat (color r)]
let lemma_root_has_color_zero r = ()

//expose this so that no-one should assume otheriwse
let root_has_color_zero (u:unit) :Lemma (color root = 0) = ()

private let rid_tail (r:rid{Cons? (reveal r)}) :rid =
  elift1_p Cons?.tl r

private let rid_length (r:rid) :GTot nat = List.Tot.length (reveal r)

abstract val includes : r1:rid -> r2:rid -> GTot bool (decreases (reveal r2))
let rec includes r1 r2 =
  if r1=r2 then true
  else if rid_length r2 > rid_length r1
  then includes r1 (rid_tail r2)
  else false

let disjoint (i:rid) (j:rid) : GTot bool =
  not (includes i j) && not (includes j i)

private val lemma_aux: k:rid -> i:rid
      -> Lemma  (requires
                    rid_length k > 0
                    /\ rid_length k <= rid_length i
                    /\ includes k i
                    /\ not (includes (rid_tail k) i))
                 (ensures False)
                 (decreases (rid_length i))
let rec lemma_aux k i = lemma_aux k (rid_tail i)

abstract val lemma_disjoint_includes: i:rid -> j:rid -> k:rid ->
  Lemma (requires (disjoint i j /\ includes j k))
        (ensures (disjoint i k))
        (decreases (List.Tot.length (reveal k)))
        [SMTPat (disjoint i j);
         SMTPat (includes j k)]
let rec lemma_disjoint_includes i j k =
  if rid_length k <= rid_length j
  then ()
  else (lemma_disjoint_includes i j (rid_tail k);
        if rid_length i <= rid_length (rid_tail k)
        then ()
        else (if includes k i
              then lemma_aux k i
              else ()))

abstract val extends: rid -> rid -> GTot bool
let extends r0 r1 = Cons? (reveal r0) && rid_tail r0 = r1

abstract val parent: r:rid{r<>root} -> Tot rid
let parent r = rid_tail r

abstract val lemma_includes_refl: i:rid
                      -> Lemma (requires (True))
                               (ensures (includes i i))
                               [SMTPat (includes i i)]
let lemma_includes_refl i = ()

abstract val lemma_extends_includes: i:rid -> j:rid ->
  Lemma (requires (extends j i))
        (ensures (includes i j /\ not(includes j i)))
        [SMTPat (extends j i)]
let lemma_extends_includes i j = ()

let lemma_includes_anti_symmetric (i:rid) (j:rid) :
  Lemma (requires (includes i j /\ i <> j))
        (ensures (not (includes j i)))
        [SMTPat (includes i j)]
  = ()

abstract val lemma_extends_disjoint: i:rid -> j:rid -> k:rid ->
    Lemma (requires (extends j i /\ extends k i /\ j<>k))
          (ensures (disjoint j k))
let lemma_extends_disjoint i j k = ()

abstract val lemma_extends_parent: i:rid{i<>root} ->
  Lemma (requires True)
        (ensures (extends i (parent i)))
        [SMTPat (parent i)]
let lemma_extends_parent i = ()

abstract val lemma_extends_not_root: i:rid -> j:rid{extends j i} ->
  Lemma (requires True)
        (ensures (j<>root))
        [SMTPat (extends j i)]
let lemma_extends_not_root i j = ()

abstract val lemma_extends_only_parent: i:rid -> j:rid{extends j i} ->
  Lemma (requires True)
        (ensures (i = parent j))
        [SMTPat (extends j i)]
let lemma_extends_only_parent i j = ()

private let test0 = assert (includes (hide [(0, 1) ; (1, 0)]) (hide [(2, 2); (0, 1); (1, 0)]))
private let test1 (r1:rid) (r2:rid{includes r1 r2}) = assert (includes r1 (hide ((0,0)::(reveal r2))))


assume val mod_set : Set.set rid -> Tot (Set.set rid)
assume Mod_set_def: forall (x:rid) (s:Set.set rid). {:pattern Set.mem x (mod_set s)}
                    Set.mem x (mod_set s) <==> (exists (y:rid). Set.mem y s /\ includes y x)

let modifies (s:Set.set rid) (m0:t) (m1:t) =
  Map.equal m1 (Map.concat m1 (Map.restrict (Set.complement (mod_set s)) m0))
  /\ Set.subset (Map.domain m0) (Map.domain m1)

let modifies_just (s:Set.set rid) (m0:t) (m1:t) =
  Map.equal m1 (Map.concat m1 (Map.restrict (Set.complement s) m0))
  /\ Set.subset (Map.domain m0) (Map.domain m1)

let modifies_one (r:rid) (m0:t) (m1:t) =
  modifies_just (Set.singleton r) m0 m1

let equal_on (s:Set.set rid) (m0:t) (m1:t) =
 (forall (r:rid). {:pattern (Map.contains m0 r)} (Set.mem r (mod_set s) /\ Map.contains m0 r) ==> Map.contains m1 r)
 /\ Map.equal m1 (Map.concat m1 (Map.restrict (mod_set s) m0))

abstract val lemma_modifies_just_trans: m1:t -> m2:t -> m3:t
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies_just s1 m1 m2 /\ modifies_just s2 m2 m3))
                               (ensures (modifies_just (Set.union s1 s2) m1 m3))
let lemma_modifies_just_trans m1 m2 m3 s1 s2 = ()

abstract val lemma_modifies_trans: m1:t -> m2:t -> m3:t
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                               (ensures (modifies (Set.union s1 s2) m1 m3))
let lemma_modifies_trans m1 m2 m3 s1 s2 = ()

abstract val lemma_includes_trans: i:rid -> j:rid -> k:rid
                        -> Lemma (requires (includes i j /\ includes j k))
                                (ensures (includes i k))
				(decreases (reveal k))
                                [SMTPat (includes i j);
                                 SMTPat (includes j k)]
let rec lemma_includes_trans i j k =
  if j=k then ()
  else match reveal k with
        | hd::tl -> lemma_includes_trans i j (hide tl)

abstract val lemma_modset: i:rid -> j:rid
                  -> Lemma (requires (includes j i))
                           (ensures (Set.subset (mod_set (Set.singleton i)) (mod_set (Set.singleton j))))
let lemma_modset i j = ()

abstract val lemma_modifies_includes: m1:t -> m2:t
                       -> i:rid -> j:rid
                       -> Lemma (requires (modifies (Set.singleton i) m1 m2 /\ includes j i))
                                (ensures (modifies (Set.singleton j) m1 m2))
let lemma_modifies_includes m1 m2 i j = ()

abstract val lemma_modifies_includes2: m1:t -> m2:t
                       -> s1:Set.set rid -> s2:Set.set rid
                       -> Lemma (requires (modifies s1 m1 m2 /\ (forall x.  Set.mem x s1 ==> (exists y. Set.mem y s2 /\ includes y x))))
                                (ensures (modifies s2 m1 m2))
let lemma_modifies_includes2 m1 m2 s1 s2 = ()

abstract val lemma_disjoint_parents: pr:rid -> r:rid -> ps:rid -> s:rid -> Lemma
  (requires (r `extends` pr /\ s `extends` ps /\ disjoint pr ps))
  (ensures (disjoint r s))
  [SMTPat (extends r pr); SMTPat (extends s ps); SMTPat (disjoint pr ps)]
let lemma_disjoint_parents pr r ps s =
    assert (pr `includes` r);
    assert (ps `includes` s)

abstract val lemma_include_cons: i:rid -> j:rid -> Lemma
  (requires (i<>j /\ includes i j))
  (ensures (j<>root))
let lemma_include_cons i j = ()

let map_invariant (m:t) =
  forall r. Map.contains m r ==>
      (forall s. includes s r ==> Map.contains m s)

let disjoint_regions (s1:Set.set rid) (s2:Set.set rid) =
     forall x y. {:pattern (Set.mem x s1); (Set.mem y s2)} (Set.mem x s1 /\ Set.mem y s2) ==> disjoint x y

let extends_parent (tip:rid{tip<>root}) (r:rid)
  : Lemma (ensures (extends r (parent tip) /\ r<>tip ==> disjoint r tip \/ extends r tip))
          [SMTPat (extends r (parent tip))]
  = ()

let includes_child (tip:rid{tip<>root}) (r:rid)
  : Lemma (ensures (includes r tip ==> r=tip \/ includes r (parent tip)))
          [SMTPat (includes r (parent tip))]
  = ()

let root_is_root (s:rid)
  : Lemma (requires (includes s root))
          (ensures (s = root))
          [SMTPat (includes s root)]
  = ()

(*
* AR: we can prove this lemma only if both the mreferences have same preorder
*)

(*** Untyped views of references *)

(* Definition and ghost decidable equality *)

// abstract let aref (i: rid) : Type0 = Heap.aref

// abstract let as_heap_aref (#i:rid) (r:aref i) :Heap.aref = r

// abstract let heap_aref_as_aref (i:rid) (r:Heap.aref) :aref i = r

// let lemma_as_aref_injective (#i:rid) (r:aref i)
//   :Lemma (requires True)
//          (ensures  (heap_aref_as_aref i (as_heap_aref r) == r))
// 	 [SMTPat (as_heap_aref r)]
//   = ()

// abstract let dummy_aref (i: rid) : aref i = Heap.dummy_aref

// let aref_equal
//   (#i: rid)
//   (a1 a2: aref i)
// : Ghost bool
//   (requires True)
//   (ensures (fun b -> b == true <==> a1 == a2))
// = Heap.aref_equal (as_heap_aref a1) (as_heap_aref a2)

// (* Introduction rule *)

// let aref_of
//   (#i: rid)
//   (#a: Type)
//   (#rel: preorder a)
//   (r: mrref i a rel)
// : Tot (aref i)
// = Heap.aref_of (as_ref r)

// (* Operators lifted from rref *)

// let addr_of_aref
//   (#id:rid)
//   (r:aref id)
// : GTot nat
// = Heap.addr_of_aref (as_heap_aref r)

// let addr_of_aref_of
//   (#id:rid)
//   (#a: Type)
//   (#rel: preorder a)
//   (r: mrref id a rel)
// : Lemma
//   (addr_of r == addr_of_aref (aref_of r))
//   [SMTPat (addr_of_aref (aref_of r))]
// = Heap.addr_of_aref_of (as_ref r)

// let aref_is_mm
//   (#id: rid)
//   (r: aref id)
// : GTot bool
// = Heap.aref_is_mm (as_heap_aref r)

// let is_mm_aref_of
//   (#id: rid)
//   (#a: Type)
//   (#rel: preorder a)
//   (r: mrref id a rel)
// : Lemma
//   (is_mm r == aref_is_mm (aref_of r))
//   [SMTPat (aref_is_mm (aref_of r))]
// = Heap.is_mm_aref_of (as_ref r)

// let aref_unused_in
//   (#i: rid)
//   (r: aref i)
//   (m: t)
// : GTot Type0
// = not (Map.contains m i) \/
//   Heap.aref_unused_in (as_heap_aref r) (Map.sel m i)

// let unused_in_aref_of
//   (#i: rid)
//   (#a: Type)
//   (#rel: preorder a)
//   (r: mrref i a rel)
//   (m: t)
// : Lemma
//   (aref_unused_in (aref_of r) m <==> unused_in r m)
//   [SMTPat (aref_unused_in (aref_of r) m)]
// = Heap.unused_in_aref_of (as_ref r) (Map.sel m i)

// // abstract
// // val contains_ref_aref_unused_in: #i: rid -> #a:Type -> #rel: preorder a -> h:t -> x:mrref i a rel -> y:aref i -> Lemma
// //   (requires (contains_ref x h /\ aref_unused_in y h))
// //   (ensures  (addr_of x <> addr_of_aref y))
// // let contains_ref_aref_unused_in #i #a #rel h x y = Heap.contains_aref_unused_in (Map.sel h i) x y

// (* Elimination rule *)

// let aref_live_at (m: t) (#i: rid) (a: aref i) (v: Type) (rel: preorder v) : GTot Type0 =
//   Map.contains m i /\
//   Heap.aref_live_at (Map.sel m i) (as_heap_aref a) v rel

// let grref_of
//   (#i: rid)
//   (a: aref i)
//   (v: Type0)
//   (rel: preorder v)
// : Ghost (mrref i v rel)
//   (requires (exists m . aref_live_at m a v rel))
//   (ensures (fun x -> True))
// = Heap.gref_of (as_heap_aref a) v rel

// let rref_of
//   (m: t)
//   (#i: rid)
//   (a: aref i)
//   (v: Type)
//   (rel: preorder v)
// : Pure (mrref i v rel)
//   (requires (aref_live_at m a v rel))
//   (ensures (fun x -> aref_live_at m a v rel /\ addr_of x == addr_of_aref a /\ is_mm x == aref_is_mm a))
// = Heap.ref_of (Map.sel m i) (as_heap_aref a) v rel

// // abstract
// // let aref_live_at_aref_of
// //   (m: t)
// //   (#i: rid)
// //   (#v: Type0)
// //   (#rel: preorder v)
// //   (r: mrref i v rel)
// // : Lemma
// //   (ensures (aref_live_at m (aref_of r) v rel <==> contains_ref r m))
// //   [SMTPat (aref_live_at m (aref_of r) v rel)]
// // = ()

// // abstract
// // let contains_ref_grref_of
// //   (m: t)
// //   (#i: rid)
// //   (a: aref i)
// //   (v: Type0)
// //   (rel: preorder v)
// // : Lemma
// //   (requires (exists h' . aref_live_at h' a v rel))
// //   (ensures ((exists h' . aref_live_at h' a v rel) /\ (contains_ref (grref_of a v rel) m <==> aref_live_at m a v rel)))
// //   [SMTPatOr [
// //     [SMTPat (contains_ref (grref_of a v rel) m)];
// //     [SMTPat (aref_live_at m a v rel)];
// //   ]]
// // = ()

// let aref_of_grref_of
//   (#i: rid)
//   (a: aref i)
//   (v: Type0)
//   (rel: preorder v)
// : Lemma
//   (requires (exists h . aref_live_at h a v rel))
//   (ensures ((exists h. aref_live_at h a v rel) /\ aref_of (grref_of a v rel) == a))
//   [SMTPat (aref_of (grref_of a v rel))]
// = ()

// (* Operators lowered to rref *)

// let addr_of_grref_of
//   (#i: rid)
//   (a: aref i)
//   (t: Type0)
//   (rel: preorder t)
// : Lemma
//   (requires (exists h . aref_live_at h a t rel))
//   (ensures ((exists h . aref_live_at h a t rel) /\ addr_of (grref_of a t rel) == addr_of_aref a))
//   [SMTPat (addr_of (grref_of a t rel))]
// = ()

// let is_mm_grref_of
//   (#i: rid)
//   (a: aref i)
//   (t: Type0)
//   (rel: preorder t)
// : Lemma
//   (requires (exists h . aref_live_at h a t rel))
//   (ensures ((exists h . aref_live_at h a t rel) /\ is_mm (grref_of a t rel) == aref_is_mm a))
//   [SMTPat (is_mm (grref_of a t rel))]
// = ()

// let unused_in_gref_of
//   (#i: rid)
//   (a: aref i)
//   (v: Type0)
//   (rel: preorder v)
//   (h: t)
// : Lemma
//   (requires (exists h . aref_live_at h a v rel))
//   (ensures ((exists h . aref_live_at h a v rel) /\ (unused_in (grref_of a v rel) h <==> aref_unused_in a h)))
//   [SMTPat (unused_in (grref_of a v rel) h)]
// = ()

// let sel_rref_of
//   (#i: rid)
//   (a: aref i)
//   (v: Type0)
//   (rel: preorder v)
//   (h1 h2: t)
// : Lemma
//   (requires (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel))
//   (ensures (aref_live_at h2 a v rel /\ sel h1 (rref_of h2 a v rel) == sel h1 (grref_of a v rel)))
//   [SMTPat (sel h1 (rref_of h2 a v rel))]
// = ()

// let upd_rref_of
//   (#i: rid)
//   (a: aref i)
//   (v: Type0)
//   (rel: preorder v)
//   (h1 h2: t)
//   (x: v)
// : Lemma
//   (requires (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel))
//   (ensures (aref_live_at h2 a v rel /\ upd h1 (rref_of h2 a v rel) x == upd h1 (grref_of a v rel) x))
//   [SMTPat (upd h1 (rref_of h2 a v rel) x)]
// = ()

abstract let extend (r:rid) (n:int) (c:int)
  :Pure rid (requires True) (ensures (fun s -> s `extends` r /\ Cons? (reveal s) /\ Cons?.hd (reveal s) == (c, n) /\ color s == c))
  = elift1 (fun r -> (c, n)::r) r

abstract let extend_monochrome (r:rid) (n:int)
  : Pure rid (requires True) (ensures (fun s -> s `extends` r /\ Cons? (reveal s) /\ Cons?.hd (reveal s) == ((color r), n) /\ color s == color r))
= elift1 (fun r -> ((match r with | [] -> 0 | (c, _) :: _ -> c), n)::r) r


// abstract let alloc (#a:Type0) (rel:preorder a) (id:rid) (init:a) (mm:bool) (m:t{m `Map.contains` id})
//   :Tot (p:(mrref id a rel * t){let (r, h) = Heap.alloc rel (Map.sel m id) init mm in
//                                (as_ref (fst p) == r /\
//                                snd p == Map.upd m id h)})
//   = let (r, h) = Heap.alloc rel (Map.sel m id) init mm in
//     r, Map.upd m id h
