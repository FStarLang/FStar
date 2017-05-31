(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.HyperHeap
open FStar.Map
open FStar.Heap
open FStar

abstract let rid = list (int * int)

let reveal (r:rid) : GTot (list (int * int)) = r

abstract let color (x:rid): GTot int =
  match x with
  | [] -> 0
  | (c, _)::_ -> c

type t = Map.t rid heap

let has_eq_rid (u:unit) :
  Lemma (requires True)
        (ensures hasEq rid)
  = ()

assume HasEq_rid: hasEq rid //TODO: we just proved this above, but we need to expose it as an argument-free SMT lemma, which isn't supported yet

abstract let root : rid = []

//is this SMTPat bad ?
val lemma_root_has_color_zero: r:rid{r = root}
                               -> Lemma (requires (True)) (ensures (color r = 0))
                                 [SMTPat (color r)]
let lemma_root_has_color_zero r = ()

//expose this so that no-one should assume otheriwse
let root_has_color_zero (u:unit) :Lemma (color root = 0) = ()

abstract type rref (id:rid) (a:Type) = Heap.ref a

(* let has_eq_rref (id:rid) (a:Type) : *)
(*   Lemma (requires True) *)
(*         (ensures hasEq (rref id a)) *)
(*      [SMTPat (hasEq (rref id a))] *)
(*   = ()        *)

abstract val as_ref : #a:Type -> #id:rid -> r:rref id a -> Tot (ref a)
let as_ref #a #id r = r

val addr_of: #a:Type -> #id:rid -> r:rref id a -> GTot nat
let addr_of #a #id r = Heap.addr_of (as_ref r)

let is_mm (#a:Type) (#id:rid) (r:rref id a) :GTot bool
  = Heap.is_mm (as_ref r)

abstract val ref_as_rref : i:rid -> r:ref 'a -> GTot (rref i 'a)
let ref_as_rref i r = r

val lemma_as_ref_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires (True))
             (ensures ((ref_as_rref i (as_ref r) == r)))
       [SMTPat (as_ref r)]
let lemma_as_ref_inj #a #i r = ()

abstract val includes : rid -> rid -> GTot bool
let rec includes r1 r2 =
  if r1=r2 then true
  else if List.Tot.length r2 > List.Tot.length r1
  then includes r1 (Cons?.tl r2)
  else false

let disjoint (i:rid) (j:rid) : GTot bool =
  not (includes i j) && not (includes j i)

private val lemma_aux: k:rid -> i:rid
      -> Lemma  (requires
                    List.Tot.length k > 0
                    /\ List.Tot.length k <= List.Tot.length i
                    /\ includes k i
                    /\ not (includes (Cons?.tl k) i))
                 (ensures False)
                 (decreases (List.Tot.length i))
let rec lemma_aux k i = lemma_aux k (Cons?.tl i)

abstract val lemma_disjoint_includes: i:rid -> j:rid -> k:rid ->
  Lemma (requires (disjoint i j /\ includes j k))
        (ensures (disjoint i k))
        (decreases (List.Tot.length (reveal k)))
        [SMTPat (disjoint i j);
         SMTPat (includes j k)]
let rec lemma_disjoint_includes i j k =
  if List.Tot.length k <= List.Tot.length j
  then ()
  else (lemma_disjoint_includes i j (Cons?.tl k);
        if List.Tot.length i <= List.Tot.length (Cons?.tl k)
        then ()
        else (if includes k i
              then lemma_aux k i
              else ()))

abstract val extends: rid -> rid -> GTot bool
let extends r0 r1 = Cons? r0 && Cons?.tl r0 = r1

abstract val parent: r:rid{r<>root} -> Tot rid
let parent r = Cons?.tl r

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

private let test0 = assert (includes [(0, 1) ; (1, 0)] [(2, 2); (0, 1); (1, 0)])
private let test1 (r1:rid) (r2:rid{includes r1 r2}) = assert (includes r1 ((0,0)::r2))

let fresh_region (i:rid) (m0:t) (m1:t) =
 (forall j. includes i j ==> not (Map.contains m0 j))
 /\ Map.contains m1 i

let sel (#a:Type) (#i:rid) (m:t) (r:rref i a) : GTot a = Heap.sel (Map.sel m i) (as_ref r)
unfold let op_String_Access (#a:Type) (#i:rid) (m:t) (r:rref i a) = sel m r

let upd (#a:Type) (#i:rid) (m:t) (r:rref i a) (v:a) : GTot t = Map.upd m i (Heap.upd (Map.sel m i) (as_ref r) v)
unfold let op_String_Assignment (#a:Type) (#i:rid) (m:t) (r:rref i a) v = upd m r v


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
                                 [SMTPat (includes i j);
                                  SMTPat (includes j k)]
let rec lemma_includes_trans i j k =
  if j=k then ()
  else match k with
        | hd::tl -> lemma_includes_trans i j tl

abstract val lemma_modset: i:rid -> j:rid
                  -> Lemma (requires (includes j i))
                           (ensures (Set.subset (mod_set (Set.singleton i)) (mod_set (Set.singleton j))))
let lemma_modset i j = ()

abstract val lemma_modifies_includes: m1:t -> m2:t
                       -> i:rid -> j:rid
                       -> Lemma (requires (modifies (Set.singleton i) m1 m2 /\ includes j i))
                                (ensures (modifies (Set.singleton j) m1 m2))
let lemma_modifies_includes m1 m2 s1 s2 = ()

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

(* AR: using excluded_middle here, could make it GTot Type0 instead ? *)
let contains_ref (#a:Type) (#i:rid) (r:rref i a) (m:t) :GTot bool  =
  Map.contains m i && (FStar.StrongExcludedMiddle.strong_excluded_middle (Heap.contains (Map.sel m i) (as_ref r)))
  (* AR: in master this is the code *)
  (* Map.contains m i && Heap.contains (Map.sel m i) (as_ref r) *)

let unused_in (#a:Type) (#i:rid) (r:rref i a) (m:t) :GTot bool =
  not (Map.contains m i) ||
  FStar.StrongExcludedMiddle.strong_excluded_middle (Heap.unused_in (as_ref r) (Map.sel m i))

(*
 * AR: using this from HyperStack:weak_contains,
 * Map.contains covered by weak_live_region in HyperStack
 *)
let weak_contains_ref (#a:Type) (#i:rid) (r:rref i a) (m:t) : GTot bool =
  FStar.StrongExcludedMiddle.strong_excluded_middle (Heap.contains (Map.sel m i) (as_ref r))

let fresh_rref (#a:Type) (#i:rid) (r:rref i a) (m0:t) (m1:t) =
  Heap.unused_in (as_ref r) (Map.sel m0 i) /\
  Heap.contains (Map.sel m1 i) (as_ref r)

let modifies_rref (r:rid) (s:Set.set nat) h0 h1 =
  Heap.modifies s (Map.sel h0 r) (Map.sel h1 r)

abstract val lemma_include_cons: i:rid -> j:rid -> Lemma
  (requires (i<>j /\ includes i j))
  (ensures (j<>root))
let lemma_include_cons i j = ()

let map_invariant (m:t) =
  forall r. Map.contains m r ==>
      (forall s. includes s r ==> Map.contains m s)

abstract val lemma_extends_fresh_disjoint: i:rid -> j:rid -> ipar:rid -> jpar:rid
                               -> m0:t{map_invariant m0} -> m1:t{map_invariant m1} ->
  Lemma (requires (fresh_region i m0 m1
                  /\ fresh_region j m0 m1
                  /\ Map.contains m0 ipar
                  /\ Map.contains m0 jpar
                  /\ extends i ipar
                  /\ extends j jpar
                  /\ i<>j))
        (ensures (disjoint i j))
        [SMTPatT (fresh_region i m0 m1);
         SMTPatT (fresh_region j m0 m1);
         SMTPat (extends i ipar);
         SMTPat (extends j jpar)]
let lemma_extends_fresh_disjoint i j ipar jpar m0 m1 = ()

let disjoint_regions (s1:Set.set rid) (s2:Set.set rid) =
     forall x y. {:pattern (Set.mem x s1); (Set.mem y s2)} (Set.mem x s1 /\ Set.mem y s2) ==> disjoint x y

let extends_parent (tip:rid{tip<>root}) (r:rid)
  : Lemma (requires True)
          (extends r (parent tip) /\ r<>tip ==> disjoint r tip \/ extends r tip)
          [SMTPat (extends r (parent tip))]
  = ()

let includes_child (tip:rid{tip<>root}) (r:rid)
  : Lemma (requires True)
          (includes r tip ==> r=tip \/ includes r (parent tip))
          [SMTPat (includes r (parent tip))]
  = ()

let root_is_root (s:rid)
  : Lemma (requires (includes s root))
          (ensures (s = root))
          [SMTPat (includes s root)]
  = ()
