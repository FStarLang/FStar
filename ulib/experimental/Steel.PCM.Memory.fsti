(*
   Copyright 2019 Microsoft Research

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
module Steel.PCM.Memory
open FStar.Ghost
open Steel.PCM

/// Building up on `Steel.PCM.Heap`, this module adds memory invariants to the heap to expose the
/// final interface for Steel's PCM-based memory model.

(**** Basic memory properties *)

(** Abstract type of memories *)
val mem  : Type u#(a + 1)

(**
  The memory is built on top of the heap, adding on the memory invariants. However, some of the
  properties exposed for memories need only to talk about the underlying heap, putting aside
  the memory invariants. To avoid exposing the underlying heap in this abstract interface, we
  prefer to relying on this [core_mem] function that returns a new memory sharing the same
  heap with the original memory but without any of the memory invariants.
*)
val core_mem (m:mem u#a) : mem u#a

(** A predicate describing non-overlapping memories. Based on [Steel.PCM.Heap.disjoint] *)
val disjoint (m0 m1:mem u#h) : prop

(** Disjointness is symmetric *)
val disjoint_sym (m0 m1:mem u#h)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)
          [SMTPat (disjoint m0 m1)]

(** Disjoint memories can be combined. Based on [Steel.PCM.Heap.join] *)
val join (m0:mem u#h) (m1:mem u#h{disjoint m0 m1}) : mem u#h

(** Join is commutative *)
val join_commutative (m0 m1:mem)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      (disjoint_sym m0 m1;
       join m0 m1 == join m1 m0))

(** Disjointness distributes over join *)
val disjoint_join (m0 m1 m2:mem)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)

(** Join is associative *)
val join_associative (m0 m1 m2:mem)
  : Lemma
    (requires
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2))
    (ensures
      (disjoint_join m0 m1 m2;
       join m0 (join m1 m2) == join (join m0 m1) m2))

(**** Separation logic *)

(** The type of separation logic propositions. Based on Steel.PCM.Heap.slprop *)
[@@erasable]
val slprop : Type u#(a + 1)

(** Interpreting mem assertions as memory predicates *)
val interp (p:slprop u#a) (m:mem u#a) : prop

(** A common abbreviation: memories validating [p] *)
let hmem (p:slprop u#a) = m:mem u#a {interp p m}

(** Equivalence relation on slprops is just equivalence of their interpretations *)
let equiv (p1 p2:slprop) : prop =
  forall m. interp p1 m <==> interp p2 m

(** A memory maps a [ref]erence to its associated value *)
val ref (a:Type u#a) (pcm:pcm a) : Type u#0

(** All the standard connectives of separation logic, based on [Steel.PCM.Heap] *)
val emp : slprop u#a
val pure (p:prop) : slprop u#a
val pts_to (#a:Type u#a) (#pcm:_) (r:ref a pcm) (v:a) : slprop u#a
val h_and (p1 p2:slprop u#a) : slprop u#a
val h_or  (p1 p2:slprop u#a) : slprop u#a
val star  (p1 p2:slprop u#a) : slprop u#a
val wand  (p1 p2:slprop u#a) : slprop u#a
val h_exists (#a:Type u#b) (f: (a -> slprop u#a)) : slprop u#a
val h_forall (#a:Type u#b) (f: (a -> slprop u#a)) : slprop u#a

(***** Properties of separation logic equivalence *)

val equiv_symmetric (p1 p2:slprop)
  : squash (p1 `equiv` p2 ==> p2 `equiv` p1)

val equiv_extensional_on_star (p1 p2 p3:slprop)
  : squash (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))

val emp_unit (p:slprop)
  : Lemma (p `equiv` (p `star` emp))

val intro_emp (m:mem)
  : Lemma (interp emp m)

(** Equivalence of pure propositions is the equivalence of the underlying propositions *)
val pure_equiv (p q:prop)
  : Lemma ((p <==> q) ==> (pure p `equiv` pure q))

(** And the interpretation of pure propositions is their underlying propositions *)
val pure_interp (q:prop) (m:mem)
   : Lemma (interp (pure q) m <==> q)

(** A helper lemma for interpreting a pure proposition with another [slprop] *)
val pure_star_interp (p:slprop u#a) (q:prop) (m:mem)
   : Lemma (interp (p `star` pure q) m <==>
            interp (p `star` emp) m /\ q)

(***** Properties of [pts_to] *)

(** [ptr r] asserts that the reference [r] points to a value *)
let ptr (#a: Type u#a) (#pcm: pcm a) (r:ref a pcm) =
    h_exists (pts_to r)

(** Injectivity-like lemma for [pts_to], see [Steel.PCM.Heap] for more explanations *)
val pts_to_compatible
  (#a:Type u#a)
  (#pcm:pcm a)
  (x:ref a pcm)
  (v0 v1:a)
  (m:mem u#a)
    : Lemma
      (interp (pts_to x v0 `star` pts_to x v1) m <==>
       composable pcm v0 v1 /\ interp (pts_to x (op pcm v0 v1)) m)

val pts_to_compatible_equiv (#a:Type)
                            (#pcm:_)
                            (x:ref a pcm)
                            (v0:a)
                            (v1:a{composable pcm v0 v1})
  : Lemma (equiv (pts_to x v0 `star` pts_to x v1)
                 (pts_to x (op pcm v0 v1)))

(***** Properties of the separating conjunction *)

/// See [Steel.PCM.Memory.Heap] for more explanations

val intro_star (p q:slprop) (mp:hmem p) (mq:hmem q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))

val star_commutative (p1 p2:slprop)
  : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

val star_associative (p1 p2 p3:slprop)
  : Lemma ((p1 `star` (p2 `star` p3))
           `equiv`
           ((p1 `star` p2) `star` p3))

val star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))

val affine_star (p q:slprop) (m:mem)
  : Lemma ((interp (p `star` q) m ==> interp p m /\ interp q m))

(**** Memory invariants *)

module S = FStar.Set

(** Invariants have a name *)
val iname : eqtype

let inames = S.set iname

(** This proposition tells us that all the invariants names in [e] are valid in memory [m] *)
val inames_ok (e:inames) (m:mem) : prop

(** The empty set of invariants is always empty *)
val inames_ok_empty (m:mem)
  : Lemma (ensures inames_ok Set.empty m)
          [SMTPat (inames_ok Set.empty m)]

(**
  This separation logic proposition asserts that all the invariants whose names are in [e]
  are in effect and satisfied on the heap inside the memory [m]
*)
val locks_invariant (e:inames) (m:mem u#a) : slprop u#a

(** Memory refined with invariants and a footprint *)
let hmem_with_inv_except (e:inames) (fp:slprop u#a) =
  m:mem{inames_ok e m /\ interp (fp `star` locks_invariant e m) m}

(** Memory refined with just a footprint and no invariants  *)
let hmem_with_inv (fp:slprop u#a) = hmem_with_inv_except S.empty fp

/// The following lemmas are needed in `Steel.Effect`


(** Any separation logic proposition valid over [m] is also valid on [core_mem m] *)
val core_mem_interp (hp:slprop u#a) (m:mem u#a)
    : Lemma
      (requires interp hp m)
      (ensures interp hp (core_mem m))
      [SMTPat (interp hp (core_mem m))]

(** Interpretation is an affine heap proposition. See [Steel.PCM.Heap.interp_depends_only_on] *)
val interp_depends_only_on (hp:slprop u#a)
    : Lemma
      (forall (m0:hmem hp) (m1:mem u#a{disjoint m0 m1}).
        interp hp m0 <==> interp hp (join m0 m1))

(** This adds a SMT trigger to the [Steel.PCM.Heap.affine_star] lemma *)
let affine_star_smt (p q:slprop u#a) (m:mem u#a)
    : Lemma (interp (p `star` q) m ==> interp p m /\ interp q m)
      [SMTPat (interp (p `star` q) m)]
    = affine_star p q m

(** See [Steel.PCM.Heap.h_exists_cong] *)
val h_exists_cong (#a:Type) (p q : a -> slprop)
    : Lemma
      (requires (forall x. p x `equiv` q x))
      (ensures (h_exists p `equiv` h_exists q))

(**** Actions *)

/// Note, at this point, using the NMSTTotal effect constrains the mem to be
/// in universe 2, rather than being universe polymorphic

(** A memory predicate that depends only on fp *)
let mprop (fp:slprop u#a) =
  q:(mem u#a -> prop){
    forall (m0:mem{interp fp m0}) (m1:mem{disjoint m0 m1}).
      q m0 <==> q (join m0 m1)}

(**
  The preorder along wich the memory evolves with every update. See [Steel.PCM.Heap.heap_evolves]
*)
val mem_evolves : FStar.Preorder.preorder mem

(** See [Steel.PCM.Heap.is_frame_preserving]. We add in [lock_invariants] now *)
let preserves_frame (e:inames) (pre post:slprop) (m0 m1:mem) =
  forall (frame:slprop).
    interp ((pre `star` frame) `star` locks_invariant e m0) m0 ==>
    (interp ((post `star` frame) `star` locks_invariant e m1) m1 /\
     (forall (f_frame:mprop frame). f_frame (core_mem m0) == f_frame (core_mem m1)))

(**
  To guarantee that the memory always evolve according to frame-preserving updates,
  we encode it into the [MstTot] effect build on top of the non-deterministic state total
  effect NMSTATETOT. The effect is indexed by [except], which is the set of invariants that
  are currently opened.
*)
effect MstTot (a:Type u#a) (except:inames) (expects:slprop u#1) (provides: a -> slprop u#1) =
  NMSTTotal.NMSTATETOT a (mem u#1) mem_evolves
    (requires fun m0 ->
        inames_ok except m0 /\
        interp (expects `star` locks_invariant except m0) m0)
    (ensures fun m0 x m1 ->
        inames_ok except m1 /\
        interp (provides x `star` locks_invariant except m1) m1 /\
        preserves_frame except expects (provides x) m0 m1)

(** An action is just a thunked computation in [MstTot] *)
let action_except (a:Type u#a) (except:inames) (expects:slprop) (provides: a -> slprop) =
  unit -> MstTot a except expects provides

val sel_action (#a:Type u#1) (#pcm:_) (e:inames) (r:ref a pcm) (v0:erased a)
  : action_except (v:a{compatible pcm v0 v}) e (pts_to r v0) (fun _ -> pts_to r v0)

val upd_action (#a:Type u#1) (#pcm:_) (e:inames)
               (r:ref a pcm)
               (v0:FStar.Ghost.erased a)
               (v1:a {Steel.PCM.frame_preserving pcm v0 v1})
  : action_except unit e (pts_to r v0) (fun _ -> pts_to r v1)

val free_action (#a:Type u#1) (#pcm:pcm a) (e:inames)
                (r:ref a pcm) (x:FStar.Ghost.erased a{Steel.PCM.exclusive pcm x})
  : action_except unit e (pts_to r x) (fun _ -> pts_to r pcm.Steel.PCM.p.one)

(** Splitting a permission on a composite resource into two separate permissions *)
val split_action
  (#a:Type u#1)
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
  : action_except unit e (pts_to r (v0 `op pcm` v1)) (fun _ -> pts_to r v0 `star` pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val gather_action
  (#a:Type u#1)
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
  : action_except (_:unit{composable pcm v0 v1}) e (pts_to r v0 `star` pts_to r v1) (fun _ -> pts_to r (op pcm v0 v1))

val alloc_action (#a:Type u#1) (#pcm:pcm a) (e:inames) (x:a{compatible pcm x x})
  : action_except (ref a pcm) e emp (fun r -> pts_to r x)

(**** Invariants *)

(**
  This operator asserts that the logical content of invariant [i] is the separation logic
  predicate [p]
*)
val ( >--> ) (i:iname) (p:slprop u#1) : prop

(**[i : inv p] is an invariant whose content is [p] *)
let inv (p:slprop) = i:iname{i >--> p}

(** Creates a new invariant from a separation logic predicate [p] owned at the time of the call *)
val new_invariant (e:inames) (p:slprop)
  : action_except (inv p) e p (fun _ -> emp)

val with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#p:slprop)
                   (i:inv p{not (i `Set.mem` opened_invariants)})
                   (f:action_except a (Set.union (Set.singleton i) opened_invariants) (p `star` fp) (fun x -> p `star` fp' x))
  : action_except a opened_invariants fp fp'


val frame (#a:Type)
          (#opened_invariants:inames)
          (#pre:slprop)
          (#post:a -> slprop)
          (frame:slprop)
          ($f:action_except a opened_invariants pre post)
  : action_except a opened_invariants (pre `star` frame) (fun x -> post x `star` frame)

val change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem -> Lemma (requires interp p m) (ensures interp q m)))
  : action_except unit opened_invariants p (fun _ -> q)
