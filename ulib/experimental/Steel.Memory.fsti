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
module Steel.Memory
open FStar.Ghost
open FStar.PCM

/// Building up on `Steel.Heap`, this module adds memory invariants to the heap to expose the
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

val core_mem_invol (m: mem u#a) : Lemma
  (core_mem (core_mem m) == core_mem m)
  [SMTPat (core_mem (core_mem m))]

(** A predicate describing non-overlapping memories. Based on [Steel.Heap.disjoint] *)
val disjoint (m0 m1:mem u#h) : prop

(** Disjointness is symmetric *)
val disjoint_sym (m0 m1:mem u#h)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)
          [SMTPat (disjoint m0 m1)]

(** Disjoint memories can be combined. Based on [Steel.Heap.join] *)
val join (m0:mem u#h) (m1:mem u#h{disjoint m0 m1}) : mem u#h

(** Join is commutative *)
val join_commutative (m0 m1:mem)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      (disjoint m0 m1 /\
       disjoint m1 m0 /\
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

(** The type of separation logic propositions. Based on Steel.Heap.slprop *)
[@@erasable]
val slprop : Type u#(a + 1)

(** Interpreting mem assertions as memory predicates *)
val interp (p:slprop u#a) (m:mem u#a) : prop

(** A common abbreviation: memories validating [p] *)
let hmem (p:slprop u#a) = m:mem u#a {interp p m}

(** Equivalence relation on slprops is just equivalence of their interpretations *)
val equiv (p1 p2:slprop u#a) : prop

(**
  An extensional equivalence principle for slprop
 *)
val slprop_extensionality (p q:slprop)
  : Lemma
    (requires p `equiv` q)
    (ensures p == q)

val reveal_equiv (p1 p2:slprop u#a) : Lemma
  (ensures (forall m. interp p1 m <==> interp p2 m) <==> p1 `equiv` p2)
  [SMTPat (p1 `equiv` p2)]

(** Implication of slprops *)
let slimp (p1 p2 : slprop) : prop =
  forall m. interp p1 m ==> interp p2 m

(** A memory maps a [ref]erence to its associated value *)
val core_ref : Type u#0

let ref (a:Type u#a) (pcm:pcm a) : Type u#0 = core_ref

(** [null] is a specific reference, that is not associated to any value
*)
val core_ref_null : core_ref

(** [null] is a specific reference, that is not associated to any value
*)
let null (#a:Type u#a) (#pcm:pcm a) : ref a pcm = core_ref_null

val core_ref_is_null (r:core_ref) : b:bool { b <==> r == core_ref_null }

(** Checking whether [r] is the null pointer is decidable through [is_null]
*)
let is_null (#a:Type u#a) (#pcm:pcm a) (r:ref a pcm) : (b:bool{b <==> r == null}) = core_ref_is_null r

(** All the standard connectives of separation logic, based on [Steel.Heap] *)
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

(** Injectivity-like lemma for [pts_to], see [Steel.Heap] for more explanations *)
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

val pts_to_not_null (#a:Type u#a)
                    (#pcm:_)
                    (x:ref a pcm)
                    (v:a)
                    (m:mem u#a)
  : Lemma (requires interp (pts_to x v) m)
          (ensures x =!= null)

(***** Properties of the separating conjunction *)

/// See [Steel.Memory.Heap] for more explanations

val intro_star (p q:slprop) (mp:hmem p) (mq:hmem q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))

val elim_star (p q:slprop) (m:hmem (p `star` q))
  : Lemma
    (requires
      interp (p `star` q) m)
    (ensures exists ml mr.
      disjoint ml mr /\ m == join ml mr /\ interp p ml /\ interp q mr)

val interp_star
  (p q: slprop)
  (m: mem)
: Lemma
  (interp (p `star` q) m <==> (exists (mp: mem) (mq: mem) . disjoint mp mq /\ interp p mp /\ interp q mq /\ join mp mq == m))

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

let inames = erased (S.set iname)

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

val full_mem_pred: mem -> prop
let full_mem = m:mem{full_mem_pred m}

(** Memory refined with invariants and a footprint *)
let hmem_with_inv_except (e:inames) (fp:slprop u#a) =
  m:full_mem{inames_ok e m /\ interp (fp `star` locks_invariant e m) m}

(** Memory refined with just a footprint and no invariants  *)
let hmem_with_inv (fp:slprop u#a) = hmem_with_inv_except S.empty fp

/// The following lemmas are needed in `Steel.Effect`


(** Any separation logic proposition valid over [m] is also valid on [core_mem m] *)
val core_mem_interp (hp:slprop u#a) (m:mem u#a)
    : Lemma
      (requires True)
      (ensures (interp hp (core_mem m) <==> interp hp m))
      [SMTPat (interp hp (core_mem m))]

(** Interpretation is an affine heap proposition. See [Steel.Heap.interp_depends_only_on] *)
val interp_depends_only_on (hp:slprop u#a)
    : Lemma
      (forall (m0:hmem hp) (m1:mem u#a{disjoint m0 m1}).
        interp hp m0 <==> interp hp (join m0 m1))

(** This adds a SMT trigger to the [Steel.Heap.affine_star] lemma *)
let affine_star_smt (p q:slprop u#a) (m:mem u#a)
    : Lemma (interp (p `star` q) m ==> interp p m /\ interp q m)
      [SMTPat (interp (p `star` q) m)]
    = affine_star p q m

let mem_prop_is_affine
  (sl: slprop u#a)
  (f: (hmem sl -> Tot prop))
: Tot prop
= (forall m . f m <==> f (core_mem m)) /\
  (forall (m0: hmem sl) m1 . (disjoint m0 m1 /\ interp sl (join m0 m1)) ==> (f m0 <==> f (join m0 m1)))

let a_mem_prop (sl: slprop u#a) : Type u#(a+1) = (f: (hmem sl -> Tot prop) { mem_prop_is_affine sl f })

val refine_slprop
  (sl: slprop u#a)
  (f: a_mem_prop sl)
: Tot (slprop u#a)

val interp_refine_slprop
  (sl: slprop u#a)
  (f: a_mem_prop sl)
  (m: mem u#a)
: Lemma
  (interp (refine_slprop sl f) m <==> (interp sl m /\ f m))
  [SMTPat (interp (refine_slprop sl f) m)]

val sdep
  (s: slprop u#a)
  (f: (hmem s -> Tot (slprop u#a)))
: Tot (slprop u#a)

let dep_slprop_is_affine
  (s: slprop)
  (f: (hmem s -> Tot slprop))
: Tot prop
= (forall (h: hmem s) . f h `equiv`  f (core_mem h))

val interp_sdep
  (s: slprop)
  (f: (hmem s -> Tot slprop))
  (m: mem)
: Lemma
  (requires (dep_slprop_is_affine s f))
  (ensures (
    interp (sdep s f) m <==> (exists m1 m2 . interp s m1 /\ interp (f m1) m2 /\ disjoint m1 m2 /\ join m1 m2 == m)
  ))
  [SMTPat (interp (sdep s f) m)]

(** See [Steel.Heap.h_exists_cong] *)
val h_exists_cong (#a:Type) (p q : a -> slprop)
    : Lemma
      (requires (forall x. p x `equiv` q x))
      (ensures (h_exists p `equiv` h_exists q))

(** Introducing [h_exists] by presenting a witness *)
val intro_h_exists (#a:_) (x:a) (p:a -> slprop) (m:mem)
  : Lemma (interp (p x) m ==> interp (h_exists p) m)

val elim_h_exists (#a:_) (p:a -> slprop) (m:mem)
  : Lemma (interp (h_exists p) m ==> (exists x. interp (p x) m))

(**** Actions *)

/// Note, at this point, using the NMSTTotal effect constrains the mem to be
/// in universe 2, rather than being universe polymorphic

(** A memory predicate that depends only on fp *)
let mprop (fp:slprop u#a) =
  q:(mem u#a -> prop){
    forall (m0:mem{interp fp m0}) (m1:mem{disjoint m0 m1}).
      q m0 <==> q (join m0 m1)}

let mprop2 (#a:Type u#b) (fp_pre:slprop u#a) (fp_post:a -> slprop u#a) =
  q:(mem u#a -> a -> mem u#a -> prop){
    // can join any disjoint mem to the pre-mem and q is still valid
    (forall (x:a) (m0:mem{interp fp_pre m0}) (m_post:mem{interp (fp_post x) m_post}) (m1:mem{disjoint m0 m1}).
      q m0 x m_post <==> q (join m0 m1) x m_post) /\
    // can join any mem to the post-mem and q is still valid
    (forall (x:a) (m_pre:mem{interp fp_pre m_pre}) (m0:mem{interp (fp_post x) m0}) (m1:mem{disjoint m0 m1}).
      q m_pre x m0 <==> q m_pre x (join m0 m1))}

(**
  The preorder along which the memory evolves with every update. See [Steel.Heap.heap_evolves]
*)
val mem_evolves : FStar.Preorder.preorder full_mem

(**
  To guarantee that the memory always evolve according to frame-preserving updates,
  we encode it into the [MstTot] effect build on top of the non-deterministic state total
  effect NMSTATETOT. The effect is indexed by [except], which is the set of invariants that
  are currently opened.
*)
effect MstTot
  (a:Type u#a)
  (except:inames)
  (expects:slprop u#1)
  (provides: a -> slprop u#1)
  (frame:slprop u#1)
  (pre:mprop expects)
  (post:mprop2 expects provides)
  = NMSTTotal.NMSTATETOT a (full_mem u#1) mem_evolves
    (requires fun m0 ->
        inames_ok except m0 /\
        interp (expects `star` frame `star` locks_invariant except m0) m0 /\
        pre (core_mem m0))
    (ensures fun m0 x m1 ->
        inames_ok except m1 /\
        interp (expects `star` frame `star` locks_invariant except m0) m0 /\  //TODO: fix the effect so as not to repeat this
        interp (provides x `star` frame `star` locks_invariant except m1) m1 /\
        post (core_mem m0) x (core_mem m1) /\
        (forall (f_frame:mprop frame). f_frame (core_mem m0) == f_frame (core_mem m1)))

(** An action is just a thunked computation in [MstTot] that takes a frame as argument *)
let action_except (a:Type u#a) (except:inames) (expects:slprop) (provides: a -> slprop) =
  frame:slprop -> MstTot a except expects provides frame (fun _ -> True) (fun _ _ _ -> True)

let action_except_full (a:Type u#a)
  (except:inames)
  (expects:slprop)
  (provides: a -> slprop)
  (req:mprop expects)
  (ens:mprop2 expects provides)
= frame:slprop -> MstTot a except expects provides frame req ens

val sel_action (#a:Type u#1) (#pcm:_) (e:inames) (r:ref a pcm) (v0:erased a)
  : action_except (v:a{compatible pcm v0 v}) e (pts_to r v0) (fun _ -> pts_to r v0)

val upd_action (#a:Type u#1) (#pcm:_) (e:inames)
               (r:ref a pcm)
               (v0:FStar.Ghost.erased a)
               (v1:a {FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.refine v1})
  : action_except unit e (pts_to r v0) (fun _ -> pts_to r v1)

val free_action (#a:Type u#1) (#pcm:pcm a) (e:inames)
                (r:ref a pcm) (x:FStar.Ghost.erased a{FStar.PCM.exclusive pcm x /\ pcm.refine pcm.FStar.PCM.p.one})
  : action_except unit e (pts_to r x) (fun _ -> pts_to r pcm.FStar.PCM.p.one)

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

val alloc_action (#a:Type u#1) (#pcm:pcm a) (e:inames) (x:a{compatible pcm x x /\ pcm.refine x})
  : action_except (ref a pcm) e emp (fun r -> pts_to r x)


val select_refine (#a:Type u#1) (#p:pcm a)
                  (e:inames)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  FStar.PCM.frame_compatible p x v y})))
   : action_except (v:a{compatible p x v /\ p.refine v}) e
                   (pts_to r x)
                   (fun v -> pts_to r (f v))

val upd_gen (#a:Type) (#p:pcm a) (e:inames) (r:ref a p) (x y:Ghost.erased a)
            (f:FStar.PCM.frame_preserving_upd p x y)
  : action_except unit e
                  (pts_to r x)
                  (fun _ -> pts_to r y)

let property (a:Type)
  = a -> prop

val witnessed (#a:Type u#1)
              (#pcm:pcm a)
              (r:ref a pcm)
              (fact:property a)
  : Type0

let stable_property (#a:Type) (pcm:pcm a)
  = fact:property a {
       FStar.Preorder.stable fact (Steel.Preorder.preorder_of_pcm pcm)
    }

val witness (#a:Type) (#pcm:pcm a)
            (e:inames)
            (r:erased (ref a pcm))
            (fact:stable_property pcm)
            (v:Ghost.erased a)
            (_:squash (forall z. compatible pcm v z ==> fact z))
  : action_except (witnessed r fact) e (pts_to r v) (fun _ -> pts_to r v)

val recall (#a:Type u#1) (#pcm:pcm a) (#fact:property a)
           (e:inames)
           (r:erased (ref a pcm))
           (v:Ghost.erased a)
           (w:witnessed r fact)
  : action_except (v1:Ghost.erased a{compatible pcm v v1}) e
                  (pts_to r v)
                  (fun v1 -> pts_to r v `star` pure (fact v1))

(**** Invariants *)

(**[i : inv p] is an invariant whose content is [p] *)
val inv (p:slprop u#1) : Type0

val name_of_inv (#p:slprop) (i:inv p) : GTot iname

let mem_inv (#p:slprop) (e:inames) (i:inv p) : erased bool = elift2 (fun e i -> Set.mem i e) e (name_of_inv i)

let add_inv (#p:slprop) (e:inames) (i:inv p) : inames =
  Set.union (Set.singleton (name_of_inv i)) (reveal e)

(** Creates a new invariant from a separation logic predicate [p] owned at the time of the call *)
val new_invariant (e:inames) (p:slprop)
  : action_except (inv p) e p (fun _ -> emp)

val with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#opened_invariants:inames)
                   (#p:slprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   (f:action_except a (add_inv opened_invariants i) (p `star` fp) (fun x -> p `star` fp' x))
  : action_except a opened_invariants fp fp'


val frame (#a:Type)
          (#opened_invariants:inames)
          (#pre:slprop)
          (#post:a -> slprop)
          (#req:mprop pre)
          (#ens:mprop2 pre post)
          (frame:slprop)
          ($f:action_except_full a opened_invariants pre post req ens)
  : action_except_full a opened_invariants (pre `star` frame) (fun x -> post x `star` frame) req ens

val change_slprop (#opened_invariants:inames)
                  (p q:slprop)
                  (proof: (m:mem -> Lemma (requires interp p m) (ensures interp q m)))
  : action_except unit opened_invariants p (fun _ -> q)

module U = FStar.Universe

let is_frame_monotonic #a (p : a -> slprop) : prop =
  forall x y m frame. interp (p x `star` frame) m /\ interp (p y) m ==> interp (p y `star` frame) m

let is_witness_invariant #a (p : a -> slprop) =
  forall x y m. interp (p x) m /\ interp (p y) m ==> x == y

val witness_h_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
  : action_except (erased a) opened_invariants
           (h_exists p)
           (fun x -> p x)

val lift_h_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
  : action_except unit opened_invariants
           (h_exists p)
           (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))

val elim_pure (#opened_invariants:_) (p:prop)
  : action_except (u:unit{p}) opened_invariants (pure p) (fun _ -> emp)

val pts_to_join (#a:Type) (#pcm:pcm a) (r:ref a pcm) (x y : a) (m:mem) :
  Lemma (requires (interp (pts_to r x) m /\ interp (pts_to r y) m))
        (ensures (joinable pcm x y))

val pts_to_evolve (#a:Type u#a) (#pcm:_) (r:ref a pcm) (x y : a) (m:mem) :
  Lemma (requires (interp (pts_to r x) m /\ compatible pcm y x))
        (ensures  (interp (pts_to r y) m))

val id_elim_star (p q:slprop) (m:mem)
  : Pure (erased mem & erased mem)
         (requires (interp (p `star` q) m))
         (ensures (fun (ml, mr) -> disjoint ml mr
                              /\ m == join ml mr
                              /\ interp p ml
                              /\ interp q mr))

val id_elim_exists (#a:Type) (p : a -> slprop) (m:mem)
  : Pure (erased a)
         (requires (interp (h_exists p) m))
         (ensures (fun x -> interp (p x) m))


val slimp_star (p q r s : slprop)
  : Lemma (requires (slimp p q /\ slimp r s))
          (ensures (slimp (p `star` r) (q `star` s)))

val elim_wi (#a:Type) (p : a -> slprop{is_witness_invariant p}) (x y : a) (m : mem)
  : Lemma (requires (interp (p x) m /\ interp (p y) m))
          (ensures (x == y))

val witinv_framon (#a:Type) (p : a -> slprop)
  : Lemma (is_witness_invariant p ==> is_frame_monotonic p)
          [SMTPatOr [[SMTPat (is_witness_invariant p)]; [SMTPat (is_frame_monotonic p)]]]

val star_is_frame_monotonic (#a:Type)
    (f g : a -> slprop)
  : Lemma (requires (is_frame_monotonic f /\ is_frame_monotonic g))
          (ensures (is_frame_monotonic (fun x -> f x `star` g x)))
          //[SMTPat (is_frame_monotonic (fun x -> f x `star` g x))]

val star_is_witinv_left (#a:Type)
    (f g : a -> slprop)
  : Lemma (requires (is_witness_invariant f))
          (ensures  (is_witness_invariant (fun x -> f x `star` g x)))
          //[SMTPat   (is_witness_invariant (fun x -> f x `star` g x))]

val star_is_witinv_right (#a:Type)
    (f g : a -> slprop)
  : Lemma (requires (is_witness_invariant g))
          (ensures  (is_witness_invariant (fun x -> f x `star` g x)))
          //[SMTPat   (is_witness_invariant (fun x -> f x `star` g x))]
