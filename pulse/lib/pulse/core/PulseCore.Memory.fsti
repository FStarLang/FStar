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
module PulseCore.Memory
open FStar.Ghost
open FStar.PCM
module M_ = PulseCore.NondeterministicMonotonicStateMonad
module PP = PulseCore.Preorder
module PST = PulseCore.PreorderStateMonad

/// Building on `PulseCore.Heap`, this module adds memory invariants to the heap to expose the
/// final interface for Pulse's PCM-based memory model.

(**** Basic memory properties *)

(** Abstract type of memories *)
val mem  : Type u#(a + 1)

val is_ghost_action (m0 m1:mem u#a) : prop
let maybe_ghost_action (b:bool) (m0 m1:mem u#a) = b ==> is_ghost_action m0 m1

val ghost_action_preorder (_:unit)
  : Lemma (FStar.Preorder.preorder_rel is_ghost_action)
 
(**
  The memory is built on top of the heap, adding on the memory invariants. However, some of the
  properties exposed for memories need only to talk about the underlying heap, putting aside
  the memory invariants. To avoid exposing the underlying heap in this abstract interface, we
  prefer to relying on this [core_mem] function that returns a new memory sharing the same
  heap with the original memory but without any of the memory invariants.
*)
val core_mem (m:mem u#a) : mem u#a

(**** Separation logic *)

(** The type of separation logic propositions. Based on Steel.Heap.slprop *)
[@@erasable]
val slprop : Type u#(a + 1)

(** Interpreting mem assertions as memory predicates *)
val interp (p:slprop u#a) (m:mem u#a) : prop


(** Equivalence relation on slprops is just equivalence of their interpretations *)
val equiv (p1 p2:slprop u#a) : prop

(**
  An extensional equivalence principle for slprop
 *)

val slprop_extensionality (p q:slprop)
  : Lemma
    (requires p `equiv` q)
    (ensures p == q)

val slprop_equiv_refl (p:slprop)
  : Lemma (p `equiv` p)
          [SMTPat (equiv p p)]
          
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
val star  (p1 p2:slprop u#a) : slprop u#a
val h_exists (#a:Type u#b) (f: (a -> slprop u#a)) : slprop u#a

(***** Properties of separation logic equivalence *)

val equiv_symmetric (p1 p2:slprop)
  : squash (p1 `equiv` p2 ==> p2 `equiv` p1)

val equiv_extensional_on_star (p1 p2 p3:slprop)
  : squash (p1 `equiv` p2 ==> (p1 `star` p3) `equiv` (p2 `star` p3))

val emp_unit (p:slprop)
  : Lemma (p `equiv` (p `star` emp))


(** Equivalence of pure propositions is the equivalence of the underlying propositions *)
val pure_equiv (p q:prop)
  : Lemma ((p <==> q) ==> (pure p `equiv` pure q))

(** And the interpretation of pure propositions is their underlying propositions *)

val pure_true_emp (_:unit)
  : Lemma (pure True `equiv` emp)

(***** Properties of the separating conjunction *)
val star_commutative (p1 p2:slprop)
  : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))

val star_associative (p1 p2 p3:slprop)
  : Lemma ((p1 `star` (p2 `star` p3))
           `equiv`
           ((p1 `star` p2) `star` p3))

val star_congruence (p1 p2 p3 p4:slprop)
  : Lemma (requires p1 `equiv` p3 /\ p2 `equiv` p4)
          (ensures (p1 `star` p2) `equiv` (p3 `star` p4))

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

(**** Actions *)

/// Note, at this point, using the MSTTotal effect constrains the mem to be
/// in universe 2, rather than being universe polymorphic

(**
  The preorder along which the memory evolves with every update. See [Steel.Heap.heap_evolves]
*)
val mem_evolves : FStar.Preorder.preorder full_mem

(**
  To guarantee that the memory always evolve according to frame-preserving updates,
  we encode it into the [MstTot] effect build on top of the non-deterministic state total
  effect MSTATETOT. The effect is indexed by [except], which is the set of invariants that
  are currently opened.
*)
effect MstTot
  (a:Type u#a)
  (except:inames)
  (expects:slprop u#1)
  (provides: a -> slprop u#1)
  (frame:slprop u#1)
  = MSTTotal.MSTATETOT a (full_mem u#1) mem_evolves
    (requires fun m0 ->
        inames_ok except m0 /\
        interp (expects `star` frame `star` locks_invariant except m0) m0)
    (ensures fun m0 x m1 ->
        inames_ok except m1 /\
        interp (expects `star` frame `star` locks_invariant except m0) m0 /\  //TODO: fix the effect so as not to repeat this
        interp (provides x `star` frame `star` locks_invariant except m1) m1)

let _PST 
  (a:Type u#a)
  (maybe_ghost:bool)
  (except:inames)
  (expects:slprop u#1)
  (provides: a -> slprop u#1)
  (frame:slprop u#1)
= PST.pst #(full_mem u#1) a mem_evolves
    (requires fun m0 ->
        inames_ok except m0 /\
        interp (expects `star` frame `star` locks_invariant except m0) m0)
    (ensures fun m0 x m1 ->
        maybe_ghost_action maybe_ghost m0 m1 /\
        inames_ok except m1 /\
        interp (expects `star` frame `star` locks_invariant except m0) m0 /\  //TODO: fix the effect so as not to repeat this
        interp (provides x `star` frame `star` locks_invariant except m1) m1)

(** An action is just a thunked computation in [MstTot] that takes a frame as argument *)
let action_except (a:Type u#a) (except:inames) (expects:slprop) (provides: a -> slprop)
  : Type u#(max a 2) =
  frame:slprop -> MstTot a except expects provides frame

(** An action is just a thunked computation in [MstTot] that takes a frame as argument *)
let _pst_action_except 
    (a:Type u#a)
    (maybe_ghost:bool)
    (except:inames)
    (expects:slprop)
    (provides: a -> slprop)
 : Type u#(max a 2) 
 = frame:slprop -> _PST a maybe_ghost except expects provides frame

let pst_action_except (a:Type u#a) (except:inames) (expects:slprop) (provides: a -> slprop) =
  _pst_action_except a false except expects provides

let pst_ghost_action_except (a:Type u#a) (except:inames) (expects:slprop) (provides: a -> slprop) =
  _pst_action_except a true except expects provides

val sel_action (#a:Type u#1) (#pcm:_) (e:inames) (r:ref a pcm) (v0:erased a)
  : pst_action_except (v:a{compatible pcm v0 v}) e (pts_to r v0) (fun _ -> pts_to r v0)

val upd_action (#a:Type u#1) (#pcm:_) (e:inames)
               (r:ref a pcm)
               (v0:FStar.Ghost.erased a)
               (v1:a {FStar.PCM.frame_preserving pcm v0 v1 /\ pcm.refine v1})
  : pst_action_except unit e (pts_to r v0) (fun _ -> pts_to r v1)

val free_action (#a:Type u#1) (#pcm:pcm a) (e:inames)
                (r:ref a pcm) (x:FStar.Ghost.erased a{FStar.PCM.exclusive pcm x /\ pcm.refine pcm.FStar.PCM.p.one})
  : pst_action_except unit e (pts_to r x) (fun _ -> pts_to r pcm.FStar.PCM.p.one)

(** Splitting a permission on a composite resource into two separate permissions *)
val split_action
  (#a:Type u#1)
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a{composable pcm v0 v1})
  : pst_ghost_action_except unit e (pts_to r (v0 `op pcm` v1)) (fun _ -> pts_to r v0 `star` pts_to r v1)

(** Combining separate permissions into a single composite permission *)
val gather_action
  (#a:Type u#1)
  (#pcm:pcm a)
  (e:inames)
  (r:ref a pcm)
  (v0:FStar.Ghost.erased a)
  (v1:FStar.Ghost.erased a)
  : pst_ghost_action_except (_:unit{composable pcm v0 v1}) e (pts_to r v0 `star` pts_to r v1) (fun _ -> pts_to r (op pcm v0 v1))

val alloc_action (#a:Type u#1) (#pcm:pcm a) (e:inames) (x:a{compatible pcm x x /\ pcm.refine x})
  : pst_action_except (ref a pcm) e emp (fun r -> pts_to r x)

val select_refine (#a:Type u#1) (#p:pcm a)
                  (e:inames)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  FStar.PCM.frame_compatible p x v y})))
  : pst_action_except (v:a{compatible p x v /\ p.refine v}) e
                      (pts_to r x)
                      (fun v -> pts_to r (f v))

val upd_gen (#a:Type) (#p:pcm a) (e:inames) (r:ref a p) (x y:Ghost.erased a)
            (f:FStar.PCM.frame_preserving_upd p x y)
  : pst_action_except unit e
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
       FStar.Preorder.stable fact (PP.preorder_of_pcm pcm)
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

val pts_to_not_null_action 
      (#a:Type u#1) (#pcm:pcm a)
      (e:inames)
      (r:erased (ref a pcm))
      (v:Ghost.erased a)
: pst_ghost_action_except (squash (not (is_null r))) e
    (pts_to r v)
    (fun _ -> pts_to r v)

(**** Invariants *)

(**[i : inv p] is an invariant whose content is [p] *)
val pre_inv : Type0

val inv (p:slprop u#1) : Type0

val pre_inv_of_inv (#p:slprop) (i:inv p) : pre_inv

val name_of_pre_inv (i:pre_inv) : GTot iname

let name_of_inv (#p:slprop) (i:inv p)
  : GTot iname
  = name_of_pre_inv (pre_inv_of_inv i)

let mem_inv (#p:slprop) (e:inames) (i:inv p) : erased bool = elift2 (fun e i -> Set.mem i e) e (name_of_inv i)

let add_inv (#p:slprop) (e:inames) (i:inv p) : inames =
  Set.union (Set.singleton (name_of_inv i)) (reveal e)

(** Creates a new invariant from a separation logic predicate [p] owned at the time of the call *)
let fresh_wrt (ctx:list pre_inv)
              (i:iname)
  = forall i'. List.Tot.memP i' ctx ==> name_of_pre_inv i' <> i

val distinct_invariants_have_distinct_names
      (e:inames)
      (p:slprop)
      (q:slprop { p =!= q })
      (i:inv p)
      (j:inv q)
  : action_except (squash (name_of_inv i =!= name_of_inv j)) e emp (fun _ -> emp)

val invariant_name_identifies_invariant
      (e:inames)
      (p q:slprop)
      (i:inv p)
      (j:inv q { name_of_inv i == name_of_inv j } )
  : action_except (squash (p == q /\ i == j)) e emp (fun _ -> emp)

val fresh_invariant (e:inames) (p:slprop) (ctx:list pre_inv)
  : action_except (i:inv p { fresh_wrt ctx (name_of_inv i) }) e p (fun _ -> emp)

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
          (frame:slprop)
          ($f:action_except a opened_invariants pre post)
  : action_except a opened_invariants (pre `star` frame) (fun x -> post x `star` frame)

val pst_frame (#a:Type)
              (#maybe_ghost:bool)
              (#opened_invariants:inames)
              (#pre:slprop)
              (#post:a -> slprop)
              (frame:slprop)
              ($f:_pst_action_except a maybe_ghost opened_invariants pre post)
  : _pst_action_except a maybe_ghost opened_invariants (pre `star` frame) (fun x -> post x `star` frame)

module U = FStar.Universe

val witness_h_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
  : pst_ghost_action_except (erased a) opened_invariants
           (h_exists p)
           (fun x -> p x)

val intro_exists (#opened_invariants:_) (#a:_) (p:a -> slprop) (x:erased a)
  : pst_ghost_action_except unit opened_invariants
           (p x)
           (fun _ -> h_exists p)

val lift_h_exists (#opened_invariants:_) (#a:_) (p:a -> slprop)
  : pst_ghost_action_except unit opened_invariants
           (h_exists p)
           (fun _a -> h_exists #(U.raise_t a) (U.lift_dom p))

val elim_pure (#opened_invariants:_) (p:prop)
  : pst_ghost_action_except (u:unit{p}) opened_invariants (pure p) (fun _ -> emp)

val intro_pure (#opened_invariants:_) (p:prop) (_:squash p)
  : pst_ghost_action_except unit opened_invariants emp (fun _ -> pure p)

val drop (#opened_invariants:_) (p:slprop)
  : pst_ghost_action_except unit opened_invariants p (fun _ -> emp)

let non_info a = x:erased a -> y:a { reveal x == y}
val lift_ghost
      (#a:Type)
      #opened_invariants #p #q
      (ni_a:non_info a)
      (f:erased (pst_ghost_action_except a opened_invariants p q))
  : pst_ghost_action_except a opened_invariants p q

[@@erasable]
val ghost_ref (#[@@@unused] a:Type u#a) ([@@@unused]p:pcm a) : Type0
val ghost_pts_to (#a:Type u#a) (#p:pcm a) (r:ghost_ref p) (v:a) : slprop u#a

val ghost_alloc
    (#o:_)
    (#a:Type u#1)
    (#pcm:pcm a)
    (x:erased a{compatible pcm x x /\ pcm.refine x})
: pst_ghost_action_except
    (ghost_ref pcm)
    o
    emp 
    (fun r -> ghost_pts_to r x)

val ghost_read
    #o
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: pst_ghost_action_except
    (erased (v:a{compatible p x v /\ p.refine v}))
    o
    (ghost_pts_to r x)
    (fun v -> ghost_pts_to r (f v))

val ghost_write
    #o
    (#a:Type)
    (#p:pcm a)
    (r:ghost_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: pst_ghost_action_except unit o 
    (ghost_pts_to r x)
    (fun _ -> ghost_pts_to r y)

val ghost_share
    #o
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: pst_ghost_action_except unit o
    (ghost_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pts_to r v0 `star` ghost_pts_to r v1)

val ghost_gather
    #o
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: pst_ghost_action_except
    (squash (composable pcm v0 v1)) o
    (ghost_pts_to r v0 `star` ghost_pts_to r v1)
    (fun _ -> ghost_pts_to r (op pcm v0 v1))
