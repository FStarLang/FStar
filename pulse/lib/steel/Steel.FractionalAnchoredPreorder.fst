(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: N. Swamy
*)
module Steel.FractionalAnchoredPreorder

(** This module provides a partial commutative monoid (PCM) for use in
    the ghost state of a concurrent Steel program.

    Its goal is to facilitate a form of information-sharing between
    multiple threads including the following features: Fractions,
    Preorders, Snapshots, and Anchors --- Anchors are the most
    unusual.

    1. Fractions: Ownership of the state is controlled by a fractional
       permission, so multiple threads may share read-only privileges
       on the state, but only one can have write permission.

    2. Preorders: The ghost state is governed by a preorder p and all
       updates to the state must respect the preorder (a reflexive,
       transitive relation on the state)

    3. Snapshots: Since the state always evolves by a preorder, it is
       possible to take a snapshot of the state. A snapshot does not
       confer any particular ownership on the state, except knowledge
       of a snapshot ensures that the current state is related to the
       snapshot by the preorder.

    4. Anchors are a kind of refinement of the preorder. If a thread
       owns an anchored value [v], then no other thread, even a thread
       owning a full fractional permission, can advance the state "too
       far" from the anchor. In particular, the PCM is parameterized
       by a binary relation on values, [anchors:anchor_relation]. If a
       thread owns the anchor [v], then the current value `cur` of the
       state must be in relation [v `anchors` cur]. This can be used
       to ensure that the knowledge of one thread is never becomes too
       stale.

   For example, this allows one to model a shared monotonically
   increasing counter, where if one thread anchors knowledge of the
   counter at the value 5, no other thread can increase the value of
   the counter beyond, say, 10, (when the anchor relation is y - x <=
   5), until the anchoring thread releases the anchor. Further, at any
   point, a thread can take a snapshot of the counter and rely on the
   fact that the value of the counter in the future will be >= the
   snapshot.
*)
open FStar.PCM
open FStar.Preorder
open Steel.Preorder
open Steel.FractionalPermission

#push-options "--fuel 0 --ifuel 2"

/// A permission: is a pair of
///
///   * an optional fractional permission; with `Some p` indicating
///     some ownership, while `None` is an additional "0" permission
///     value, to encode snapshots.
///
///   * and an optional anchor, where `Some a` indicates the current
///     value can't be too far from `a`.
let permission (v:Type) = option perm & option v

/// Non-zero permission is either a read or write permission
let has_nonzero #v (p:permission v) = Some? (fst p)
/// Has an anchor set
let has_anchor #v (p:permission v) = Some? (snd p)
/// Either an anchor or non-zero
let has_some_ownership #v (p:permission v) = has_nonzero p || has_anchor p
/// The anchoring value
let anchor_of #v (p:permission v { has_anchor p }) : v = Some?.v (snd p)

/// The anchoring relation:
///   -- A binary relation on values
///   -- refining the preorder
///   -- and if x `anchors` z then it also anchors any `y` between `x` and `z`
///
/// Explaining the third clause a bit:
/// Think intuitively of anchoring relations as a kind of distance measure
///
///   if `z` is close enough to `x` then if `z` is further than `y`
///   (since it is ahead of `y` in the preorder) then `y` is also
///   close enough to `x`
let anchor_rel (#v:Type) (p:preorder v) =
  anchors:(v -> v -> prop) {
    (forall v0 v1. anchors v0 v1 ==> p v0 v1) /\
    (forall x z. x `anchors` z  ==> (forall y. p x y /\ p y z ==> x `anchors` y)) //
  }

/// An implementation remark: We use Steel.Preorder here to
/// generically transform any preorder into a PCM. That works by
/// taking the value of the PCM to be a history of values related by
/// the preorder. So, throughout, we'll be using the the [vhist p]
/// from Steel.Preorder, the type of a non-empty history compatible
/// with [p]. The details of the histories don't matter much for our
/// purposes---we only care about the most recent value, for which
/// we'll use [curval v].

/// If the anchor is set, then the current value is anchored by it
let anchored (#v:Type) (#p:preorder v) (anchors:anchor_rel p)
             (pv:(permission v & vhist p))
  = has_anchor (fst pv) ==> anchor_of (fst pv) `anchors` curval (snd pv)

/// A value in our fractional anchored PCM is a pair of a permission
/// and a p-compatible history, refined to ensure that if the anchor
/// is set, then the current value is anchored by it.
let avalue (#v:Type) (#p:preorder v) (anchors:anchor_rel p)
  = pv:(permission v & vhist p) { anchored anchors pv }

/// initial_value: A utility to construct a value in the PCM
#push-options "--fuel 1"
let initial_value (#v:Type) (#p:preorder v) (#anchors:anchor_rel p) (value:v { anchors value value })
  : avalue anchors
  = (Some full_perm, Some value), [value]
#pop-options

/// We add a unit element to [avalue], as needed for a PCM
[@@erasable]
noeq
type knowledge (#v:Type) (#p:preorder v) (anchors:anchor_rel p) =
  | Owns     : avalue anchors -> knowledge anchors
  | Nothing  : knowledge anchors

let b2p (b:bool)
  : prop
  = b == true

/// Fractional permissions are composable when their sum <= 1.0
let perm_opt_composable (p0 p1:option perm)
  : prop
  = match p0, p1 with
    | None, None -> True
    | Some p, None
    | None, Some p -> b2p (p `lesser_equal_perm` full_perm)
    | Some p0, Some p1 -> b2p (sum_perm p0 p1 `lesser_equal_perm` full_perm)

/// Composing them sums the permissions
let compose_perm_opt (p0 p1:option perm) =
  match p0, p1 with
  | None, p
  | p, None -> p
  | Some p0, Some p1 -> Some (sum_perm p0 p1)

/// Anchored permissions are composable when at most one of them has the anchor set
let permission_composable #v (p0 p1 : permission v)
  : prop
  = let q0, s0 = p0 in
    let q1, s1 = p1 in
    perm_opt_composable q0 q1 /\  // some of fracs can't exceed 1
    not (Some? s0 && Some? s1)   // at most one can have an anchor

/// Compose permissions component wise, keeping the anchor if set
let compose_permissions (#v:_) (p0:permission v) (p1:permission v{permission_composable p0 p1})
  : permission v
  = compose_perm_opt (fst p0) (fst p1),
    (match snd p0, snd p1 with
     | None, a
     | a, None -> a)

/// This is the central definition of the PCM --- defining when two
/// values are composable, or equivalently, when one thread's
/// knowledge of [av0] is compatible with another thread's knowledge
/// of [av1]
///
/// This definition shows the interplay between fractions and anchors.
/// It wasn't obvious to me how to factor this further, e.g., adding
/// anchors to preorders and then separately adding fractions to it.
let avalue_composable (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                      (av0 av1: avalue anchors)
   : prop
   = let (p0, v0) = av0 in
     let (p1, v1) = av1 in
     permission_composable p0 p1 /\
    (if not (has_some_ownership p0)
     && not (has_some_ownership p1)
     then p_composable _ v0 v1 //neither has ownership, one history is older than the other
     else if not (has_some_ownership p0)
          && has_some_ownership p1
     then (
          if has_nonzero p1
          then v1 `extends` v0 //the one with ownership is more recent
          else ( //this part is the most subtle
            assert (has_anchor p1);
            p_composable _ v0 v1 /\ 
            (v0 `extends` v1 ==> //if v0 is a more recent snapshot than v1
                                 //then v0 must still be anchored by v1's anchor
             anchor_of p1 `anchors` curval v0)
          )
     )
     else if has_some_ownership p0
          && not (has_some_ownership p1)
     then ( //symmetric
          if has_nonzero p0
          then v0 `extends` v1
          else ( 
            assert (has_anchor p0);          
            p_composable _ v0 v1 /\
            (v1 `extends` v0 ==> anchor_of p0 `anchors` curval v1)
          )
     )
     else (
       assert (has_some_ownership p0 && has_some_ownership p1);
       if has_nonzero p0 && has_nonzero p1
       then v0 == v1 //if both have non-zero perm, then they must both only have read permission and must agree on the value
       else if has_nonzero p0 && has_anchor p1
       then ( assert (not (has_nonzero p1));
              //The key part of the anchor semantics:
              v0 `extends` v1 /\           //v0 has advanceable ownership, so extends
              anchor_of p1 `anchors` curval v0  //but not beyond what is allowed by s
            )
       else if has_anchor p0 && has_nonzero p1 //symmetric
       then ( assert (not (has_nonzero p0));
              v1 `extends` v0 /\
              anchor_of p0 `anchors` curval v1  //v1 extends, but not beyond what is allowed by s
            )
       else (assert false; False)
     )
    ) //exhaustive

/// Lifting avalue comosability to knowledge, including the unit
let composable #v (#p:preorder v) (#a:anchor_rel p)
  : symrel (knowledge a)
  = fun (k0 k1:knowledge a) ->
    match k0, k1 with
    | Nothing, _
    | _, Nothing -> True

    | Owns m, Owns m' ->
      avalue_composable m m'

/// Compose avalues by composing permissions and composing the values
/// using the underlying preorder PCM
let compose_avalue (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                   (m0:avalue anchors)
                   (m1:avalue anchors { avalue_composable m0 m1 } )
  : avalue anchors
  =  let p0, v0 = m0 in
     let p1, v1 = m1 in
     let p12 = compose_permissions p0 p1 in
     let v12 = p_op _ v0 v1 in
     p12, v12

////////////////////////////////////////////////////////////////////////////////

(** avalue composition is associative and commutative **)

let compose_avalue_comm (#v:Type) (#p:preorder v) (#anc:anchor_rel p)
                        (m0: avalue anc)
                        (m1: avalue anc{ avalue_composable m0 m1 })
 : Lemma (compose_avalue m0 m1 == compose_avalue m1 m0)
 = ()

let avalue_composable_assoc_l (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                              (m0: avalue anchors)
                              (m1: avalue anchors)
                              (m2: avalue anchors {
                                avalue_composable m1 m2 /\
                                avalue_composable m0 (compose_avalue m1 m2)
                              })
 : Lemma (avalue_composable m0 m1 /\
          avalue_composable (compose_avalue m0 m1) m2)
 = ()

let compose_avalue_assoc_l (#v:Type) (#p:preorder v) (#s:anchor_rel p)
                           (m0: avalue s)
                           (m1: avalue s)
                           (m2: avalue s {
                             avalue_composable m1 m2 /\
                             avalue_composable m0 (compose_avalue m1 m2)
                           })
 : Lemma (avalue_composable m0 m1 /\
          avalue_composable (compose_avalue m0 m1) m2 /\
          compose_avalue m0 (compose_avalue m1 m2) ==
          compose_avalue (compose_avalue m0 m1) m2)
 = avalue_composable_assoc_l m0 m1 m2

let avalue_composable_assoc_r (#v:Type) (#p:preorder v) (#anchors:anchor_rel p)
                            (m0: avalue anchors)
                            (m1: avalue anchors)
                            (m2: avalue anchors {
                              avalue_composable m0 m1 /\
                              avalue_composable (compose_avalue m0 m1) m2
                            })
 : Lemma (avalue_composable m1 m2 /\
          avalue_composable m0 (compose_avalue m1 m2))
 = ()


let compose_avalue_assoc_r (#v:Type) (#p:preorder v) (#s:anchor_rel p)
                           (m0: avalue s)
                           (m1: avalue s)
                           (m2: avalue s{
                             avalue_composable m0 m1 /\
                             avalue_composable (compose_avalue m0 m1) m2
                           })
 : Lemma (avalue_composable m1 m2 /\
          avalue_composable m0 (compose_avalue m1 m2) /\
          compose_avalue m0 (compose_avalue m1 m2) ==
          compose_avalue (compose_avalue m0 m1) m2)
 = avalue_composable_assoc_r m0 m1 m2

////////////////////////////////////////////////////////////////////////////////

/// lifting avalue composition to knowledge, including unit
let compose (#v:Type) (#p:preorder v) (#s:anchor_rel p)
            (k0:knowledge s)
            (k1:knowledge s{ composable k0 k1 })
  : knowledge s
  = match k0, k1 with
    | Nothing, k
    | k, Nothing -> k

    | Owns m, Owns m' ->
      Owns (compose_avalue m m')

let composable_assoc_r #v (#p:preorder v) (#s:anchor_rel p)
                       (k0 k1 k2: knowledge s)
  : Lemma
    (requires  composable k0 k1 /\
               composable (compose k0 k1) k2)
    (ensures
               composable k1 k2 /\
               composable k0 (compose k1 k2) /\
               compose k0 (compose k1 k2) ==
               compose (compose k0 k1) k2
               )
  = match k0, k1, k2 with
    | Nothing, _, _
    | _, Nothing, _
    | _, _, Nothing -> ()
    | Owns m0, Owns m1, Owns m2 ->
      compose_avalue_assoc_r m0 m1 m2

let composable_assoc_l #v (#p:preorder v) (#s:anchor_rel p)
                          (k0 k1 k2: knowledge s)
  : Lemma
    (requires
               composable k1 k2 /\
               composable k0 (compose k1 k2))
    (ensures   composable k0 k1 /\
               composable (compose k0 k1) k2 /\
               compose k0 (compose k1 k2) ==
               compose (compose k0 k1) k2)
  = match k0, k1, k2 with
    | Nothing, _, _
    | _, Nothing, _
    | _, _, Nothing -> ()
    | Owns m0, Owns m1, Owns m2 ->
      compose_avalue_assoc_l m0 m1 m2

/// Now, we can define our PCM


/// The core of the PCM
let p0 #v #p #s : pcm' (knowledge #v #p s) = {
  composable;
  op=compose;
  one=Nothing
}

let avalue_perm (#v:Type)
                (#p:preorder v)
                (#s:anchor_rel p)
                (m:avalue s)
    = fst m

/// A avalue represents full ownership when the fraction is full AND
/// the anchor is set. This means that no knowledge held by any other
/// thread can constrain this value meaningfully.
let avalue_owns (#v:Type)
                (#p:preorder v)
                (#s:anchor_rel p)
                (m:avalue s)
  : prop
  = fst (avalue_perm m) == Some full_perm /\
    Some? (snd (avalue_perm m))

let full_knowledge #v #p #s (kn:knowledge #v #p s)
  : prop
  = match kn with
    | Nothing -> False
    | Owns km -> avalue_owns km

/// The PCM itself, together with proofs of its properties
let pcm #v #p #s : pcm (knowledge #v #p s) = {
  p = p0;
  comm = (fun k0 k1 ->
             match k0, k1 with
             | Nothing, _
             | _, Nothing -> ()
             | Owns m0, Owns m1 ->
               compose_avalue_comm m0 m1);
  assoc = (fun k0 k1 k2 -> composable_assoc_l k0 k1 k2);
  assoc_r = (fun k0 k1 k2 -> composable_assoc_r k0 k1 k2);
  is_unit = (fun _ -> ());
  refine = full_knowledge;
}

/// Some utilities: The value of an avalue
let avalue_val (#v:Type)
               (#p:preorder v)
               (#s:anchor_rel p)
               (m:avalue #v #p s)
    = snd m

/// Updating the value, in a full-ownership situation, also involves
/// updating the anchor
let avalue_update (#v:Type)
                  (#p:preorder v)
                  (#s:anchor_rel p)
                  (m:avalue s)
                  (value:vhist p { s (curval value) (curval value) })
  : avalue s
  = let p, _ = avalue_perm m in
    let p' = p, Some (curval value) in
    (p', value)

/// Our core frame-preserving update:
///
///    If you fully own a value, you can update it so long as you
///    respect the preorder, and prove that the new value is related
///    to itself by the anchor (since we'll be setting the anchor to
///    the new value)
///
/// This is a building block: we'll define a derived version that
/// on values rather than histories
#push-options "--z3rlimit_factor 2"
let update_hist (#v:Type)
                (#p:preorder v)
                (#s:anchor_rel p)
                (m:avalue s)
                (v1:vhist p {
                      avalue_owns m /\
                      v1 `extends` avalue_val m /\
                      s (curval v1) (curval v1)
                })
  : frame_preserving_upd pcm (Owns m) (Owns (avalue_update m v1))
  = fun full_v ->
      let Owns full_m = full_v in
      let m_res = avalue_update full_m v1 in
      Owns m_res
#pop-options

/// Updating with value, rather than a history
let avalue_update_value (#v:Type)
                        (#p:preorder v)
                        (#s:anchor_rel p)
                        (m:avalue s)
                        (value:v {
                          curval (avalue_val m) `p` value /\
                          s value value 
                        })
  : m':avalue s {
       curval (avalue_val m') == value /\
       avalue_val m'  `extends` avalue_val m
    }
  = let v = avalue_val m in
    avalue_update m (extend_history v value)

/// A derived frame-preserving update for which one presents only a value
let update_value (#v:Type)
                 (#p:preorder v)
                 (#s:anchor_rel p)
                 (m:avalue s)
                 (v1:v {
                   avalue_owns m /\ //if you have full ownership of key
                   curval (avalue_val m) `p` v1 /\ //you can update it wrt the preorder only
                   s v1 v1 //and it is related to itself by the anchor
                 })
  : frame_preserving_upd pcm (Owns m) (Owns (avalue_update_value m v1))
  = coerce_eq () (update_hist m (extend_history (avalue_val m) v1)) //F* goes nuts and starts swallowing gobs of memory without the coerce_eq: TODO, debug

/// Now for anchored updates

/// Ownership of the whole fraction, but not the anchor
let avalue_owns_anchored (#v:Type)
                         (#p:preorder v)
                         (#s:anchor_rel p)
                         (m:avalue s)
    = fst (avalue_perm m) == Some full_perm /\
      None? (snd (avalue_perm m))

/// [v1] is compatible with (i.e., not too far from) any anchor of [v0]
let compat_with_any_anchor_of (#v:Type)
                              (#p:preorder v)
                              (#anchors:anchor_rel p)
                              (v1:v)
                              (v0:avalue anchors)
  = forall (anchor:v). anchor `anchors` curval (avalue_val v0) ==>
                  anchor `anchors` v1

/// An anchored update: Update the value, but leave the permission
/// unchanged Only possible if the new value is compatible with any
/// anchor of the old value
let avalue_anchored_update (#v:Type)
                           (#p:preorder v)
                           (#s:anchor_rel p)
                           (m:avalue s)
                           (value:vhist p {
                                curval value `compat_with_any_anchor_of` m
                           })
  : avalue s
  = avalue_perm m, value

/// A frame-preserving update for anchored values.
///   Notice the additional precondition, refining the preorder
let update_anchored_hist (#v:Type)
                         (#p:preorder v)
                         (#s:anchor_rel p)
                         (m:avalue s)
                         (v1:vhist p {
                           avalue_owns_anchored m /\
                           v1 `extends` avalue_val m /\
                           curval v1 `compat_with_any_anchor_of` m
                         })
  : frame_preserving_upd pcm (Owns m) (Owns (avalue_anchored_update m v1))
  = fun full_v ->
      let Owns full_m = full_v in
      let m_res = avalue_anchored_update full_m v1 in
      Owns m_res

/// A derived form without a history on the new value
let avalue_update_anchored_value (#v:Type)
                                 (#p:preorder v)
                                 (#s:anchor_rel p)
                                 (m:avalue s)
                                 (value:v { curval (avalue_val m) `p` value /\
                                            value `compat_with_any_anchor_of` m })
  : m':avalue s {
       curval (avalue_val m') == value /\
       avalue_val m'  `extends` avalue_val m
    }
  = let v = avalue_val m in
    avalue_anchored_update m (extend_history v value)

/// Derived frame-preserving update
let update_anchored_value (#v:Type)
                          (#p:preorder v)
                          (#s:anchor_rel p)
                          (m:avalue s)
                          (v1:v {
                            avalue_owns_anchored m /\ //if you own an anchored key, you can update if you respect
                            curval (avalue_val m) `p` v1 /\ //the preorder
                            v1 `compat_with_any_anchor_of` m //and respect any anchor of the current value
                          })
  : frame_preserving_upd pcm (Owns m) (Owns (avalue_update_anchored_value m v1))
  = coerce_eq () (update_anchored_hist m (extend_history (avalue_val m) v1))

////////////////////////////////////////////////////////////////////////////////

/// Now for some lemmas about which kinds of knowledge are compatible
/// with others and about snapshots

/// A [snapshot] keeps the value, dropping all permissions
let snapshot (#v:Type0) (#p:preorder v) (#s:anchor_rel p)
             (a: avalue s)
  : avalue s
  = (None, None), avalue_val a

let perm_ok #v #p #s (a:avalue #v #p s)
  = perm_opt_composable (fst (avalue_perm a)) None

/// You can take a snapshot of any knowledge
///   - perm_ok is a side-condition. Any vprop defined on top of this
///     will ensure that the permissions are always <= 1.0
let snapshot_lemma (#v:Type)
                   (#p:preorder v)
                   (#s:anchor_rel p)
                   (a:avalue s)
  : Lemma (requires perm_ok a)
          (ensures Owns a `composable` Owns (snapshot a))
  = ()

/// A snapshot is duplicable
let snapshot_dup_lemma (#v:Type)
                       (#p:preorder v)
                       (#s:anchor_rel p)
                       (a:avalue s)
  : Lemma (ensures Owns (snapshot a) `composable` Owns (snapshot a))
  = ()

/// An anchored snapshot takes the current value, drops the fraction
/// but keeps the anchor or takes the current value as the anchor, if
/// not set
let anchored_snapshot (#v:Type0) (#p:preorder v) (#s:anchor_rel p)
                      (a: avalue s { s (curval (avalue_val a)) (curval (avalue_val a)) })
  : avalue s & avalue s
  = let (p,a0), v = a in
    let a =
      match a0 with
      | None -> Some (curval v)
      | Some a -> Some a
    in
    ((p, None), v),
    ((None, a), v)

/// An anchored snapshot also be taken at any time, but what's left
/// over is ownership that is constrained by the anchor
let anchored_snapshot_lemma (#v:Type)
                            (#p:preorder v)
                            (#s:anchor_rel p)
                            (a:avalue s)
  : Lemma (requires avalue_owns a /\
                    s (curval (avalue_val a)) (curval (avalue_val a)))
          (ensures (
            let owned, anchor = anchored_snapshot a in
            (Owns owned `composable` Owns anchor) /\
            compose_avalue owned anchor == a))
  = ()

