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
module Steel.PCMMap
(** Given a PCM on [p:pcm a] and a key type [k:eqtype], this module
    builds a [pcm (map k a)] by lifting [p] pointwise. It also lifts
    frame-preserving updates on [p] to frame-preserving updates on
    entries of the map. **)
open FStar.Map
open FStar.PCM

/// The carrier type of our constructed PCM
///
/// -- FStar.Map comes with a notion of domain that we don't need here
///    So, we'll just worked with maps whose domain is always
///    universal.
let map (k:eqtype) (v:Type) =
  m:Map.t k v {
    Map.domain m `Set.equal` Set.complement Set.empty
  }

/// Maps are composable if they are composable pointwise
let composable_maps (#a:_)
                    (#k:eqtype)
                    (p:pcm a)
                    (m0 m1: map k a)
  : prop
  = forall k. Map.sel m0 k `composable p` Map.sel m1 k

/// Compose maps pointwise
let compose_maps (#a:_) (#k:eqtype)
                 (p:pcm a)
                 (m0:map k a)
                 (m1:map k a { composable_maps p m0 m1 })
  : map k a
  = Map.map_literal (fun k ->
                       Map.sel m0 k `op p` Map.sel m1 k)

/// Composability is commutative
let composable_maps_comm #k #a
                    (p:pcm a)
                    (m0 m1: map k a)
  : Lemma (composable_maps p m0 m1 <==>
           composable_maps p m1 m0)
  = ()

/// Composition is commutative
let compose_maps_comm #k #a
                    (p:pcm a)
                    (m0 m1: map k a)
  : Lemma
    (requires composable_maps p m0 m1)
    (ensures compose_maps p m0 m1 == compose_maps p m1 m0)
  = let m01 = compose_maps p m0 m1 in
    let m10 = compose_maps p m1 m0 in
    introduce forall key.
         Map.sel m01 key == Map.sel m10 key
    with ( p.comm (Map.sel m0 key) (Map.sel m1 key) );
    assert (Map.equal m01 m10)

/// Composability is left-associative
let composable_maps_assoc_l #k #a
                          (p:pcm a)
                          (m0 m1 m2: map k a)
  : Lemma
    (requires
      composable_maps p m1 m2 /\
      composable_maps p m0 (compose_maps p m1 m2))
    (ensures
      composable_maps p m0 m1 /\
      composable_maps p (compose_maps p m0 m1) m2 /\
      compose_maps p (compose_maps p m0 m1) m2 ==
      compose_maps p m0 (compose_maps p m1 m2))
  = introduce forall key.
      composable p (Map.sel m0 key) (Map.sel m1 key)
    with ( p.assoc (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    let m01 = compose_maps p m0 m1 in
    introduce forall key.
      composable p (Map.sel m01 key) (Map.sel m2 key)
    with ( p.assoc (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    let m012 = compose_maps p m01 m2 in
    let m012' = compose_maps p m0 (compose_maps p m1 m2) in
    introduce forall key.
      Map.sel m012 key == Map.sel m012' key
    with ( p.assoc (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    assert (Map.equal
                 (compose_maps p (compose_maps p m0 m1) m2)
                 (compose_maps p m0 (compose_maps p m1 m2)))

/// Composability is right-associative
let composable_maps_assoc_r #k #a
                          (p:pcm a)
                          (m0 m1 m2: map k a)
  : Lemma
    (requires
      composable_maps p m0 m1 /\
      composable_maps p (compose_maps p m0 m1) m2)
    (ensures
      composable_maps p m1 m2 /\
      composable_maps p m0 (compose_maps p m1 m2) /\
      compose_maps p (compose_maps p m0 m1) m2 ==
      compose_maps p m0 (compose_maps p m1 m2))
  = introduce forall key.
      composable p (Map.sel m1 key) (Map.sel m2 key)
    with ( p.assoc_r (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    let m12 = compose_maps p m1 m2 in
    introduce forall key.
      composable p (Map.sel m0 key) (Map.sel m12 key)
    with ( p.assoc_r (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    let m012 = compose_maps p (compose_maps p m0 m1) m2 in
    let m012' = compose_maps p m0 (compose_maps p m1 m2) in
    introduce forall key.
      Map.sel m012 key == Map.sel m012' key
    with ( p.assoc_r (Map.sel m0 key) (Map.sel m1 key) (Map.sel m2 key) );
    assert (Map.equal m012 m012')

/// The core of the constructed PCM
///    The unit is just the pointwise unit
let pcm'_map_of_pcm (#a:_) (k:eqtype) (p:pcm a)
  : pcm' (map k a)
  = {
       composable = composable_maps p;
       op = compose_maps p;
       one = Map.const p.p.one
    }

/// The unit is really a unit
let is_unit #k #a (p:pcm a) (m:map k a)
  : Lemma (composable_maps p (Map.const p.p.one) m /\
           compose_maps p (Map.const p.p.one) m `Map.equal` m /\
           compose_maps p m (Map.const p.p.one) `Map.equal` m)
   = introduce forall k. composable p p.p.one (Map.sel m k)
     with (
       p.is_unit (Map.sel m k)
     );
     introduce forall k. Map.sel (compose_maps p (Map.const p.p.one) m) k == Map.sel m k /\
                    Map.sel (compose_maps p m (Map.const p.p.one)) k == Map.sel m k
     with (
       p.is_unit (Map.sel m k);
       p.comm p.p.one (Map.sel m k)
     )

/// The main function of this module:
///    Given a [k] and [p:pcm a], lift it pointwise
let pointwise (#a:_) (k:eqtype) (p:pcm a)
  : pcm (map k a)
  = {
       p = pcm'_map_of_pcm k p;
       comm = (fun m0 m1 -> compose_maps_comm p m0 m1);
       assoc = (fun m0 m1 m2 -> composable_maps_assoc_l p m0 m1 m2);
       assoc_r = (fun m0 m1 m2 -> composable_maps_assoc_r p m0 m1 m2);
       is_unit = (fun m -> is_unit p m);
       refine = (fun m -> forall k. p.refine (Map.sel m k))
    }

/// Now some constructions that allow us to lift frame-preserving updates

/// If a two maps are compatible, then they are also compatible pointwise
let compatible_pointwise #a #k
                         (p:pcm a)
                         (m0 m1:map k a)
  : Lemma
    (requires compatible (pointwise k p) m0 m1)
    (ensures forall k. compatible p (Map.sel m0 k) (Map.sel m1 k))
  = let pcm' = pointwise k p in
    introduce forall k. compatible p (Map.sel m0 k) (Map.sel m1 k)
    with (
      eliminate exists frame.
        composable pcm' m0 frame /\ op pcm' frame m0 == m1
      returns _
      with _. (
        introduce exists (frame:a).
                         composable p
                                    (Map.sel m0 k)
                                    frame /\
                         op p frame (Map.sel m0 k) == Map.sel m1 k
        with (Map.sel frame k)
        and ()))

/// A very specific lemma for use in lifting frame-preserving updates
///
/// If two maps are compatible, then updating them at a key with
/// values that are compatible produces compatible maps
let compatible_pointwise_upd #a (#k:eqtype)
                             (p:pcm a)
                             (v1 full_v1:a)
                             (m0 full_m0:map k a)
                             (key:k)
  : Lemma
    (requires
      compatible p v1 full_v1 /\
      compatible (pointwise k p) m0 full_m0)
    (ensures
      compatible (pointwise k p) (Map.upd m0 key v1)
                                 (Map.upd full_m0 key full_v1))
  = compatible_pointwise p m0 full_m0;
    assert (compatible p (Map.sel m0 key) (Map.sel full_m0 key));
    let m1 = (Map.upd m0 key v1) in
    let full_m1 = (Map.upd full_m0 key full_v1) in
    let p' = pointwise k p in
    eliminate exists (frame_m0:_). composable p' m0 frame_m0 /\ op p' frame_m0 m0 == full_m0
    returns _
    with _. (
    eliminate exists (frame0:_). composable p v1 frame0 /\ op p frame0 v1 == full_v1
    returns _
    with _. (
      introduce exists (frame:_).
      composable p' m1 frame /\ op p' frame m1 == full_m1
    with (Map.upd frame_m0 key frame0)
    and (
        let w = Map.upd frame_m0 key frame0 in
        assert (Map.equal (compose_maps p w m1) full_m1)
    )))

/// If any frame composes with [v0] to produce [full_v0]
/// can also be composed with [v1] to produce [full_v1]
///
/// Then any frame composable with a map contains [v0] yielding a map
/// containing [full_v0], is also composable with a map containing
/// [v1] yielding [full_v1] at that key.
let lift_frame_preservation #a (#k:eqtype) (p:pcm a)
                            (m0 full_m0:map k a)
                            (v1 full_v1:a)
                            (key:k)
  : Lemma
    (requires (
      let v0 = Map.sel m0 key in
      let full_v0 = Map.sel full_m0 key in
      let m1 = Map.upd m0 key v1 in
      let full_m1 = Map.upd full_m0 key full_v1 in
      (forall (frame:a{composable p v0 frame}). {:pattern composable p v0 frame}
         composable p v1 frame /\
         (op p v0 frame == full_v0 ==>
          op p v1 frame == full_v1))))
    (ensures (
      let v0 = Map.sel m0 key in
      let full_v0 = Map.sel full_m0 key in
      let m1 = Map.upd m0 key v1 in
      let full_m1 = Map.upd full_m0 key full_v1 in
      let p' = pointwise k p in
      (forall (frame:_{composable p' m0 frame}).
         composable p' m1 frame /\
         (op p' m0 frame == full_m0 ==>
          op p' m1 frame == full_m1))))
    = let v0 = Map.sel m0 key in
      let full_v0 = Map.sel full_m0 key in
      let m1 = Map.upd m0 key v1 in
      let full_m1 = Map.upd full_m0 key full_v1 in
      let p' = pointwise k p in
      introduce forall (frame:_{composable p' m0 frame}).
         composable p' m1 frame /\
         (op p' m0 frame == full_m0 ==>
          op p' m1 frame == full_m1)
      with (
        introduce _ /\ _
        with ()
        and ( introduce _ ==> _
              with _. (
                  assert (compose_maps p m1 frame `Map.equal` full_m1)
              )
        )
      )

/// Lift a frame-preserving update from [v0] to [v1]
/// to a map contains [v0] at [k] producing the updated map
let lift_frame_preserving_upd #a #k (#p:pcm a)
                              (v0 v1: Ghost.erased a)
                              (f:frame_preserving_upd p v0 v1)
                              (m0: Ghost.erased (map k a))
                              (key:k { Map.sel m0 key == Ghost.reveal v0 })
  : frame_preserving_upd (pointwise k p) m0 (Map.upd m0 key v1)
  = fun full_m0 ->
          let p' = pointwise k p in
          let full_v0 = Map.sel full_m0 key in
          assert (compatible (pointwise _ p) m0 full_m0);
          assert (p.refine full_v0);
          compatible_pointwise #a #k p m0 full_m0;
          assert (compatible p v0 full_v0);
          let full_v1 = f full_v0 in
          let full_m1 = Map.upd full_m0 key full_v1 in
          assert (p'.refine full_m1);
          compatible_pointwise_upd p v1 full_v1 m0 full_m0 key;
          assert (
            let m1 = Map.upd m0 key v1 in
            compatible p' m1 full_m1
          );
          lift_frame_preservation p m0 full_m0 v1 full_v1 key;
          full_m1

/// Composability in the pcm [p] is preserved pointwise
let lift_composable #k #a (p:pcm a)
                          (v0 v1:a)
                          (m0 m1:map k a)
                          (key:k)
 : Lemma (requires composable p v0 v1 /\
                   composable (pointwise k p) m0 m1)
         (ensures  composable (pointwise k p) (Map.upd m0 key v0) (Map.upd m1 key v1))
 = ()
