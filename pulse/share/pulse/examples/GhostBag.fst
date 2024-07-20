(*
   Copyright 2023 Microsoft Research

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

module GhostBag
#lang-pulse

//
// This module implements the ghost bag data structure from
#lang-pulse
//   Expressive modular fine-grained concurrency specification, POPL 2011 (Sec. 6)
//
//
// It provides the following interface:
//
// 1. { emp } gbag_create () { r. gbag (r, Set.empty) }
//
// 2. { gbag (r, S) ** pure (x \notin S) }
//      gbag_add (r, S, x)
//    { gbag (r, Set.add x S) ** gbagh (r, x) }
//
// 3. { gbag (r, S) ** gbagh (r, x) }
//      gbag_remove (r, S, x)
//    { gbag (r, Set.remove x S) ** pure (x \in S) }
//

open FStar.PCM
open Pulse.Lib.Pervasives

type map (a:eqtype) = m:Map.t a (option perm) { forall (x:a). Map.contains m x }

//
// P represents the partial knowledge of the set membership
//   i.e. x and y may be in the set, but P may only know about x or y
// F represents the full knowledge, but not full permissions
//   (the permissions may be distributed in P frames)
//   so if x and y are in the set, F will map x and y to non-zero permissions
//
noeq
type gbag_pcm_carrier (a:eqtype) : Type u#1 =
  | P : map a -> gbag_pcm_carrier a
  | F : map a -> gbag_pcm_carrier a

let gbag_pcm_composable #a : symrel (gbag_pcm_carrier a) =
  fun x y ->
  match x, y with
  | P m1, P m2 ->
    forall (x:a).
    (Map.sel m1 x == None) \/
    (Map.sel m2 x == None) \/
    ((Some?.v (Map.sel m1 x)) +. (Some?.v ((Map.sel m2 x)))) <=. 1.0R
  
  | F m1, P m2
  | P m2, F m1 ->
    forall (x:a).
    (Map.sel m2 x == None) \/
    (Some? (Map.sel m1 x) /\ ((Some?.v (Map.sel m1 x)) +. (Some?.v ((Map.sel m2 x)))) <=. 1.0R)

  | _ -> False

let op_maps #a (m1:map a) (m2:map a) : map a =
  Map.map_literal #a #(option perm) (fun x ->
    match Map.sel m1 x, Map.sel m2 x with
    | None, None -> None
    | Some p, None -> Some p
    | None, Some p -> Some p
    | Some p1, Some p2 ->
      Some (p1 +. p2)
  )

let gbag_pcm_op #a (x:gbag_pcm_carrier a) (y:gbag_pcm_carrier a { gbag_pcm_composable x y })
  : gbag_pcm_carrier a =

  match x, y with
  | P m1, P m2 -> P (op_maps m1 m2)
  | F m1, P m2
  | P m1, F m2 -> F (op_maps m1 m2)

let gbag_pcm_one #a : gbag_pcm_carrier a = P (Map.const None)

let gbag_pcm' a : pcm' (gbag_pcm_carrier a) =
  {
    composable = gbag_pcm_composable;
    op = gbag_pcm_op;
    one = gbag_pcm_one;
  }

#push-options "--warn_error -271"
let op_maps_comm a
  : m1:map a -> m2:map a -> Lemma (op_maps m1 m2 == op_maps m2 m1) [SMTPat ()] =
  fun m1 m2 ->
  assert (Map.equal (op_maps m1 m2) (op_maps m2 m1))

let op_maps_assoc_l a
  : m1:map a -> m2:map a -> m3:map a ->
    Lemma (op_maps m1 (op_maps m2 m3) == op_maps (op_maps m1 m2) m3) [SMTPat ()] =
  fun m1 m2 m3 ->
  assert (Map.equal (op_maps m1 (op_maps m2 m3)) (op_maps (op_maps m1 m2) m3))

let op_maps_assoc_r a
  : m1:map a -> m2:map a -> m3:map a ->
    Lemma (op_maps m1 (op_maps m2 m3) == op_maps (op_maps m1 m2) m3) [SMTPat ()] =
  fun m1 m2 m3 ->
  assert (Map.equal (op_maps m1 (op_maps m2 m3)) (op_maps (op_maps m1 m2) m3))

let gbag_pcm_commutative a : lem_commutative (gbag_pcm' a) =
  let _ = op_maps_comm a in
  fun _ _ -> ()

#restart-solver
#push-options "--z3rlimit_factor 20 --fuel 0 --ifuel 1 --split_queries no"
let gbag_pcm_assoc_l a : lem_assoc_l (gbag_pcm' a) =
  let _ = op_maps_comm a in
  let _ = op_maps_assoc_l a in
  let _ = op_maps_assoc_r a in
  fun _ _ _ -> ()

let gbag_pcm_assoc_r a : lem_assoc_r (gbag_pcm' a) =
  let _ = op_maps_comm a in
  let _ = op_maps_assoc_l a in
  let _ = op_maps_assoc_r a in
  fun _ _ _ -> ()

let gbag_pcm_is_unit a : lem_is_unit (gbag_pcm' a) =
  let p = gbag_pcm' a in
  fun x ->
  assert (p.composable x p.one);
  match x with
  | P m ->
    assert (Map.equal (op_maps m (Map.const None)) m)
  | F m ->
    assert (Map.equal (op_maps m (Map.const None)) m)

let gbag_pcm a : pcm (gbag_pcm_carrier a) = {
  p = gbag_pcm' a;
  comm = gbag_pcm_commutative a;
  assoc = gbag_pcm_assoc_l a;
  assoc_r = gbag_pcm_assoc_r a;
  is_unit = gbag_pcm_is_unit a;
  refine = (fun _ -> True)
}
#pop-options
#pop-options

#restart-solver
#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1 --split_queries no --warn_error -271"
let fp_upd_add #a
  (m:map a)
  (x:a { Map.sel m x == None })
  : frame_preserving_upd (gbag_pcm a) (F m) (F (Map.upd m x (Some 1.0R))) =

  fun v ->
  let F mv = v in
  let v_new = F (Map.upd mv x (Some 1.0R)) in

  eliminate exists (frame:gbag_pcm_carrier a). composable (gbag_pcm a) (F m) frame /\
                                               op (gbag_pcm a) frame (F m) == v
  returns compatible (gbag_pcm a) (F (Map.upd m x (Some 1.0R))) v_new
  with _. (match frame with
           | P m_frame
           | F m_frame ->
             assert (Map.equal (op_maps m_frame (Map.upd m x (Some 1.0R)))
                               (Map.upd mv x (Some 1.0R))));

  let aux (frame:gbag_pcm_carrier a)
    : Lemma
      (requires
         gbag_pcm_composable (F m) frame /\
         gbag_pcm_op (F m) frame == v)
      (ensures
         gbag_pcm_composable (F (Map.upd m x (Some 1.0R))) frame /\
         gbag_pcm_op (F (Map.upd m x (Some 1.0R))) frame == v_new)
      [SMTPat ()] =

      match frame with
      | P m_frame
      | F m_frame ->
        assert (Map.equal (op_maps (Map.upd m x (Some 1.0R)) m_frame)
                          (Map.upd mv x (Some 1.0R)));
        ()
  in

  v_new


let fp_upd_rem #a
  (m:map a)
  (x:a { Map.sel m x == Some 1.0R })
  : frame_preserving_upd (gbag_pcm a) (F m) (F (Map.upd m x None)) =

  fun v ->
  let F mv = v in
  let v_new = F (Map.upd mv x None) in

  eliminate exists (frame:gbag_pcm_carrier a). composable (gbag_pcm a) (F m) frame /\
                                               op (gbag_pcm a) frame (F m) == v
  returns compatible (gbag_pcm a) (F (Map.upd m x None)) v_new
  with _. (match frame with
           | P m_frame
           | F m_frame ->
             assert (Map.equal (op_maps m_frame (Map.upd m x None))
                               (Map.upd mv x None));
             assert (composable (gbag_pcm a) (F (Map.upd m x None)) frame));

  let aux (frame:gbag_pcm_carrier a)
    : Lemma
      (requires
         gbag_pcm_composable (F m) frame /\
         gbag_pcm_op (F m) frame == v)
      (ensures
         gbag_pcm_composable (F (Map.upd m x None)) frame /\
         gbag_pcm_op (F (Map.upd m x None)) frame == v_new)
      [SMTPat ()] =

      match frame with
      | P m_frame
      | F m_frame ->
        assert (Map.equal (op_maps (Map.upd m x None) m_frame)
                          (Map.upd mv x None));
        ()
  in

  v_new
#pop-options

let gbag #a (r:ghost_pcm_ref (gbag_pcm a)) (s:Set.set a) : slprop =
  exists* (m:map a).
          ghost_pcm_pts_to r (F m) **
          (pure (forall (x:a). (~ (Set.mem x s)) ==> Map.sel m x == None)) **
          (pure (forall (x:a). Set.mem x s ==> Map.sel m x == Some 0.5R))

let gbagh #a (r:ghost_pcm_ref (gbag_pcm a)) (x:a) : slprop =
  ghost_pcm_pts_to r (P (Map.upd (Map.const None) x (Some 0.5R)))



ghost
fn gbag_create (a:eqtype)
  requires emp
  returns r:ghost_pcm_ref (gbag_pcm a)
  ensures gbag r Set.empty
{
  let r = ghost_alloc #_ #(gbag_pcm a) (F (Map.const None));
  with _m. rewrite (ghost_pcm_pts_to r (Ghost.reveal (Ghost.hide _m))) as
                   (ghost_pcm_pts_to r _m);
  fold (gbag r Set.empty);
  r
}



ghost
fn gbag_add #a (r:ghost_pcm_ref (gbag_pcm a)) (s:Set.set a) (x:a)
  requires gbag r s **
           pure (~ (Set.mem x s))
  ensures gbag r (Set.add x s) **
          gbagh r x
{
  unfold gbag;
  with mf. assert (ghost_pcm_pts_to r (F mf));
  ghost_write r (F mf) (F (Map.upd mf x (Some 1.0R))) (fp_upd_add mf x);
  assert (pure (Map.equal (Map.upd mf x (Some 1.0R))
                          (op_maps (Map.upd mf x (Some 0.5R))
                                   (Map.upd (Map.const None) x (Some 0.5R)))));
  rewrite (ghost_pcm_pts_to r (F (Map.upd mf x (Some 1.0R)))) as
          (ghost_pcm_pts_to r (op (gbag_pcm a)
                              (F (Map.upd mf x (Some 0.5R)))
                              (P (Map.upd (Map.const None) x (Some 0.5R)))));
  ghost_share r (F (Map.upd mf x (Some 0.5R)))
                (P (Map.upd (Map.const None) x (Some 0.5R)));
  fold (gbag r (Set.add x s));
  with _v. rewrite (ghost_pcm_pts_to r (Ghost.reveal (Ghost.hide _v))) as
                   (gbagh r x)
}



ghost
fn gbag_remove #a (r:ghost_pcm_ref (gbag_pcm a)) (s:Set.set a) (x:a)
  requires gbag r s **
           gbagh r x
  ensures gbag r (Set.remove x s) **
          pure (x `Set.mem` s)
{
  unfold gbag;
  with mf. assert (ghost_pcm_pts_to r (F mf));
  unfold gbagh;
  let mp = Map.upd (Map.const #_ #(option perm) None) x (Some 0.5R);
  with _m. rewrite (ghost_pcm_pts_to r (P _m)) as
                   (ghost_pcm_pts_to r (P mp));
  ghost_gather r (F mf) (P mp);
  assert (pure (x `Set.mem` s));
  let mop = op_maps mf mp;
  ghost_write r (F mop) (F (Map.upd mop x None)) (fp_upd_rem mop x);
  fold (gbag r (Set.remove x s))
}

