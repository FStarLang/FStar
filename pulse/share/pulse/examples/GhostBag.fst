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

let perm0 = r:real{r >=. 0.0R}
type map (a:eqtype) = m:Map.t a perm0 { forall (x:a). Map.contains m x }

//
// P represents the partial knowledge of the set membership
//   i.e. x and y may be in the set, but P may only know about x or y
// F represents the full knowledge, but not full permissions
//   (the permissions may be distributed in P frames)
//   so if x and y are in the set, F will map x and y to non-zero permissions
//
noeq
type gbag_pcm_carrier (a:eqtype) =
  | P : map a -> gbag_pcm_carrier a
  | F : map a -> gbag_pcm_carrier a

let gbag_equal #a (m1 m2 : gbag_pcm_carrier a) : Tot prop =
  match m1, m2 with
  | P m1', P m2' -> Map.equal m1' m2'
  | F m1', F m2' -> Map.equal m1' m2'
  | _, _ -> False

let lemma_elim_gbag_equal #a (m1 m2 : gbag_pcm_carrier a)
  : Lemma (requires gbag_equal m1 m2) (ensures m1 == m2) [SMTPat (gbag_equal m1 m2)]
  = ()

let gbag_pcm_composable #a : symrel (gbag_pcm_carrier a) =
  fun x y ->
  match x, y with
  | P m1, P m2 ->
    forall (x:a).
      (Map.sel m1 x == 0.0R) \/
      (Map.sel m2 x == 0.0R) \/
      (Map.sel m1 x +. Map.sel m2 x) <=. 1.0R

  | F m1, P m2
  | P m2, F m1 ->
    forall (x:a).
      (Map.sel m2 x == 0.0R) \/
      (Map.sel m1 x >. 0.0R /\ Map.sel m1 x +. Map.sel m2 x <=. 1.0R)

  | _ -> False

let op_maps #a (m1:map a) (m2:map a) : map a =
  Map.map_literal #a #perm0 (fun x ->
    Map.sel m1 x +. Map.sel m2 x
  )

let gbag_pcm_op #a (x:gbag_pcm_carrier a) (y:gbag_pcm_carrier a { gbag_pcm_composable x y })
  : gbag_pcm_carrier a =

  match x, y with
  | P m1, P m2 -> P (op_maps m1 m2)
  | F m1, P m2
  | P m1, F m2 -> F (op_maps m1 m2)

let gbag_pcm_one #a : gbag_pcm_carrier a = P (Map.const 0.0R)

let gbag_pcm' a : pcm' (gbag_pcm_carrier a) =
  {
    composable = gbag_pcm_composable;
    op = gbag_pcm_op;
    one = gbag_pcm_one;
  }

let gbag_pcm_commutative a : lem_commutative (gbag_pcm' a) =
  fun m1 m2 ->
    assert (gbag_equal (gbag_pcm_op m1 m2) (gbag_pcm_op m2 m1))

#push-options "--split_queries always --z3rlimit 20"
let gbag_pcm_assoc_l a : lem_assoc_l (gbag_pcm' a) =
  fun x y z ->
    match x, y, z with
    | P m1, P m2, P m3
    | F m1, P m2, P m3
    | P m1, F m2, P m3
    | P m1, P m2, F m3 ->
      assert (gbag_pcm_composable x y);
      assert (gbag_pcm_composable (gbag_pcm_op x y) z);
      assert (gbag_pcm_op x (gbag_pcm_op y z) `gbag_equal` gbag_pcm_op (gbag_pcm_op x y) z);
      ()
    | _ -> assert False

let gbag_pcm_assoc_r a : lem_assoc_r (gbag_pcm' a) =
  fun x y z ->
    match x, y, z with
    | P m1, P m2, P m3
    | F m1, P m2, P m3
    | P m1, F m2, P m3
    | P m1, P m2, F m3 ->
      assert (gbag_pcm_composable y z);
      assert (gbag_pcm_composable x (gbag_pcm_op y z));
      assert (gbag_pcm_op x (gbag_pcm_op y z) `gbag_equal` gbag_pcm_op (gbag_pcm_op x y) z);
      ()
    | _ -> assert False
#pop-options

let gbag_pcm_is_unit a : lem_is_unit (gbag_pcm' a) =
  let p = gbag_pcm' a in
  fun x ->
  assert (p.composable x p.one);
  assert (p.op x p.one `gbag_equal` x);
  ()

let gbag_pcm a : pcm (gbag_pcm_carrier a) = {
  p = gbag_pcm' a;
  comm = gbag_pcm_commutative a;
  assoc = gbag_pcm_assoc_l a;
  assoc_r = gbag_pcm_assoc_r a;
  is_unit = gbag_pcm_is_unit a;
  refine = (fun _ -> True)
}

let fp_upd_add #a
  (m:map a)
  (x:a { Map.sel m x == 0.0R })
  : frame_preserving_upd (gbag_pcm a) (F m) (F (Map.upd m x 1.0R)) =

  fun v ->
  let F mv = v in
  let v_new = F (Map.upd mv x 1.0R) in

  eliminate exists (frame:gbag_pcm_carrier a). composable (gbag_pcm a) (F m) frame /\
                                               op (gbag_pcm a) frame (F m) == v
  returns compatible (gbag_pcm a) (F (Map.upd m x 1.0R)) v_new
  with _. (match frame with
           | P m_frame
           | F m_frame ->
             assert (Map.equal (op_maps m_frame (Map.upd m x 1.0R))
                               (Map.upd mv x 1.0R)));

  let aux (frame:gbag_pcm_carrier a)
    : Lemma
      (requires
         gbag_pcm_composable (F m) frame /\
         gbag_pcm_op (F m) frame == v)
      (ensures
         gbag_pcm_composable (F (Map.upd m x 1.0R)) frame /\
         gbag_pcm_op (F (Map.upd m x 1.0R)) frame == v_new)
      [SMTPat ()] =

      match frame with
      | P m_frame
      | F m_frame ->
        assert (Map.equal (op_maps (Map.upd m x 1.0R) m_frame)
                          (Map.upd mv x 1.0R));
        ()
  in

  v_new


let fp_upd_rem #a
  (m:map a)
  (x:a { Map.sel m x == 1.0R })
  : frame_preserving_upd (gbag_pcm a) (F m) (F (Map.upd m x 0.0R)) =

  fun v ->
  let F mv = v in
  let v_new = F (Map.upd mv x 0.0R) in

  eliminate exists (frame:gbag_pcm_carrier a). composable (gbag_pcm a) (F m) frame /\
                                               op (gbag_pcm a) frame (F m) == v
  returns compatible (gbag_pcm a) (F (Map.upd m x 0.0R)) v_new
  with _. (match frame with
           | P m_frame
           | F m_frame ->
             assert (Map.equal (op_maps m_frame (Map.upd m x 0.0R))
                               (Map.upd mv x 0.0R));
             assert (composable (gbag_pcm a) (F (Map.upd m x 0.0R)) frame));

  let aux (frame:gbag_pcm_carrier a)
    : Lemma
      (requires
         gbag_pcm_composable (F m) frame /\
         gbag_pcm_op (F m) frame == v)
      (ensures
         gbag_pcm_composable (F (Map.upd m x 0.0R)) frame /\
         gbag_pcm_op (F (Map.upd m x 0.0R)) frame == v_new)
      [SMTPat ()] =

      match frame with
      | P m_frame
      | F m_frame ->
        assert (Map.equal (op_maps (Map.upd m x 0.0R) m_frame)
                          (Map.upd mv x 0.0R));
        ()
  in

  v_new

module GR = Pulse.Lib.GhostPCMReference

let gbag #a (r:GR.gref (gbag_pcm a)) (s:Set.set a) : slprop =
  exists* (m:map a).
          GR.pts_to r (F m) **
          (pure (forall (x:a). (~ (Set.mem x s)) ==> Map.sel m x == 0.0R)) **
          (pure (forall (x:a). Set.mem x s ==> Map.sel m x == 0.5R))

let gbagh #a (r:GR.gref (gbag_pcm a)) (x:a) : slprop =
  GR.pts_to r (P (Map.upd (Map.const 0.0R) x 0.5R))



ghost
fn gbag_create (a:eqtype)
  requires emp
  returns r:GR.gref (gbag_pcm a)
  ensures gbag r Set.empty
{
  let r = GR.alloc #_ #(gbag_pcm a) (F (Map.const 0.0R));
  with _m. rewrite (GR.pts_to r (Ghost.reveal (Ghost.hide _m))) as
                   (GR.pts_to r _m);
  fold (gbag r Set.empty);
  r
}



#set-options "--split_queries always --debug SMTFail"


ghost
fn gbag_add #a (r:GR.gref (gbag_pcm a)) (s:Set.set a) (x:a)
  requires gbag r s **
           pure (~ (Set.mem x s))
  ensures gbag r (Set.add x s) **
          gbagh r x
{
  unfold gbag;
  with mf. assert (GR.pts_to r (F mf));
  GR.write r (F mf) (F (Map.upd mf x 1.0R)) (fp_upd_add mf x);
  assert (pure (Map.equal (Map.upd mf x 1.0R)
                          (op_maps (Map.upd mf x 0.5R)
                                   (Map.upd (Map.const #a #perm0 0.0R) x 0.5R))));
  rewrite (GR.pts_to r (F (Map.upd mf x 1.0R))) as
          (GR.pts_to r (op (gbag_pcm a)
                              (F (Map.upd mf x 0.5R))
                              (P (Map.upd (Map.const #a #perm0 0.0R) x 0.5R))));
  GR.share r (F (Map.upd mf x 0.5R))
                (P (Map.upd (Map.const #a #perm0 0.0R) x 0.5R));
  fold (gbag r (Set.add x s));
  with _v. rewrite (GR.pts_to r (Ghost.reveal (Ghost.hide _v))) as
                   (gbagh r x)
}



ghost
fn gbag_remove #a (r:GR.gref (gbag_pcm a)) (s:Set.set a) (x:a)
  requires gbag r s **
           gbagh r x
  ensures gbag r (Set.remove x s) **
          pure (x `Set.mem` s)
{
  unfold gbag;
  with mf. assert (GR.pts_to r (F mf));
  unfold gbagh;
  let mp = Map.upd (Map.const #_ #perm0 0.0R) x 0.5R;
  with _m. rewrite (GR.pts_to r (P _m)) as
                   (GR.pts_to r (P mp));
  GR.gather r (F mf) (P mp);
  assert (pure (x `Set.mem` s));
  let mop = op_maps mf mp;
  GR.write r (F mop) (F (Map.upd mop x 0.0R)) (fp_upd_rem mop x);
  fold (gbag r (Set.remove x s))
}

