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

(*
 * An implementation of the parallel counter presented by Owicki and Gries
 * "Verifying properties of parallel programs: An axiomatic approach.", CACM'76
 *
 * In this example, the main thread forks two worker thread that both
 *   increment a shared counter. The goal of the example is to show that
 *   after both the worker threads are done, the value of the counter is
 *   its original value + 2.
 *
 * See http://pm.inf.ethz.ch/publications/getpdf.php for an implementation
 *   of the OWG counters in the Chalice framework.
 *)

module OWGCounter

module G = FStar.Ghost

open Steel.Memory
open Steel.FractionalPermission
open Steel.Reference
open Steel.SpinLock

open Steel.Effect.Atomic
open Steel.Effect

module R = Steel.Reference
module P = Steel.FractionalPermission
module A = Steel.Effect.Atomic

#set-options "--ide_id_info_off --using_facts_from '* -FStar.Tactics -FStar.Reflection' --fuel 0 --ifuel 0"

let half_perm = half_perm full_perm

(* Some basic wrappers to avoid issues with normalization.
   TODO: The frame inference tactic should not normalize fst and snd*)

noextract
let fst = fst

noextract
let snd = snd


/// The core invariant of the Owicki-Gries counter, shared by the two parties.
/// The concrete counter [r] is shared, and the full permission is stored in the invariant.
/// Each party also has half permission to their own ghost counter [r1] or [r2], ensuring that
/// only them can modify it by retrieving the other half of the permission when accessing the invariant.
/// The `__reduce__` attribute indicates the frame inference tactic to unfold this predicate for frame inference only
[@@ __reduce__]
let lock_inv_slprop (r:ref int) (r1 r2:ghost_ref int) (w:G.erased int & G.erased int) =
  ghost_pts_to r1 half_perm (fst w) `star`
  ghost_pts_to r2 half_perm (snd w) `star`
  pts_to r full_perm (G.hide (fst w + snd w))

[@@ __reduce__]
let lock_inv_pred (r:ref int) (r1 r2:ghost_ref int) =
  fun (x:G.erased int & G.erased int) -> lock_inv_slprop r r1 r2 x

/// The actual invariant, existentially quantifying over the values currently stored in the two ghost references
[@@ __reduce__]
let lock_inv (r:ref int) (r1 r2:ghost_ref int) : vprop =
  h_exists (lock_inv_pred r r1 r2)


#push-options "--warn_error -271 --fuel 1 --ifuel 1"
/// A helper lemma to reason about the lock invariant
let lock_inv_equiv_lemma (r:ref int) (r1 r2:ghost_ref int)
  : Lemma (lock_inv r r1 r2 `equiv` lock_inv r r2 r1)
  =
  let aux (r:ref int) (r1 r2:ghost_ref int) (m:mem)
      : Lemma
          (requires interp (hp_of (lock_inv r r1 r2)) m)
          (ensures interp (hp_of (lock_inv r r2 r1)) m)
          [SMTPat ()]
      = assert (
          Steel.Memory.h_exists #(G.erased int & G.erased int) (fun x -> hp_of (lock_inv_pred r r1 r2 x)) ==
          h_exists_sl #(G.erased int & G.erased int) (lock_inv_pred r r1 r2))
          by (FStar.Tactics.norm [delta_only [`%h_exists_sl]]);

        let w : G.erased (G.erased int & G.erased int) = id_elim_exists (fun x -> hp_of (lock_inv_pred r r1 r2 x)) m in
        assert ((ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 pts_to r full_perm (G.hide (G.reveal (fst (snd w, fst w)) + G.reveal (snd (snd w, fst w))))) `equiv`
                (ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 pts_to r full_perm (G.hide (G.reveal (fst (snd w, fst w)) + G.reveal (snd (snd w, fst w)))))) by (FStar.Tactics.norm [delta_attr [`%__steel_reduce__]]; canon' false (`true_p) (`true_p));

        reveal_equiv
          (ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 pts_to r full_perm (G.hide (G.reveal (fst (snd w, fst w)) + G.reveal (snd (snd w, fst w)))))
          (ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 pts_to r full_perm (G.hide (G.reveal (fst (snd w, fst w)) + G.reveal (snd (snd w, fst w)))));

        assert (interp (hp_of (lock_inv_pred r r2 r1 (snd w, fst w))) m);

        intro_h_exists (snd w, fst w) (fun x -> hp_of (lock_inv_pred r r2 r1 x)) m;
        assert (interp (Steel.Memory.h_exists (fun x -> hp_of (lock_inv_pred r r2 r1 x))) m);

       assert (
          Steel.Memory.h_exists #(G.erased int & G.erased int) (fun x -> hp_of (lock_inv_pred r r2 r1 x)) ==
          h_exists_sl #(G.erased int & G.erased int) (lock_inv_pred r r2 r1))
          by (FStar.Tactics.norm [delta_only [`%h_exists_sl]]) in

  reveal_equiv (lock_inv r r1 r2) (lock_inv r r2 r1)
#pop-options

/// Acquiring the shared lock invariant
inline_for_extraction noextract
let og_acquire (r:ref int) (r_mine r_other:ghost_ref int) (b:G.erased bool)
  (l:lock (lock_inv r (if b then r_mine else r_other)
                      (if b then r_other else r_mine)))
  : SteelT unit
      emp
      (fun _ -> lock_inv r r_mine r_other)
  = acquire l;
    if b then begin
      rewrite_slprop (lock_inv r (if b then r_mine else r_other)
                                (if b then r_other else r_mine))
                    (lock_inv r r_mine r_other)
                    (fun _ -> ());
      ()
    end
    else begin
      rewrite_slprop (lock_inv r (if b then r_mine else r_other)
                                (if b then r_other else r_mine))
                    (lock_inv r r_other r_mine)
                    (fun _ -> ());
      lock_inv_equiv_lemma r r_other r_mine;
      rewrite_slprop (lock_inv r r_other r_mine) (lock_inv r r_mine r_other) (fun _ -> reveal_equiv (lock_inv r r_other r_mine) (lock_inv r r_mine r_other))
    end

/// Releasing the shared lock invariant
inline_for_extraction noextract
let og_release (r:ref int) (r_mine r_other:ghost_ref int) (b:G.erased bool)
  (l:lock (lock_inv r (if b then r_mine else r_other)
                      (if b then r_other else r_mine)))
  : SteelT unit
      (lock_inv r r_mine r_other)
      (fun _ -> emp)
  = if b then begin
      rewrite_slprop (lock_inv r r_mine r_other)
                    (lock_inv r (if b then r_mine else r_other)
                                (if b then r_other else r_mine))
                    (fun _ -> ());
      ()
    end
    else begin
      lock_inv_equiv_lemma r r_mine r_other;
      rewrite_slprop (lock_inv r r_mine r_other) (lock_inv r r_other r_mine) (fun _ -> reveal_equiv (lock_inv r r_mine r_other) (lock_inv r r_other r_mine));
      rewrite_slprop (lock_inv r r_other r_mine)
                    (lock_inv r (if b then r_mine else r_other)
                                (if b then r_other else r_mine))
                    (fun _ -> ())
    end;
    release l

(*
 * Incrementing a ghost int
 *)
let g_incr (n:G.erased int) = G.elift1 (fun (n:int) -> n + 1) n

inline_for_extraction noextract
let incr_ctr (#v:G.erased int) (r:ref int)
  : SteelT unit
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (g_incr v))
  = let n = R.read_pt r in
    R.write_pt r (n+1);
    rewrite_slprop (pts_to r full_perm (n + 1))
                  (pts_to r full_perm (g_incr v))
                  (fun _ -> ())

inline_for_extraction noextract
let rewrite_perm(#a:Type) (#v:G.erased a) (r:ghost_ref a) (p1 p2:P.perm)
  : Steel unit
      (ghost_pts_to r p1 v)
      (fun _ -> ghost_pts_to r p2 v)
      (fun _ -> p1 == p2)
      (fun _ _ _ -> True)
  = rewrite_slprop (ghost_pts_to r p1 v)
                  (ghost_pts_to r p2 v)
                  (fun _ -> ())

inline_for_extraction noextract
let incr_ghost_contrib (#v1 #v2:G.erased int) (r:ghost_ref int)
  : Steel unit
      (ghost_pts_to r half_perm v1 `star`
       ghost_pts_to r half_perm v2)
      (fun _ -> ghost_pts_to r half_perm (g_incr v1) `star`
             ghost_pts_to r half_perm (g_incr v2))
      (fun _ -> True)
      (fun _ _ _ -> v1 == v2)
  = ghost_gather_pt #_ #_ #half_perm #half_perm #v1 #v2 r;
    rewrite_perm r (sum_perm half_perm half_perm) full_perm;
    ghost_write_pt r (g_incr v1);
    ghost_share_pt r;
    rewrite_slprop (ghost_pts_to r (P.half_perm P.full_perm) (g_incr v1) `star`
                   ghost_pts_to r (P.half_perm P.full_perm) (g_incr v1))
                  (ghost_pts_to r half_perm (g_incr v1) `star`
                   ghost_pts_to r half_perm (g_incr v2))
                  (fun _ -> ())

let incr (r:ref int) (r_mine r_other:ghost_ref int) (b:G.erased bool)
  (l:lock (lock_inv r (if b then r_mine else r_other)
                      (if b then r_other else r_mine)))
  (n_ghost:G.erased int)
  ()
  : SteelT unit
      (ghost_pts_to r_mine half_perm n_ghost)
      (fun _ -> ghost_pts_to r_mine half_perm (g_incr n_ghost))
  = og_acquire r r_mine r_other b l;
    let w : G.erased (G.erased int & G.erased int) = witness_exists () in
    incr_ctr r;
    incr_ghost_contrib #n_ghost #(fst w) r_mine;
    rewrite_slprop (pts_to r full_perm (g_incr (G.hide (fst w + snd w))))
                  (pts_to r full_perm (G.hide (g_incr (fst w) + snd w)))
                  (fun _ -> ());
    intro_exists (g_incr (fst w), snd w) (lock_inv_pred r r_mine r_other);
    og_release r r_mine r_other b l

let incr_main (#v:G.erased int) (r:ref int)
  : SteelT unit
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (G.hide (G.reveal v + 2)))
  = //allocate the two contribution references
    let r1 = ghost_alloc_pt (G.hide 0) in
    let r2 = ghost_alloc_pt v in

    //split their permissions into half
    ghost_share_pt r1;
    rewrite_slprop (ghost_pts_to r1 (P.half_perm P.full_perm) (G.hide 0) `star`
                   ghost_pts_to r1 (P.half_perm P.full_perm) (G.hide 0))
                  (ghost_pts_to r1 half_perm (G.hide 0) `star`
                   ghost_pts_to r1 half_perm (G.hide 0))
                  (fun _ -> ());

    ghost_share_pt r2;
    rewrite_slprop (ghost_pts_to r2 (P.half_perm P.full_perm) v `star`
                   ghost_pts_to r2 (P.half_perm P.full_perm) v)
                  (ghost_pts_to r2 half_perm v `star`
                   ghost_pts_to r2 half_perm v)
                  (fun _ -> ());


    //rewrite the value of `r` to bring it in the shape as expected by the lock
    rewrite_slprop (pts_to r full_perm v)
                  (pts_to r full_perm (G.hide (G.reveal (fst (G.hide 0, v)) + G.reveal (snd (G.hide 0, v)))))
                  (fun _ -> ());

    //create the lock
    intro_exists (G.hide 0, v) (lock_inv_pred r r1 r2);

    let l = new_lock (lock_inv r r1 r2) in

    let _ = par (incr r r1 r2 true  l 0)
                (incr r r2 r1 false l v) in

    //take the lock
    acquire l;

    let w = witness_exists () in

    //gather the permissions for the ghost references, and then drop them
    ghost_gather_pt #_ #_ #_ #_ #(fst w) #_ r1;
    ghost_gather_pt #_ #_ #_ #_ #(snd w) #_ r2;
    drop (ghost_pts_to r1 (P.sum_perm half_perm half_perm) (fst w));
    drop (ghost_pts_to r2 (P.sum_perm half_perm half_perm) (snd w));

    rewrite_slprop (pts_to r full_perm (G.hide (G.reveal (fst w) + G.reveal (snd w))))
                  (pts_to r full_perm (v + 2))
                  (fun _ -> ())
