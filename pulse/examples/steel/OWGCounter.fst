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

#set-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --fuel 0 --ifuel 0"

let half_perm = half_perm full_perm

let fst = fst
let snd = snd

[@@ __reduce__]
let lock_inv_slprop (r:ref int) (r1 r2:ghost_ref int) (w:G.erased int & G.erased int) =
  ghost_pts_to r1 half_perm (fst w) `star`
  ghost_pts_to r2 half_perm (snd w) `star`
  pts_to r  full_perm (G.hide (fst w + snd w))

[@@ __reduce__]
let lock_inv_pred (r:ref int) (r1 r2:ghost_ref int) =
  fun (x:G.erased int & G.erased int) -> lock_inv_slprop r r1 r2 x

[@@ __reduce__]
let lock_inv (r:ref int) (r1 r2:ghost_ref int) : slprop =
  h_exists (lock_inv_pred r r1 r2)

#push-options "--warn_error -271"
let lock_inv_equiv_lemma (r:ref int) (r1 r2:ghost_ref int)
  : Lemma (lock_inv r r1 r2 `equiv` lock_inv r r2 r1)
  = let aux (r:ref int) (r1 r2:ghost_ref int) (m:mem)
      : Lemma
          (requires interp (lock_inv r r1 r2) m)
          (ensures interp (lock_inv r r2 r1) m)
          [SMTPat ()]
      = let w : G.erased (G.erased int & G.erased int) = id_elim_exists (lock_inv_pred r r1 r2) m in
        assert ((ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 pts_to r full_perm (G.hide (G.reveal (fst (snd w, fst w)) + G.reveal (snd (snd w, fst w))))) `equiv`
                (ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 pts_to r full_perm (G.hide (G.reveal (fst (snd w, fst w)) + G.reveal (snd (snd w, fst w)))))) by Steel.Memory.Tactics.canon ();

        intro_h_exists (snd w, fst w) (lock_inv_pred r r2 r1) m in
    ()
#pop-options

let og_acquire (r:ref int) (r_mine r_other:ghost_ref int) (b:bool)
  (l:lock (lock_inv r (if b then r_mine else r_other)
                      (if b then r_other else r_mine)))
  : SteelT unit
      emp
      (fun _ -> lock_inv r r_mine r_other)
  = acquire l;
    if b then begin
      change_slprop (lock_inv r (if b then r_mine else r_other)
                                (if b then r_other else r_mine))
                    (lock_inv r r_mine r_other)
                    (fun _ -> ());
      ()
    end
    else begin
      change_slprop (lock_inv r (if b then r_mine else r_other)
                                (if b then r_other else r_mine))
                    (lock_inv r r_other r_mine)
                    (fun _ -> ());
      lock_inv_equiv_lemma r r_other r_mine;
      rewrite_context #_ #(lock_inv r r_other r_mine) #(lock_inv r r_mine r_other) ()
    end

let og_release (r:ref int) (r_mine r_other:ghost_ref int) (b:bool)
  (l:lock (lock_inv r (if b then r_mine else r_other)
                      (if b then r_other else r_mine)))
  : SteelT unit
      (lock_inv r r_mine r_other)
      (fun _ -> emp)
  = if b then begin
      change_slprop (lock_inv r r_mine r_other)
                    (lock_inv r (if b then r_mine else r_other)
                                (if b then r_other else r_mine))
                    (fun _ -> ());
      ()
    end
    else begin
      lock_inv_equiv_lemma r r_mine r_other;
      rewrite_context #_ #(lock_inv r r_mine r_other) #(lock_inv r r_other r_mine) ();
      change_slprop (lock_inv r r_other r_mine)
                    (lock_inv r (if b then r_mine else r_other)
                                (if b then r_other else r_mine))
                    (fun _ -> ())
    end;
    release l

(*
 * Incrementing a ghost int
 *)
let g_incr (n:G.erased int) = G.elift1 (fun (n:int) -> n + 1) n

let incr_ctr (#v:G.erased int) (r:ref int)
  : SteelT unit
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (g_incr v))
  = let n = R.read r in
    R.write r (n+1);
    A.change_slprop (pts_to r full_perm (n + 1))
                  (pts_to r full_perm (g_incr v))
                  (fun _ -> ())

let rewrite_perm(#a:Type) (#v:G.erased a) (r:ghost_ref a) (p1 p2:P.perm)
  : Steel unit
      (ghost_pts_to r p1 v)
      (fun _ -> ghost_pts_to r p2 v)
      (fun _ -> p1 == p2)
      (fun _ _ _ -> True)
  = change_slprop (ghost_pts_to r p1 v)
                  (ghost_pts_to r p2 v)
                  (fun _ -> ())

let incr_ghost_contrib (#v1 #v2:G.erased int) (r:ghost_ref int)
  : Steel unit
      (ghost_pts_to r half_perm v1 `star`
       ghost_pts_to r half_perm v2)
      (fun _ -> ghost_pts_to r half_perm (g_incr v1) `star`
             ghost_pts_to r half_perm (g_incr v2))
      (fun _ -> True)
      (fun _ _ _ -> v1 == v2)
  = ghost_gather #_ #_ #half_perm #half_perm #v1 #v2 r;
    rewrite_perm r (sum_perm half_perm half_perm) full_perm;
    ghost_write r (g_incr v1);
    ghost_share r;
    change_slprop (ghost_pts_to r (P.half_perm P.full_perm) (g_incr v1) `star`
                   ghost_pts_to r (P.half_perm P.full_perm) (g_incr v1))
                  (ghost_pts_to r half_perm (g_incr v1) `star`
                   ghost_pts_to r half_perm (g_incr v2))
                  (fun _ -> ())

let incr (r:ref int) (r_mine r_other:ghost_ref int) (b:bool)
  (l:lock (lock_inv r (if b then r_mine else r_other)
                      (if b then r_other else r_mine)))
  (n_ghost:G.erased int)
  ()
  : SteelT unit
      (ghost_pts_to r_mine half_perm n_ghost)
      (fun _ -> ghost_pts_to r_mine half_perm (g_incr n_ghost))
  = og_acquire r r_mine r_other b l;
    let w : G.erased (G.erased int & G.erased int) = witness_h_exists () in
    incr_ctr r;
    incr_ghost_contrib #n_ghost #(fst w) r_mine;
    change_slprop (pts_to r full_perm (g_incr (G.hide (fst w + snd w))))
                  (pts_to r full_perm (G.hide (g_incr (fst w) + snd w)))
                  (fun _ -> ());
    intro_exists (g_incr (fst w), snd w) (lock_inv_pred r r_mine r_other);
    og_release r r_mine r_other b l

let incr_main (#v:G.erased int) (r:ref int)
  : SteelT unit
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (G.hide (G.reveal v + 2)))
  = //allocate the two contribution references
    let r1 = ghost_alloc (G.hide 0) in
    let r2 = ghost_alloc v in

    //split their permissions into half
    ghost_share r1;
    change_slprop (ghost_pts_to r1 (P.half_perm P.full_perm) (G.hide 0) `star`
                   ghost_pts_to r1 (P.half_perm P.full_perm) (G.hide 0))
                  (ghost_pts_to r1 half_perm (G.hide 0) `star`
                   ghost_pts_to r1 half_perm (G.hide 0))
                  (fun _ -> ());

    ghost_share r2;
    change_slprop (ghost_pts_to r2 (P.half_perm P.full_perm) v `star`
                   ghost_pts_to r2 (P.half_perm P.full_perm) v)
                  (ghost_pts_to r2 half_perm v `star`
                   ghost_pts_to r2 half_perm v)
                  (fun _ -> ());


    //rewrite the value of `r` to bring it in the shape as expected by the lock
    change_slprop (pts_to r full_perm v)
                  (pts_to r full_perm (G.hide (G.reveal (fst (G.hide 0, v)) + G.reveal (snd (G.hide 0, v)))))
                  (fun _ -> ());

    //create the lock
    intro_exists (G.hide 0, v) (lock_inv_pred r r1 r2);

    let l = new_lock (lock_inv r r1 r2) in

    let _ = par (incr r r1 r2 true  l 0)
                (incr r r2 r1 false l v) in

    //take the lock
    acquire l;

    let w = A.witness_h_exists () in

    //gather the permissions for the ghost references, and then drop them
    ghost_gather #_ #_ #_ #_ #(fst w) #_ r1;
    ghost_gather #_ #_ #_ #_ #(snd w) #_ r2;
    drop (ghost_pts_to r1 (P.sum_perm half_perm half_perm) (fst w));
    drop (ghost_pts_to r2 (P.sum_perm half_perm half_perm) (snd w));

    change_slprop (pts_to r full_perm (G.hide (G.reveal (fst w) + G.reveal (snd w))))
                  (pts_to r full_perm (v + 2))
                  (fun _ -> ())
