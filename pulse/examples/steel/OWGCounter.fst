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

let half_perm = half_perm (MkPerm 1.0R)

let fst = fst
let snd = snd


(*
 * The shared threads use a lock to synchronize on the counter.
 * The lock holds full permission for the counter,
 *   and half permission for each of the two contribution (ghost) references
 * It provides the crucial invariant that the value of the counter is the
 *   sum of the values of the contribution references
 *
 * `lock_inv_pred` is the predicate for the h_exists lock invariant
 *)

//the __reduce__ keyword is a hint to the framing tactic to unfold this defn.
[@@ __reduce__]
let lock_inv_pred (r:ref int) (r1 r2:ref (G.erased int)) =
  fun (x:G.erased int & G.erased int) ->
    pts_to r1 half_perm (G.hide (fst x)) `star`
    pts_to r2 half_perm (G.hide (snd x)) `star`
    pts_to r  full_perm (G.hide (fst x + snd x))


(*
 * The lock invariant is an existential
 *)
[@@ __reduce__]
let lock_inv (r:ref int) (r1 r2:ref (G.erased int)) : slprop =
  h_exists (lock_inv_pred r r1 r2)

(*
 * A specialization of change_slprop to rewrite permissions
 *)
let rewrite_perm(#a:Type) (#v:G.erased a) (r:ref a) (p1 p2:P.perm)
  : Steel unit
      (pts_to r p1 v)
      (fun _ -> pts_to r p2 v)
      (fun _ -> p1 == p2)
      (fun _ _ _ -> True)
  = change_slprop (pts_to r p1 v)
                  (pts_to r p2 v)
                  (fun _ -> ())

(*
 * Incrementing a ghost int
 *)
let g_incr (n:G.erased int) = G.elift1 (fun (n:int) -> n + 1) n

(*
 * Auxiliary function to increment the counter
 *)
let incr_ctr (#v:G.erased int) (r:ref int)
  : SteelT unit
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (g_incr v))
  = let n = R.read r in
    R.write r (n+1);
    A.change_slprop (pts_to r full_perm (n + 1))
                  (pts_to r full_perm (g_incr v))
                  (fun _ -> ())

(*
 * Auxiliary function to increment a ghost contribution reference
 *
 * The caller provides two split permissions pointing to v1 and v2
 *
 * And it returns two split permissions, both pointing to (v1+1)
 *   with a squash proof that v1 == v2
 *)
let incr_ghost_contrib (#v1 #v2:G.erased int) (r:ref (G.erased int))
  : Steel unit
      (pts_to r half_perm (G.hide v1) `star`
       pts_to r half_perm (G.hide v2))
      (fun _ -> pts_to r half_perm (G.hide (g_incr v1)) `star`
             pts_to r half_perm (G.hide (g_incr v1)))
      (fun _ -> True)
      (fun _ _ _ -> v1 == v2)
  = R.gather_atomic #_ #_ #half_perm #half_perm #(G.hide v1) #(G.hide v2) r;
    rewrite_perm r (sum_perm half_perm half_perm) full_perm;
    R.write r (g_incr v1);
    R.share_atomic r;
    change_slprop (pts_to r (P.half_perm P.full_perm) (G.hide (g_incr v1)) `star`
                   pts_to r (P.half_perm P.full_perm) (G.hide (g_incr v1)))
                  (pts_to r half_perm (G.hide (g_incr v1)) `star`
                   pts_to r half_perm (G.hide (g_incr v1)))
                  (fun _ -> ())

(*
 * The incr function (that the worker threads will use) is parametrized
 *   with a boolean, to indicate which contribution ref (r1 or r2) it should
 *   increment.
 *
 * `incr_slprop` is the slprop that's conditional on b
 *)
[@@ __reduce__]
let incr_slprop (r1 r2:ref (G.erased int)) (n:G.erased int) (b:bool) : slprop =
  if b then pts_to r1 half_perm (G.hide n)
       else pts_to r2 half_perm (G.hide n)

(*
 * `incr` function to be called by the worker threads
 *)
let incr (r:ref int) (r1 r2:ref (G.erased int))
  (l:lock (lock_inv r r1 r2))
  (n_ghost_contrib:G.erased int)
  (b:bool)
  ()
  : SteelT unit
      (incr_slprop r1 r2 n_ghost_contrib b)
      (fun _ -> incr_slprop r1 r2 (g_incr n_ghost_contrib) b)
  = acquire l;

    //TODO: this annotation seems necessary
    let w : G.erased (G.erased int & G.erased int) = A.witness_h_exists () in

    incr_ctr r;

    if b then begin
      //rewrite the `if b ...` slprop to its specialized r1 version
      A.change_slprop (incr_slprop r1 r2 n_ghost_contrib b)
                    (pts_to r1 half_perm (G.hide n_ghost_contrib))
                    (fun _ -> ());

      incr_ghost_contrib #n_ghost_contrib #(fst (G.reveal w)) r1;

      //rewrite the pts_to assertion for r, to push `g_incr` inside at r1's contrib
      A.change_slprop (pts_to r full_perm (g_incr (G.hide (fst (G.reveal w) + snd (G.reveal w)))))
                    (pts_to r full_perm (G.hide (g_incr n_ghost_contrib + snd (G.reveal w))))
                    (fun _ -> ());

      //restore lock invariant
      intro_exists (g_incr n_ghost_contrib, snd (G.reveal w)) (lock_inv_pred r r1 r2);
      //rewrite to `if b ...` form
      change_slprop (pts_to r1 half_perm (G.hide (g_incr n_ghost_contrib)))
                    (incr_slprop r1 r2 (g_incr n_ghost_contrib) b)
                    (fun _ -> ())
    end
    else begin  //similar to the then branch
      change_slprop (incr_slprop r1 r2 n_ghost_contrib b)
                    (pts_to r2 half_perm (G.hide n_ghost_contrib))
                    (fun _ -> ());

      incr_ghost_contrib #n_ghost_contrib #(snd (G.reveal w)) r2;

      change_slprop (pts_to r full_perm (g_incr (G.hide (fst (G.reveal w) + snd (G.reveal w)))))
                    (pts_to r full_perm (G.hide (fst (G.reveal w) + g_incr n_ghost_contrib)))
                    (fun _ -> ());

      intro_exists (fst (G.reveal w), g_incr n_ghost_contrib) (lock_inv_pred r r1 r2);
      change_slprop (pts_to r2 half_perm (G.hide (g_incr n_ghost_contrib)))
                    (incr_slprop r1 r2 (g_incr n_ghost_contrib) b)
                    (fun _ -> ())
    end;
    release l

(*
 * Fork two parallel threads with `incr`
 *)
let incr_par (r:ref int) (r1 r2:ref (G.erased int)) (n1 n2:G.erased int)
  (l:lock (lock_inv r r1 r2))
  : SteelT unit
      (pts_to r1 half_perm (G.hide n1) `star`
       pts_to r2 half_perm (G.hide n2))
      (fun _ -> pts_to r1 half_perm (G.hide (g_incr n1)) `star`
             pts_to r2 half_perm (G.hide (g_incr n2)))
  = let _ = par (incr r r1 r2 l n1 true)
                (incr r r1 r2 l n2 false) in
    ()

(*
 * The main function
 *)
let incr_main (#v:G.erased int) (r:ref int)
  : SteelT unit
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (G.hide (G.reveal v + 2)))
  = //allocate the two contribution references
    let r1 = R.alloc (G.hide 0) in
    let r2 = R.alloc v in

    //split their permissions into half
    R.share_atomic r1;
    change_slprop (pts_to r1 (P.half_perm P.full_perm) (G.hide (G.hide 0)) `star`
                   pts_to r1 (P.half_perm P.full_perm) (G.hide (G.hide 0)))
                  (pts_to r1 half_perm (G.hide (G.hide 0)) `star`
                   pts_to r1 half_perm (G.hide (G.hide 0)))
                  (fun _ -> ());

    R.share_atomic r2;
    change_slprop (pts_to r2 (P.half_perm P.full_perm) (G.hide v) `star`
                   pts_to r2 (P.half_perm P.full_perm) (G.hide v))
                  (pts_to r2 half_perm (G.hide v) `star`
                   pts_to r2 half_perm (G.hide v))
                  (fun _ -> ());


    //rewrite the value of `r` to bring it in the shape as expected by the lock
    change_slprop (pts_to r full_perm v)
                  (pts_to r full_perm (G.hide (G.reveal (fst (G.hide 0, v)) + G.reveal (snd (G.hide 0, v)))))
                  (fun _ -> ());

    //create the lock
    intro_exists (G.hide 0, v) (lock_inv_pred r r1 r2);

    let l = new_lock (lock_inv r r1 r2) in

    //do the increments
    incr_par r r1 r2 (G.hide 0) v l;

    //rewrite g_incr in the returned slprops from the two increments
    change_slprop (pts_to r1 half_perm (G.hide (g_incr (G.hide 0))))
                  (pts_to r1 half_perm (G.hide (G.hide 1)))
                  (fun _ -> ());
    change_slprop (pts_to r2 half_perm (G.hide (g_incr v)))
                  (pts_to r2 half_perm (G.hide (G.hide (G.reveal v + 1))))
                  (fun _ -> ());

    //take the lock
    acquire l;

    let w = A.witness_h_exists () in

    //gather the permissions for the ghost references, and then free them
    R.gather_atomic #_ #_ #_ #_ #_ #(G.hide (fst (G.reveal w))) r1;
    R.gather_atomic #_ #_ #_ #_ #_ #(G.hide (snd (G.reveal w))) r2;
    rewrite_perm r1 (P.sum_perm half_perm half_perm) full_perm;
    rewrite_perm r2 (P.sum_perm half_perm half_perm) full_perm;
    R.free r1;
    R.free r2;

    change_slprop (pts_to r full_perm (G.hide (G.reveal (fst (G.reveal w)) + G.reveal (snd (G.reveal w)))))
                  (pts_to r full_perm (G.hide (G.reveal v + 2)))
                  (fun _ -> ())
