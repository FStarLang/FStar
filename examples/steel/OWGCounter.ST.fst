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

   Author: Aseem Rastogi
*)

module OWGCounter.ST

open Steel.Memory
open Steel.ST.Effect.Atomic
open Steel.ST.Effect
open Steel.ST.SpinLock
open Steel.ST.Util

module G = FStar.Ghost
module R = Steel.ST.Reference
module GR = Steel.ST.GhostReference

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

#set-options "--ide_id_info_off"

let half_perm = half_perm full_perm

[@@ __reduce__]
let lock_inv_predicate (r:R.ref int) (r1 r2:GR.ref int)
  : int & int -> vprop
  = fun w ->
    GR.pts_to r1 half_perm (fst w)
      `star`
    GR.pts_to r2 half_perm (snd w)
      `star`
    R.pts_to r full_perm (fst w + snd w)

[@@ __reduce__]
let lock_inv (r:R.ref int) (r1 r2:GR.ref int) : vprop =
  exists_ (lock_inv_predicate r r1 r2)

inline_for_extraction
noextract
let acquire (r:R.ref int) (r_mine r_other:GR.ref int) (b:G.erased bool)
  (l:lock (lock_inv r (if b then r_mine else r_other)
                      (if b then r_other else r_mine)))
  : STT unit
        emp
        (fun _ -> lock_inv r r_mine r_other)
  = acquire l;
    if b returns STGhostT unit
                          Set.empty
                          _
                          (fun _ -> lock_inv r r_mine r_other)
    then begin
      rewrite (lock_inv _ _ _)
              (lock_inv r r_mine r_other)
    end
    else begin
      rewrite (lock_inv _ _ _)
              (lock_inv r r_other r_mine);
      let w = elim_exists () in
      rewrite
        (GR.pts_to r_other _ _
           `star`
         GR.pts_to r_mine _ _
           `star`
         R.pts_to _ _ _)
        (GR.pts_to r_other half_perm (snd (snd w, fst w))
           `star`
         GR.pts_to r_mine half_perm (fst (snd w, fst w))
           `star`
         R.pts_to r full_perm (fst (snd w, fst w) + snd (snd w, fst w)));
      intro_exists (snd w, fst w) (lock_inv_predicate r r_mine r_other)
    end

inline_for_extraction
noextract
let release (r:R.ref int) (r_mine r_other:GR.ref int) (b:G.erased bool)
  (l:lock (lock_inv r (if b then r_mine else r_other)
                      (if b then r_other else r_mine)))
  : STT unit
        (lock_inv r r_mine r_other)
        (fun _ -> emp)
  = if b
    then begin
      rewrite (lock_inv r r_mine r_other)
              (lock_inv r (if b then r_mine else r_other)
                          (if b then r_other else r_mine))
    end
    else begin
      let w = elim_exists () in
      rewrite
        (GR.pts_to r_mine half_perm (fst w)
           `star`
         GR.pts_to r_other half_perm (snd w)
           `star`
         R.pts_to r full_perm (fst w + snd w))
        (GR.pts_to r_mine half_perm (snd (snd w, fst w))
           `star`
         GR.pts_to r_other half_perm (fst (snd w, fst w))
           `star`
         R.pts_to r full_perm (fst (snd w, fst w) + snd (snd w, fst w)));
      intro_exists
        (snd w, fst w)
        (lock_inv_predicate r r_other r_mine);
      rewrite (lock_inv r r_other r_mine)
              (lock_inv r (if b then r_mine else r_other)
                          (if b then r_other else r_mine))
    end;
    release l

module P = Steel.FractionalPermission

let incr (r:R.ref int) (r_mine r_other:GR.ref int) (b:G.erased bool)
  (l:lock (lock_inv r (if b then r_mine else r_other)
                      (if b then r_other else r_mine)))
  (n:G.erased int)
  ()
  : STT unit
        (GR.pts_to r_mine half_perm n)
        (fun _ -> GR.pts_to r_mine half_perm (n+1))
  = acquire r r_mine r_other b l;
    let w = elim_exists () in
    let v = R.read r in
    R.write r (v+1);
    rewrite
      (R.pts_to r full_perm (v+1))
      (R.pts_to r full_perm ((fst w+1) + snd w));

    GR.gather #_ #_ #_ #_ #n #(G.hide (fst w)) r_mine;
    rewrite (GR.pts_to r_mine (sum_perm half_perm half_perm) n)
            (GR.pts_to r_mine full_perm n);
    GR.write r_mine (n+1);
    GR.share r_mine;
    rewrite (GR.pts_to r_mine (P.half_perm full_perm) (n+1))
            (GR.pts_to r_mine half_perm (fst w+1));
    intro_exists (fst w+1, snd w)
                 (lock_inv_predicate r r_mine r_other);
    release r r_mine r_other b l;
    rewrite (GR.pts_to r_mine (P.half_perm full_perm) (n+1))
            (GR.pts_to r_mine half_perm (n+1))

let incr_main (#v:G.erased int) (r:R.ref int)
  : STT unit
        (R.pts_to r full_perm v)
        (fun _ -> R.pts_to r full_perm (v+2))
  = let r1 = GR.alloc 0 in
    let r2 = GR.alloc v in

    GR.share r1;
    rewrite (GR.pts_to r1 (P.half_perm full_perm) 0
               `star`
             GR.pts_to r1 (P.half_perm full_perm) 0)
            (GR.pts_to r1 half_perm (fst (0, v))
               `star`
             GR.pts_to r1 half_perm 0);
    GR.share r2;
    rewrite (GR.pts_to r2 (P.half_perm full_perm) v
               `star`
             GR.pts_to r2 (P.half_perm full_perm) v)
            (GR.pts_to r2 half_perm (snd (0, G.reveal v))
               `star`
             GR.pts_to r2 half_perm v);

    rewrite (R.pts_to r full_perm v)
            (R.pts_to r full_perm (fst (0, v) + snd (0, G.reveal v)));

    intro_exists (0, G.reveal v) (lock_inv_predicate r r1 r2);
  
    let l = new_lock (lock_inv r r1 r2) in

    let _ = par (incr r r1 r2 true l 0)
                (incr r r2 r1 false l v) in

    Steel.ST.SpinLock.acquire l;
    let w = elim_exists () in
    GR.gather #_ #_ #_ #_ #_ #(G.hide (fst w)) r1;
    GR.gather #_ #_ #_ #_ #_ #(G.hide (snd w)) r2;
    drop (GR.pts_to r1 _ _);
    drop (GR.pts_to r2 _ _);

    rewrite (R.pts_to r full_perm (fst w+snd w))
            (R.pts_to r full_perm (v+2))
