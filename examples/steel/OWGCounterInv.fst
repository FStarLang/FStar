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
*)

module OWGCounterInv

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

open Steel.DisposableInvariant

#set-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --fuel 0 --ifuel 0"

let half_perm = half_perm (MkPerm 1.0R)

let fst = fst
let snd = snd
  
[@@ __reduce__]
let inv_pred (r:ref int) (r1 r2:ghost_ref int) =
  fun (w:G.erased int & G.erased int) ->
    ghost_pts_to r1 half_perm (fst w) `star`
    ghost_pts_to r2 half_perm (snd w) `star`
    pts_to r full_perm (G.hide (fst w + snd w))

[@@ __reduce__]
let inv_slprop (r:ref int) (r1 r2:ghost_ref int) : slprop =
  h_exists (inv_pred r r1 r2)

#push-options "--warn_error -271"
let inv_equiv_lemma (r:ref int) (r1 r2:ghost_ref int)
  : Lemma (inv_slprop r r1 r2 `equiv` inv_slprop r r2 r1)
  = let aux (r:ref int) (r1 r2:ghost_ref int) (m:mem)
      : Lemma
          (requires interp (inv_slprop r r1 r2) m)
          (ensures interp (inv_slprop r r2 r1) m)
          [SMTPat ()]
      = let w : G.erased (G.erased int & G.erased int) = id_elim_exists (inv_pred r r1 r2) m in
        assert ((ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 pts_to r full_perm (G.hide (G.reveal (fst (snd w, fst w)) + G.reveal (snd (snd w, fst w))))) `equiv`
                (ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 pts_to r full_perm (G.hide (G.reveal (fst (snd w, fst w)) + G.reveal (snd (snd w, fst w)))))) by Steel.Memory.Tactics.canon ();

        intro_h_exists (snd w, fst w) (inv_pred r r2 r1) m in
    ()
#pop-options

let enter_inv_slprop (#opened_invariants:inames)
  (r:ref int) (r_mine r_other:ghost_ref int) (b:bool)
  : SteelAtomicT unit opened_invariants unobservable
      (inv_slprop r (if b then r_mine else r_other)
                    (if b then r_other else r_mine))
      (fun _ -> inv_slprop r r_mine r_other)
  = if b then rewrite_context ()
    else begin
      change_slprop (inv_slprop r (if b then r_mine else r_other)
                                  (if b then r_other else r_mine))
                    (inv_slprop r r_other r_mine) (fun _ -> ());
      inv_equiv_lemma r r_mine r_other;
      rewrite_context #_ #(inv_slprop r r_other r_mine) #(inv_slprop r r_mine r_other) ()
    end

let exit_inv_slprop (#uses:inames)
  (r:ref int) (r_mine r_other:ghost_ref int) (b:bool)
  : SteelAtomicT unit uses unobservable
      (inv_slprop r r_mine r_other)
      (fun _ -> inv_slprop r (if b then r_mine else r_other)
                          (if b then r_other else r_mine))
  = if b then rewrite_context ()
    else begin
      inv_equiv_lemma r r_mine r_other;
      rewrite_context #_ #(inv_slprop r r_mine r_other) #(inv_slprop r r_other r_mine) ();
      rewrite_context ()
    end

let g_incr (n:G.erased int) = G.elift1 (fun (n:int) -> n + 1) n

assume val incr_atomic (#uses:inames) (#v:G.erased int) (r:ref int)
  : SteelAtomicT unit uses observable
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (g_incr v))

let rewrite_perm (#uses:inames) (#a:Type) (#v:G.erased a) (r:ghost_ref a) (p1 p2:P.perm)
  : SteelAtomic unit uses unobservable
      (ghost_pts_to r p1 v)
      (fun _ -> ghost_pts_to r p2 v)
      (fun _ -> p1 == p2)
      (fun _ _ _ -> True)
  = change_slprop (ghost_pts_to r p1 v)
                  (ghost_pts_to r p2 v)
                  (fun _ -> ())

let incr_ghost_contrib (#uses:inames) (#v1 #v2:G.erased int) (r:ghost_ref int)
  : SteelAtomic unit uses unobservable
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

let incr_with_invariant
  (r:ref int) (r_mine r_other:ghost_ref int) (n_ghost:G.erased int) (b:bool)
  (i:inv (inv_slprop r (if b then r_mine else r_other)
                       (if b then r_other else r_mine)))
  ()
  : SteelAtomicT unit (Set.singleton (name i)) observable
      (inv_slprop r (if b then r_mine else r_other)
                    (if b then r_other else r_mine)
       `star`
       ghost_pts_to r_mine half_perm n_ghost)
      (fun _ ->
       inv_slprop r (if b then r_mine else r_other)
                    (if b then r_other else r_mine)
       `star`
       ghost_pts_to r_mine half_perm (g_incr n_ghost))
  = enter_inv_slprop #_ r r_mine r_other b;
    let w : G.erased (G.erased int & G.erased int) = witness_h_exists () in
    incr_atomic r;
    incr_ghost_contrib #_ #n_ghost #(fst w) r_mine;
    change_slprop (pts_to r full_perm (g_incr (G.hide (fst w + snd w))))
                  (pts_to r full_perm (G.hide (g_incr (fst w) + snd w)))
                  (fun _ -> ());
    intro_exists (g_incr (fst w), snd w) (inv_pred r r_mine r_other);
    exit_inv_slprop r r_mine r_other b

let with_invariant (#a:Type)
                   (#fp:slprop)
                   (#fp':a -> slprop)
                   (#o:observability)
                   (#p:slprop)
                   (#perm:_)
                   (i:inv p)
                   ($f:unit -> SteelAtomicT a (Set.singleton (name i)) o
                                             (p `star` fp)
                                             (fun x -> p `star` fp' x))
                   ()
  : SteelT a (active perm i `star` fp) (fun x -> active perm i `star` fp' x)
  = sladmit () //with_invariant #a #fp #fp' #Set.empty #o #p #perm i f

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
 
    intro_exists (G.hide 0, v) (inv_pred r r1 r2);

    let i = new_inv (inv_slprop r r1 r2) in

    share i;

    change_slprop (active (P.half_perm full_perm) i `star`
                   active (P.half_perm full_perm) i)
                  (active half_perm i `star`
                   active half_perm i) (fun _ -> ());


    let _ = par
      (with_invariant
        #unit
        #(ghost_pts_to r1 half_perm 0)
        #(fun _ -> ghost_pts_to r1 half_perm (g_incr 0))
        #observable
        #(inv_slprop r r1 r2)
        #half_perm
        i
        (incr_with_invariant r r1 r2 0 true i))
      (with_invariant
        #unit
        #(ghost_pts_to r2 half_perm v)
        #(fun _ -> ghost_pts_to r2 half_perm (g_incr v))
        #observable
        #(inv_slprop r r1 r2)
        #half_perm
        i
        (incr_with_invariant r r2 r1 v false i)) in

    gather #_ #half_perm #half_perm #_ i;

    change_slprop (active (sum_perm half_perm half_perm) i)
                  (active full_perm i) (fun _ -> ());

    dispose i;

    let w = A.witness_h_exists () in

    ghost_gather #_ #_ #_ #_ #(fst w) #_ r1;
    ghost_gather #_ #_ #_ #_ #(snd w) #_ r2;
    drop (ghost_pts_to r1 (P.sum_perm half_perm half_perm) (fst w));
    drop (ghost_pts_to r2 (P.sum_perm half_perm half_perm) (snd w));

    change_slprop (pts_to r full_perm (G.hide (G.reveal (fst w) + G.reveal (snd w))))
                  (pts_to r full_perm (v + 2))
                  (fun _ -> ())
