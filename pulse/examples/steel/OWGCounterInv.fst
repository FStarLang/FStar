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

(*
 * An implementation of the parallel counter presented by Owicki and Gries
 * "Verifying properties of parallel programs: An axiomatic approach.", CACM'76
 *
 * using disposable invariants
 *
 * See OWGCounter.fst for an implementation using the locks
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

#set-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --fuel 0 --ifuel 0 --ide_id_info_off"

(**** A few wrappers over library functions ****)

let ghost_gather (#uses:inames) (v1 #v2:G.erased int) (r:ghost_ref int)
  : SteelGhost unit uses
      (ghost_pts_to r (P.half_perm full_perm) v1 `star`
       ghost_pts_to r (P.half_perm full_perm) v2)
      (fun _ -> ghost_pts_to r full_perm v1)
      (fun _ -> True)
      (fun _ _ _ -> v1 == v2)
  = ghost_gather_pt #_ #_ #_ #_ #v1 #v2 r;
    ()

let ghost_share (#uses:inames) (v1 #v2:G.erased int) (r:ghost_ref int)
  : SteelGhost unit uses
      (ghost_pts_to r full_perm v1)
      (fun _ -> ghost_pts_to r (P.half_perm full_perm) v1 `star`
             ghost_pts_to r (P.half_perm full_perm) v2)
      (fun _ -> v1 == v2)
      (fun _ _ _ -> True)
  = ghost_share_pt #_ #_ #_ #v1 r; ()

let gather_invariant (#p:vprop) (#uses:inames) (i:inv p)
  : SteelGhostT unit uses
      (active (P.half_perm full_perm) i `star` active (P.half_perm full_perm) i)
      (fun _ -> active full_perm i)
  = gather #_ #(P.half_perm full_perm) #(P.half_perm full_perm) #_ i; ()

(*
 * A SteelAtomic to Steel lift for with_invariant
 *
 * We will use it when composing with_invariant with Steel.Effect.par
 *)
inline_for_extraction
let with_invariant (#a:Type)
                   (#fp:vprop)
                   (#fp':a -> vprop)
                   (#p:vprop)
                   (#perm:_)
                   (i:inv p)
                   ($f:unit -> SteelAtomicT a (Set.singleton (Ghost.reveal (name i)))
                                             (p `star` fp)
                                             (fun x -> p `star` fp' x))
  : SteelT a (active perm i `star` fp) (fun x -> active perm i `star` fp' x)
  = assert (Set.equal (Set.singleton (Ghost.reveal (name i))) (set_add (name i) Set.empty));
    with_invariant i f

(**** Definition of the invariant slprop ****)

(*
 * The invariant holds half permission for the ghost refs and full perm for
 *   the counter, with an assertion relating their contents
 *)

let half_perm = P.half_perm full_perm

[@@ __reduce__]
let inv_pred (r:ref int) (r1 r2:ghost_ref int) =
  fun (w:int & int) ->
    ghost_pts_to r1 (P.half_perm full_perm) (fst w) `star`
    ghost_pts_to r2 (P.half_perm full_perm) (snd w) `star`
    pts_to r full_perm (fst w + snd w)

(*
 * The h_exists slprop that the invariant protects
 *)
[@@ __reduce__]
let inv_slprop (r:ref int) (r1 r2:ghost_ref int) : vprop =
  h_exists (inv_pred r r1 r2)

(*
 * A helper lemma to show that in the inv slprop the ghost refs commute with equiv
 *)
#push-options "--warn_error -271 --fuel 1"
let inv_equiv_lemma (r:ref int) (r1 r2:ghost_ref int)
  : Lemma (inv_slprop r r1 r2 `equiv` inv_slprop r r2 r1)
          [SMTPat (inv_slprop r r1 r2)]
  =   let aux (r:ref int) (r1 r2:ghost_ref int) (m:mem)
      : Lemma
          (requires interp (hp_of (inv_slprop r r1 r2)) m)
          (ensures interp (hp_of (inv_slprop r r2 r1)) m)
          [SMTPat ()]
      = assert (
          Steel.Memory.h_exists #(int & int) (fun x -> hp_of (inv_pred r r1 r2 x)) ==
          h_exists_sl #(int & int) (inv_pred r r1 r2))
          by (FStar.Tactics.norm [delta_only [`%h_exists_sl]]);


        let w : G.erased (int & int) = id_elim_exists (fun x -> hp_of (inv_pred r r1 r2 x)) m in

        assert ((ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 pts_to r full_perm (fst (snd w, fst w) + snd (snd w, fst w))) `equiv`
                (ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 pts_to r full_perm (fst (snd w, fst w) + snd (snd w, fst w)))) by (FStar.Tactics.norm [delta_attr [`%__steel_reduce__]]; canon' false (`true_p) (`true_p));

        reveal_equiv
          (ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 pts_to r full_perm (fst (snd w, fst w) + snd (snd w, fst w)))
          (ghost_pts_to r2 half_perm (fst (snd w, fst w)) `star`
                 ghost_pts_to r1 half_perm (snd (snd w, fst w)) `star`
                 pts_to r full_perm (fst (snd w, fst w) + snd (snd w, fst w)));

        assert (interp (hp_of (inv_pred r r2 r1 (snd w, fst w))) m);

        intro_h_exists (snd w, fst w) (fun x -> hp_of (inv_pred r r2 r1 x)) m;
        assert (interp (Steel.Memory.h_exists (fun x -> hp_of (inv_pred r r2 r1 x))) m);

        assert (
          Steel.Memory.h_exists #(int & int) (fun x -> hp_of (inv_pred r r2 r1 x)) ==
          h_exists_sl #(int & int) (inv_pred r r2 r1))
          by (FStar.Tactics.norm [delta_only [`%h_exists_sl]]) in

  reveal_equiv (inv_slprop r r1 r2) (inv_slprop r r2 r1)
#pop-options


(**** Helpers for the counter implementation ****)
let incr (n:G.erased int) = G.elift1 (fun (n:int) -> n + 1) n

(*
 * We assume an atomic increment operation for int refs.
 *)
assume val incr_atomic (#uses:inames) (#v:G.erased int) (r:ref int)
  : SteelAtomicT unit uses
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (incr v))

(*
 * Incrementing the ghost contribution ref
 *
 * The caller provides two half permissions,
 *   and we return the same permissions with the incremented contents
 *)
let incr_ghost_contrib (#uses:inames) (#v1 #v2:G.erased int) (r:ghost_ref int)
  : SteelGhost unit uses
      (ghost_pts_to r (P.half_perm full_perm) v1 `star`
       ghost_pts_to r (P.half_perm full_perm) v2)
      (fun _ -> ghost_pts_to r (P.half_perm full_perm) (incr v1) `star`
             ghost_pts_to r (P.half_perm full_perm) (incr v2))
      (fun _ -> True)
      (fun _ _ _ -> v1 == v2)
  = ghost_gather v1 r;
    ghost_write_pt r (incr v1);
    ghost_share (incr v1) r

(*
 * Another form of the inv_slprop with conditional on the ghost refs
 *)
[@@ __reduce__]
let inv_slprop_conditional (r:ref int) (r_mine r_other:ghost_ref int) (b:bool) =
  inv_slprop r (if b then r_mine else r_other)
               (if b then r_other else r_mine)


(*
 * The function that each thread invokes
 *
 * It increments the counter and the ghost ref r_mine
 *   consuming and restoring inv_slprop_conditional
 *)
inline_for_extraction
let incr_with_inv_slprop
  (r:ref int) (r_mine r_other:ghost_ref int) (n_ghost:G.erased int) (b:bool) (name:Ghost.erased iname)
  ()
  : SteelAtomicT unit (Set.singleton (Ghost.reveal name))
      (inv_slprop_conditional r r_mine r_other b
       `star`
       ghost_pts_to r_mine (P.half_perm full_perm) n_ghost)
      (fun _ ->
       inv_slprop_conditional r r_mine r_other b
       `star`
       ghost_pts_to r_mine (P.half_perm full_perm) (incr n_ghost))
  = //get inv_slprop in the context
    rewrite_slprop (inv_slprop_conditional _ _ _ _)
                   (inv_slprop _ _ _) (fun _ -> Classical.forall_intro_2 reveal_equiv);
    let w : G.erased (int & int) = witness_exists () in
    incr_atomic r;
    incr_ghost_contrib #_ #n_ghost #(fst w) r_mine;

    //restore inv_slprop, by first writing r to a form expected by the invariant
    intro_exists (fst w+1, snd w) (inv_pred r r_mine r_other);
    rewrite_slprop (inv_slprop _ _ _)
                   (inv_slprop_conditional _ _ _ _)
                   (fun _ -> Classical.forall_intro_2 reveal_equiv)

(*
 * A with_invariant wrapper over incr_with_inv_slprop
 *)
inline_for_extraction
let incr_with_invariant
  (r:ref int) (r_mine r_other:ghost_ref int) (n_ghost:G.erased int) (b:bool)
  (i:inv (inv_slprop_conditional r r_mine r_other b))
  ()
  : SteelT unit
      (active (P.half_perm full_perm) i `star` ghost_pts_to r_mine (P.half_perm full_perm) n_ghost)
      (fun _ -> active (P.half_perm full_perm) i `star` ghost_pts_to r_mine (P.half_perm full_perm) (incr n_ghost))
  = with_invariant i
      (incr_with_inv_slprop r r_mine r_other n_ghost b (name i))

(*
 * The main thread
 *)
let incr_main (#v:G.erased int) (r:ref int)
  : SteelT unit
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm (v + 2))
  = //allocate the two ghost refs
    let r1 = ghost_alloc_pt 0 in
    let r2 = ghost_alloc_pt v in

    //split their permissions
    R.ghost_share_pt r1;
    R.ghost_share_pt r2;

    //create the invariant

    intro_exists (0, G.reveal v) (inv_pred r r1 r2);
    let i = new_inv (inv_slprop r r1 r2) in

    //split the invariant permission
    share i;

    //invoke the two threads
    let _ =
      par (incr_with_invariant r r1 r2 0 true i)
          (incr_with_invariant r r2 r1 v false i) in

    //gather back the invariant and dispose it
    gather_invariant i; dispose i;

    let _ = witness_exists () in

    ghost_gather (incr 0) r1; ghost_gather (incr v) r2;
    drop (ghost_pts_to r1 _ _);
    drop (ghost_pts_to r2 _ _)
