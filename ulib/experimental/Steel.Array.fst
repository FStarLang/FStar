(*
   Copyright 2020 Microsoft Research

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

module Steel.Array

open Steel.Effect.Atomic
open Steel.Reference
open FStar.Ghost
module U32 = FStar.UInt32
module R = Steel.Reference
module AT = Steel.Effect.Atomic
let array t = l:erased nat & ref (Seq.lseq t l)

let length #t (x:array t) = dfst x
let is_array r = ptr (dsnd r)
let array_sel r = ptr_sel (dsnd r)

let varray_pts_to (#t:Type) (a:array t) (x:Seq.lseq t (length a))
  : vprop
  = Steel.Reference.pts_to (dsnd a) Steel.FractionalPermission.full_perm x

let intro_varray_pts_to (#t:_)
                        (#opened:inames)
                        (a:array t)
  = Steel.Reference.elim_vptr (dsnd a) Steel.FractionalPermission.full_perm

let elim_varray_pts_to (#t:_)
                       (#opened:inames)
                       (a:array t)
                       (c:elseq t (length a))
  : SteelGhost unit opened
    (varray_pts_to a c)
    (fun _ -> varray a)
    (requires fun _ -> True)
    (ensures fun _ _ h1 ->
      asel a h1 == Ghost.reveal c)
  = Steel.Reference.intro_vptr (dsnd a) Steel.FractionalPermission.full_perm c

let malloc #a x n =
  let l : erased nat = hide (U32.v n) in
  let s : Seq.lseq a l = Seq.create (U32.v n) x in
  let p : ref (Seq.lseq a l) = malloc s in
  let x : array a = (| l, p |) in
  Steel.Effect.Atomic.return x

let index r i =
  let s = read (dsnd r) in
  Seq.index s (U32.v i)

let upd r i x =
  let s = read (dsnd r) in
  let s' = Seq.upd s (U32.v i) x in
  write (dsnd r) s'

let free r = free (dsnd r)

////////////////////////////////////////////////////////////////////////////////

module AT = Steel.Effect.Atomic

let read_pt (#t:_)
            (a:array t)
            (#r:elseq t (length a))
            (i:U32.t { U32.v i < length a })
  : Steel t
    (varray_pts_to a r)
    (fun _ -> varray_pts_to a r)
    (requires fun _ -> True)
    (ensures fun h0 v h1 ->
      v == Seq.index r (U32.v i))
  = elim_varray_pts_to a r;
    let x = index a i in
    let _ = intro_varray_pts_to a in
    change_equal_slprop (varray_pts_to _ _)
                         (varray_pts_to a r);
    AT.return x


let write_pt (#t:_)
            (a:array t)
            (#r:elseq t (length a))
            (i:U32.t { U32.v i < length a })
            (v:t)
  : SteelT unit
    (varray_pts_to a r)
    (fun _ -> varray_pts_to a (Seq.upd r (U32.v i) v))
  = elim_varray_pts_to a r;
    let x = upd a i v in
    let _ = intro_varray_pts_to a in
    AT.change_equal_slprop (varray_pts_to _ _)
                           (varray_pts_to a _);
    AT.return ()

let prefix_copied #t #l0 #l1
                  (e0:elseq t l0)
                  (e1:elseq t l1)
                  (i:nat { i <= l0 /\ l0 == l1})
   : elseq t l1
   = (Seq.append (Seq.slice e0 0 i) (Seq.slice e1 i (Seq.length e1)))

let coerce #t (#l0 #l1:_) (e:elseq t l0 { l0 = l1}) : elseq t l1 = e

let slice_lem (#t:_)
              (#l0 #l1:_)
              (e0:elseq t l0)
              (e1:elseq t l1)
  : Lemma
    (requires l0 == l1)
    (ensures prefix_copied e0 e1 l0 `Seq.equal`
             coerce #t #l0 #l1 e0)
  = ()

module Loops = Steel.Loops

let memcpy_pt (#t:_)
              (a0 a1:array t)
              (#e0:elseq t (length a0))
              (#e1:elseq t (length a1))
              (i:U32.t{ U32.v i == length a0 /\ length a0 == length a1 })
  : SteelT unit
    (varray_pts_to a0 e0 `star` varray_pts_to a1 e1)
    (fun _ -> varray_pts_to a0 e0 `star` varray_pts_to a1 (coerce e0))
  = let inv (j:Loops.nat_at_most i)
      : vprop
      = varray_pts_to a0 e0 `star`
        varray_pts_to a1 (prefix_copied e0 e1 j)
    in
    let body (j:Loops.u32_between 0ul i)
      : SteelT unit
        (inv (U32.v j))
        (fun _ -> inv (U32.v j + 1))
      = AT.change_equal_slprop
            (inv (U32.v j))
            (varray_pts_to a0 e0 `star`
             varray_pts_to a1 (prefix_copied e0 e1 (U32.v j)));
        let z = read_pt a0 j in
        write_pt a1 j z;
        assert (Seq.upd (prefix_copied e0 e1 (U32.v j)) (U32.v j) z `Seq.equal`
                prefix_copied e0 e1 (U32.v j + 1));
        AT.change_equal_slprop (varray_pts_to a0 e0 `star` varray_pts_to a1 _)
                               (inv (U32.v j + 1));
        AT.return ()
    in
    assert (prefix_copied e0 e1 0 `Seq.equal` e1);
    AT.change_equal_slprop (varray_pts_to a1 _)
                           (varray_pts_to a1 (prefix_copied e0 e1 (U32.v 0ul)));
    AT.change_equal_slprop (varray_pts_to a0 e0 `star` varray_pts_to a1 _)
                           (inv (U32.v 0ul));
    Loops.for_loop 0ul i inv body;
    AT.slassert (inv (U32.v i));
    AT.change_equal_slprop (inv (U32.v i))
                           (varray_pts_to a0 e0 `star`
                            varray_pts_to a1 (prefix_copied e0 e1 (U32.v i)));
    slice_lem e0 e1;
    AT.change_equal_slprop (varray_pts_to a1 (prefix_copied e0 e1 (U32.v i)))
                           (varray_pts_to a1 (coerce e0));
    AT.return ()

let memcpy #t a0 a1 i
  = let _ : squash (length a0 == length a1) = () in
    let _ = intro_varray_pts_to a0 in
    let _ = intro_varray_pts_to a1 in
    memcpy_pt a0 a1 i;
    elim_varray_pts_to a0 _;
    elim_varray_pts_to a1 _

////////////////////////////////////////////////////////////////////////////////
// compare
////////////////////////////////////////////////////////////////////////////////

#push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 2"
let equal_up_to #t #l #m
                  (s0: elseq t l)
                  (s1: elseq t m)
                  (v : option U32.t) : prop =
    l = m /\
    (match v with
     | None -> Ghost.reveal s0 =!= Ghost.reveal s1
     | Some v -> U32.v v <= l /\ Seq.slice s0 0 (U32.v v) `Seq.equal` Seq.slice s1 0 (U32.v v))

let within_bounds (x:option U32.t) (l:U32.t) (b:Ghost.erased bool) : prop =
  if b then Some? x /\ U32.(Some?.v x <^ l)
  else None? x \/ U32.(Some?.v x >=^ l)

let inv (#t:eqtype)
        (a0 a1:array t)
        (s0: elseq t (length a0))
        (s1: elseq t (length a1))
        (l:U32.t { length a0 > 0 /\ length a0 == length a1 /\ U32.v l == length a0})
        (ctr : R.ref (option U32.t))
        (b: Ghost.erased bool) =
    varray_pts_to a0 s0 `star`
    varray_pts_to a1 s1 `star`
    AT.h_exists (fun (x:option U32.t) ->
        R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
        pure (equal_up_to s0 s1 x) `star`
        pure (within_bounds x l b))

let elim_inv #o
        (#t:eqtype)
        (a0 a1:array t)
        (#s0: elseq t (length a0))
        (#s1: elseq t (length a1))
        (l:U32.t { length a0 > 0 /\ length a0 == length a1 /\ U32.v l == length a0})
        (ctr : R.ref (option U32.t))
        (b: Ghost.erased bool)
    : AT.SteelGhostT (Ghost.erased (option U32.t)) o
        (inv a0 a1 s0 s1 l ctr b)
        (fun x ->
          let open U32 in
          varray_pts_to a0 s0 `star`
          varray_pts_to a1 s1 `star`
          R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
          pure (equal_up_to s0 s1 x) `star`
          pure (within_bounds x l b))
      = let open U32 in
        assert_spinoff
          ((inv a0 a1 s0 s1 l ctr b) ==
          (varray_pts_to a0 s0 `star`
           varray_pts_to a1 s1 `star`
           AT.h_exists (fun (v:option U32.t) ->
             R.pts_to ctr Steel.FractionalPermission.full_perm v `star`
             pure (equal_up_to s0 s1 v)  `star`
             pure (within_bounds v l b))));
        AT.change_equal_slprop
          (inv a0 a1 s0 s1 l ctr b)
          (varray_pts_to a0 s0 `star`
           varray_pts_to a1 s1 `star`
           AT.h_exists (fun (v:option U32.t) ->
             R.pts_to ctr Steel.FractionalPermission.full_perm v `star`
             pure (equal_up_to s0 s1 v) `star`
             pure (within_bounds v l b)));
        let _v = AT.witness_exists () in
        _v

let intro_inv #o
              (#t:eqtype)
              (a0 a1:array t)
              (#s0: elseq t (length a0))
              (#s1: elseq t (length a1))
              (l:U32.t { length a0 > 0 /\ length a0 == length a1 /\ U32.v l == length a0})
              (ctr : R.ref (option U32.t))
              (x: Ghost.erased (option U32.t))
              (b:bool { within_bounds x l b })
    : AT.SteelGhostT unit o
         (let open U32 in
          varray_pts_to a0 s0 `star`
          varray_pts_to a1 s1 `star`
          R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
          pure (equal_up_to s0 s1 x))
        (fun _ -> inv a0 a1 s0 s1 l ctr (Ghost.hide b))
    = let open U32 in
      AT.intro_pure (within_bounds x l (Ghost.hide b));
      AT.intro_exists_erased x (fun (x:option U32.t) ->
          R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
          pure (equal_up_to s0 s1 x) `star`
          pure (within_bounds x l (Ghost.hide b)));
      assert_norm
          ((inv a0 a1 s0 s1 l ctr (Ghost.hide b)) ==
          (varray_pts_to a0 s0 `star`
           varray_pts_to a1 s1 `star`
           AT.h_exists (fun (v:option U32.t) ->
             R.pts_to ctr Steel.FractionalPermission.full_perm v `star`
             pure (equal_up_to s0 s1 v)  `star`
             pure (within_bounds v l (Ghost.hide b)))));
        AT.change_equal_slprop
          (varray_pts_to a0 s0 `star`
           varray_pts_to a1 s1 `star`
           AT.h_exists (fun (v:option U32.t) ->
             R.pts_to ctr Steel.FractionalPermission.full_perm v `star`
             pure (equal_up_to s0 s1 v) `star`
             pure (within_bounds v l (Ghost.hide b))))
          (inv a0 a1 s0 s1 l ctr (Ghost.hide b))

let intro_exists_inv #o
              (#t:eqtype)
              (a0 a1:array t)
              (#s0: elseq t (length a0))
              (#s1: elseq t (length a1))
              (l:U32.t { length a0 > 0 /\ length a0 == length a1 /\ U32.v l == length a0})
              (ctr : R.ref (option U32.t))
              (x: Ghost.erased (option U32.t))
    : AT.SteelGhostT unit o
         (let open U32 in
          varray_pts_to a0 s0 `star`
          varray_pts_to a1 s1 `star`
          R.pts_to ctr Steel.FractionalPermission.full_perm x `star`
          pure (equal_up_to s0 s1 x))
        (fun _ -> AT.h_exists (inv a0 a1 s0 s1 l ctr))
    = let b : bool =
          match Ghost.reveal x with
          | None -> false
          | Some x -> U32.(x <^ l)
      in
      assert (within_bounds x l b);
      intro_inv a0 a1 #s0 #s1 l ctr x b;
      AT.intro_exists _ (inv a0 a1 s0 s1 l ctr)


let witness_exists_erased
      (#a:Type)
      (#opened_invariants:_)
      (#p:Ghost.erased a -> vprop)
      (_:unit)
  : AT.SteelGhostT (Ghost.erased a) opened_invariants
                   (AT.h_exists p) (fun x -> p x)
  = let w = AT.witness_exists () in
    Ghost.reveal w

let ref_read_pt (#a:Type) (#p:Steel.FractionalPermission.perm) (#v:Ghost.erased a) (r:R.ref a)
  : Steel a
    (R.pts_to r p v)
    (fun x -> R.pts_to r p v)
    (requires fun _ -> True)
    (ensures fun _ x _ -> x == Ghost.reveal v)
  = let v' = R.read_pt r in
    assert_spinoff (R.pts_to r p v' == R.pts_to r p v);
    AT.change_equal_slprop (R.pts_to r p v')
                           (R.pts_to r p v);
    AT.return v'

let extend_equal_up_to_lemma (#t:Type0)
                             (s0:Seq.seq t)
                             (s1:Seq.seq t)
                             (i:nat{ i < Seq.length s0 /\ Seq.length s0 == Seq.length s1 })
  : Lemma
    (requires
      Seq.equal (Seq.slice s0 0 i) (Seq.slice s1 0 i) /\
      Seq.index s0 i == Seq.index s1 i)
    (ensures
      Seq.equal (Seq.slice s0 0 (i + 1)) (Seq.slice s1 0 (i + 1)))
  = assert (forall k. k < i ==> Seq.index s0 k == Seq.index (Seq.slice s0 0 i) k /\
                           Seq.index s1 k == Seq.index (Seq.slice s1 0 i) k)


let extend_equal_up_to (#o:_)
                       (#t:Type0)
                       (#l #m:nat)
                       (#s0:elseq t l)
                       (#s1:elseq t m)
                       (len:U32.t)
                       (i:U32.t{ l == m /\ U32.(i <^ len) /\ U32.v len == l } )
  : AT.SteelGhost unit o
    (pure (equal_up_to s0 s1 (Some i)))
    (fun _ -> pure (equal_up_to s0 s1 (Some U32.(i +^ 1ul))))
    (requires fun _ ->
      Seq.index s0 (U32.v i) == Seq.index s1 (U32.v i))
    (ensures fun _ _ _ -> True)
  = AT.elim_pure _;
    extend_equal_up_to_lemma s0 s1 (U32.v i);
    AT.intro_pure _

let extend_equal_up_to_neg (#o:_)
                           (#t:Type0)
                           (#l #m:nat)
                           (#s0:elseq t l)
                           (#s1:elseq t m)
                           (len:U32.t)
                           (i:U32.t{ l == m /\ U32.(i <^ len) /\ U32.v len == l } )
  : AT.SteelGhost unit o
    (pure (equal_up_to s0 s1 (Some i)))
    (fun _ -> pure (equal_up_to s0 s1 None))
    (requires fun _ ->
      Seq.index s0 (U32.v i) =!= Seq.index s1 (U32.v i))
    (ensures fun _ _ _ -> True)
  = AT.elim_pure _;
    AT.intro_pure _

let init_inv #o
             (#t:eqtype)
             (a0 a1:array t)
             (#s0: elseq t (length a0))
             (#s1: elseq t (length a1))
             (l:U32.t { length a0 > 0 /\ length a0 == length a1 /\ U32.v l == length a0})
             (ctr : R.ref (option U32.t))
    : AT.SteelGhostT unit o
         (let open U32 in
          varray_pts_to a0 s0 `star`
          varray_pts_to a1 s1 `star`
          R.pts_to ctr Steel.FractionalPermission.full_perm (Some 0ul))
        (fun _ -> AT.h_exists (inv a0 a1 s0 s1 l ctr))
    = AT.intro_pure (equal_up_to s0 s1 (Ghost.hide (Some 0ul)));
      AT.change_equal_slprop
        (R.pts_to ctr Steel.FractionalPermission.full_perm (Some 0ul))
        (R.pts_to ctr Steel.FractionalPermission.full_perm (Ghost.hide (Some 0ul)));
      intro_exists_inv a0 a1 l ctr (Ghost.hide (Some 0ul))

let compare_pts (#t:eqtype)
                (a0 a1:array t)
                (#s0: elseq t (length a0))
                (#s1: elseq t (length a1))
                (l:U32.t { length a0 > 0 /\ length a0 == length a1 /\ U32.v l == length a0})
  : Steel bool
    (varray_pts_to a0 s0 `star` varray_pts_to a1 s1)
    (fun _ -> varray_pts_to a0 s0 `star` varray_pts_to a1 s1)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
      b = (Ghost.reveal s0 = Ghost.reveal s1))
  = let ctr = R.alloc_pt (Some 0ul) in
    let cond ()
      : SteelT bool
        (AT.h_exists (inv a0 a1 s0 s1 l ctr))
        (fun b -> inv a0 a1 s0 s1 l ctr (Ghost.hide b))
      = let _b = witness_exists_erased () in
        let _ = elim_inv _ _ _ _ _ in
        let x = ref_read_pt ctr in
        AT.elim_pure (within_bounds _ _ _);
        match x with
        | None ->
          intro_inv a0 a1 l ctr _ false;
          AT.return false

        | Some x ->
          let res = U32.(x <^ l) in
          intro_inv a0 a1 l ctr _ res;
          AT.return res
    in
    let body ()
      : SteelT unit
        (inv a0 a1 s0 s1 l ctr (Ghost.hide true))
        (fun _ -> AT.h_exists (inv a0 a1 s0 s1 l ctr))
      = let _i = elim_inv _ _ _ _ _ in
        AT.elim_pure (within_bounds _ _ _);
        let Some i = ref_read_pt ctr in
        assert_spinoff
          ((pure (equal_up_to s0 s1 _i)) ==
           (pure (equal_up_to s0 s1 (Some i))));
        AT.change_equal_slprop
          (pure (equal_up_to s0 s1 _i))
          (pure (equal_up_to s0 s1 (Some i)));
        let v0 = read_pt a0 i in
        let v1 = read_pt a1 i in
        if v0 = v1
        then (
          R.write_pt ctr (Some U32.(i +^ 1ul));
          extend_equal_up_to l i;
          intro_exists_inv a0 a1 l ctr (Ghost.hide (Some (U32.(i +^ 1ul))))
        )
        else (
          R.write_pt ctr None;
          extend_equal_up_to_neg l i;
          intro_exists_inv a0 a1 l ctr (Ghost.hide None)
        )
    in
    init_inv a0 a1 l ctr;
    Loops.while_loop (inv a0 a1 s0 s1 l ctr)
               cond
               body;
    let _ = elim_inv _ _ _ _ _ in
    AT.elim_pure (equal_up_to _ _ _);
    let v = R.read_pt ctr in
    R.free_pt ctr;
    AT.elim_pure (within_bounds _ _ _);
    match v with
    | None -> AT.return false
    | Some _ -> AT.return true

let compare (#t:eqtype)
            (a0 a1:array t)
            (l:U32.t { length a0 == length a1 /\ U32.v l == length a0})
  : Steel bool
    (varray a0 `star` varray a1)
    (fun _ -> varray a0 `star` varray a1)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
      asel a0 h0 == asel a0 h1 /\
      asel a1 h0 == asel a1 h1 /\
      b = (asel a0 h1 = asel a1 h1))
  = if l = 0ul
    then (
      let h = AT.get () in
      assert (Seq.equal (asel a0 h) (asel a1 h));
      AT.return true
    )
    else (
      let s0 = intro_varray_pts_to a0 in
      let s1 = intro_varray_pts_to a1 in
      let b = compare_pts a0 a1 l in
      elim_varray_pts_to a0 _;
      elim_varray_pts_to a1 _;
      AT.return b
    )
