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
let array t = l:erased nat & ref (Seq.lseq t l)

let length #t (x:array t) = dfst x
let is_array r = ptr (dsnd r)
let array_sel r = ptr_sel (dsnd r)

let varray_pts_to (#t:Type) (a:array t) (x:elseq t (length a))
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
