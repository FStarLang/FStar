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

module Steel.ST.Array
open FStar.Ghost
open Steel.ST.Util
module U32 = FStar.UInt32
module A = Steel.Array
module SEA = Steel.Effect.Atomic
module SE = Steel.Effect

/// Abstract datatype for a Steel array of type [t]
let array (t:Type u#0)
  : Type u#0
  = A.array t

/// Returns the length of the array. Usable for specification and proof purposes,
/// as modeled by the GTot effect
let length (#t:_) (r:array t)
  : GTot nat
  = A.length r

/// The main representation predicate
let pts_to (#t:Type)
           (a:array t)
           ([@@@smt_fallback]x:repr a)
  : vprop
  = A.varray_pts_to a x

let alloc_pt (#t:Type)
             (x:t)
             (n:U32.t)
  : SE.SteelT (larray t (U32.v n))
           emp
           (fun r -> pts_to r (Seq.create (U32.v n) x))
  = let a = A.malloc x n in
    let s = A.intro_varray_pts_to a in
    SEA.change_equal_slprop
              (A.varray_pts_to _ _)
              (pts_to _ _);
    return a

let alloc (#t:Type)
          (x:t)
          (n:U32.t)
  : STT (larray t (U32.v n))
        emp
        (fun r -> pts_to r (Seq.create (U32.v n) x))
  = let x = coerce_steel (fun _ -> alloc_pt x n) in x

let read_pt (#t:Type)
            (a:array t)
            (#s:erased (repr a))
            (i:U32.t { U32.v i < length a })
  : SE.Steel t
       (pts_to a s)
       (fun _ -> pts_to a s)
       (requires fun _ -> True)
       (ensures fun _ v _ ->
         v == Seq.index s (U32.v i))
  = A.elim_varray_pts_to a s;
    let x = A.index a i in
    let _ = A.intro_varray_pts_to a in
    SEA.change_equal_slprop
              (A.varray_pts_to _ _)
              (pts_to _ _);
    return x


let read (#t:Type)
         (a:array t)
         (#s:erased (repr a))
         (i:U32.t { U32.v i < length a })
  : ST t
       (pts_to a s)
       (fun _ -> pts_to a s)
       (requires True)
       (ensures fun v ->
         v == Seq.index s (U32.v i))
  = let x = coerce_steel (fun _ -> read_pt a i) in x

let write_pt (#t:Type)
          (a:array t)
          (#s:erased (repr a))
          (i:U32.t { U32.v i < length a })
          (x:t)
  : SE.SteelT unit
       (pts_to a s)
       (fun _ -> pts_to a (Seq.upd s (U32.v i) x))
  = A.elim_varray_pts_to a s;
    A.upd a i x;
    let _ = A.intro_varray_pts_to a in
    SEA.change_equal_slprop
              (A.varray_pts_to _ _)
              (pts_to _ _);
    return ()

let write (#t:Type)
          (a:array t)
          (#s:erased (repr a))
          (i:U32.t { U32.v i < length a })
          (x:t)
  : STT unit
       (pts_to a s)
       (fun _ -> pts_to a (Seq.upd s (U32.v i) x))
  = coerce_steel (fun _ -> write_pt a i x); ()

/// Frees array [r], as long as it initially was a valid array in memory
let free_pt (#t:Type) (a:array t) (#s:erased (repr a))
  : SE.SteelT unit
       (pts_to a s)
       (fun _ -> emp)
  = A.elim_varray_pts_to a s;
    A.free a;
    return ()

let free (#t:Type) (a:array t)
  : STT unit
       (exists_ (pts_to a))
       (fun _ -> emp)
  = let s = elim_exists () in
    coerce_steel (fun _ -> free_pt a #s)


let memcpy_pt (#t:_)
              (a0 a1:array t)
              (#s0:erased (repr a0))
              (#s1:erased (repr a1))
              (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : SE.SteelT unit
      (pts_to a0 s0 `star` pts_to a1 s1)
      (fun _ -> pts_to a0 s0  `star` pts_to a1 s0)
  = A.elim_varray_pts_to a0 s0;
    A.elim_varray_pts_to a1 s1;
    A.memcpy a0 a1 l;
    let _ = A.intro_varray_pts_to a0 in
    let _ = A.intro_varray_pts_to a1 in
    SEA.change_equal_slprop
              (A.varray_pts_to a0 _)
              (pts_to a0 _);
    SEA.change_equal_slprop
              (A.varray_pts_to a1 _)
              (pts_to a1 _);
    return ()

let memcpy (#t:_)
           (a0 a1:array t)
           (#s0:erased (repr a0))
           (#s1:erased (repr a1))
           (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : STT unit
    (pts_to a0 s0 `star` pts_to a1 s1)
    (fun _ -> pts_to a0 s0  `star` pts_to a1 s0)
  = coerce_steel (fun _ -> memcpy_pt a0 a1 l); ()

let compare_pt (#t:eqtype)
               (a0 a1:array t)
               (#s0:erased (repr a0))
               (#s1:erased (repr a1))
               (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : SE.Steel bool
    (pts_to a0 s0 `star` pts_to a1 s1)
    (fun _ -> pts_to a0 s0 `star` pts_to a1 s1)
    (requires fun _ -> True)
    (ensures fun _ b _ -> b <==> eq2 #(Seq.seq t) s0 s1)
  = A.elim_varray_pts_to a0 s0;
    A.elim_varray_pts_to a1 s1;
    let b = A.compare a0 a1 l in
    let _ = A.intro_varray_pts_to a0 in
    let _ = A.intro_varray_pts_to a1 in
    SEA.change_equal_slprop
              (A.varray_pts_to a0 _)
              (pts_to a0 _);
    SEA.change_equal_slprop
              (A.varray_pts_to a1 _)
              (pts_to a1 _);
    return b

let compare (#t:eqtype)
            (a0 a1:array t)
            (#s0:erased (repr a0))
            (#s1:erased (repr a1))
            (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : ST bool
    (pts_to a0 s0 `star` pts_to a1 s1)
    (fun _ -> pts_to a0 s0 `star` pts_to a1 s1)
    (requires True)
    (ensures fun b -> b <==> eq2 #(Seq.seq t) s0 s1)
  = let b = coerce_steel (fun _ -> compare_pt a0 a1 l) in
    return b
