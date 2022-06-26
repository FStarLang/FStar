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
open FStar.Seq
open Steel.ST.Coercions
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

let repr (#t:_) (r:array t) = FStar.Seq.lseq t (length r)

/// The main representation predicate
let pts_to (#t:Type)
           (a:array t)
           (p:perm)
           ([@@@smt_fallback]x:seq t)
  : vprop
  = exists_ (fun (r:repr a) ->
      pure (eq2 #(seq t) r x) `star`
      A.varray_pts_to a p r)

let intro_pts_to #t #o #p (a:array t) (s:repr a) (s':seq t)
  : STGhost unit o
      (A.varray_pts_to a p s)
      (fun _ -> pts_to a p s')
      (requires s == s')
      (ensures fun _ -> True)
  = intro_pure (s == s');
    intro_exists s (fun (s:repr a) -> pure (s == s') `star` A.varray_pts_to a p s)

let elim_pts_to #t #o #p (a:array t) (s:seq t)
  : STGhost (erased (repr a)) o
      (pts_to a p s)
      (fun s' -> A.varray_pts_to a p s')
      (requires True)
      (ensures fun s' -> eq2 #(seq t) s' s)
  = let s = elim_exists () in
    elim_pure _;
    s

let pts_to_length #t #o #p (a:array t) (s:seq t)
  : STGhost unit o
      (pts_to a p s)
      (fun _ -> pts_to a p s)
      (requires True)
      (ensures fun _ -> Seq.length s == length a)
  = let s' = elim_pts_to a s in
    intro_pts_to a s' s

let alloc_pt (#t:Type)
             (x:t)
             (n:U32.t)
  : SE.SteelT (larray t (U32.v n))
           emp
           (fun r -> pts_to r full_perm (Seq.create (U32.v n) x))
  = let a = A.malloc x n in
    let s = A.intro_varray_pts_to a in
    intro_pts_to a s (Seq.create (U32.v n) x);
    return a

let alloc (#t:Type)
          (x:t)
          (n:U32.t)
  : STT (larray t (U32.v n))
        emp
        (fun r -> pts_to r full_perm (Seq.create (U32.v n) x))
  = let x = coerce_steel (fun _ -> alloc_pt x n) in x

let read_pt (#t:Type)
            (#p:perm)
            (a:array t)
            (#s:erased (seq t))
            (i:U32.t { U32.v i < Seq.length s })
  : SE.Steel t
       (pts_to a p s)
       (fun _ -> pts_to a p s)
       (requires fun _ -> True)
       (ensures fun _ v _ ->
         v == Seq.index s (U32.v i))
  = let s' = elim_pts_to a s in
    A.elim_varray_pts_to a s';
    let x = A.index a i in
    let _ = A.intro_varray_pts_to a in
    SEA.change_equal_slprop
              (A.varray_pts_to _ _ _)
              (A.varray_pts_to _ _ _);
    intro_pts_to a s' s;
    return x

let read (#t:Type)
         (#p:perm)
         (a:array t)
         (#s:erased (seq t))
         (i:U32.t { U32.v i < Seq.length s })
  : ST t
       (pts_to a p s)
       (fun _ -> pts_to a p s)
       (requires True)
       (ensures fun v ->
         v == Seq.index s (U32.v i))
  = let x = coerce_steel (fun _ -> read_pt a i) in x

let write_pt (#t:Type)
             (a:array t)
             (#s:erased (seq t))
             (i:U32.t { U32.v i < Seq.length s })
             (x:t)
  : SE.SteelT unit
       (pts_to a full_perm s)
       (fun _ -> pts_to a full_perm (Seq.upd s (U32.v i) x))
  = let s' = elim_pts_to a s in
    A.elim_varray_pts_to a s';
    A.upd a i x;
    let s'' = A.intro_varray_pts_to a in
    intro_pts_to a _ _;
    return ()

let write (#t:Type)
          (a:array t)
          (#s:erased (seq t))
          (i:U32.t { U32.v i < Seq.length s })
          (x:t)
  : STT unit
       (pts_to a full_perm s)
       (fun _ -> pts_to a full_perm (Seq.upd s (U32.v i) x))
  = coerce_steel (fun _ -> write_pt a i x); ()

let free_pt (#t:Type) (a:array t) (#s:erased (repr a))
  : SE.SteelT unit
       (A.varray_pts_to a full_perm s)
       (fun _ -> emp)
  = A.elim_varray_pts_to a s;
    A.free a;
    return ()

let free (#t:Type) (a:array t)
  : STT unit
       (exists_ (pts_to a full_perm))
       (fun _ -> emp)
  = let _ = elim_exists () in
    let s = elim_pts_to a _ in
    coerce_steel (fun _ -> free_pt a #s)

let memcpy_pt (#t:_)
              (#p0:perm)
              (a0 a1:array t)
              (#s0 #s1:erased (seq t))
              (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : SE.SteelT unit
      (pts_to a0 p0 s0 `star` pts_to a1 full_perm s1)
      (fun _ -> pts_to a0 p0 s0  `star` pts_to a1 full_perm s0)
  = let _ = elim_pts_to a0 s0 in
    let _ = elim_pts_to a1 s1 in
    A.elim_varray_pts_to a0 _;
    A.elim_varray_pts_to a1 _;
    A.memcpy a0 a1 l;
    let _ = A.intro_varray_pts_to a0 in
    let _ = A.intro_varray_pts_to a1 in
    intro_pts_to a0 _ _;
    intro_pts_to a1 _ _;
    return ()

let memcpy (#t:_)
           (#p0:perm)
           (a0 a1:array t)
           (#s0 #s1:erased (seq t))
           (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : STT unit
    (pts_to a0 p0 s0 `star` pts_to a1 full_perm s1)
    (fun _ -> pts_to a0 p0 s0  `star` pts_to a1 full_perm s0)
  = coerce_steel (fun _ -> memcpy_pt a0 a1 l); ()

let compare_pt (#t:eqtype)
               (#p0 #p1:perm)
               (a0 a1:array t)
               (#s0 #s1:erased (seq t))
               (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : SE.Steel bool
    (pts_to a0 p0 s0 `star` pts_to a1 p1 s1)
    (fun _ -> pts_to a0 p0 s0 `star` pts_to a1 p1 s1)
    (requires fun _ -> True)
    (ensures fun _ b _ -> b <==> eq2 #(Seq.seq t) s0 s1)
  = let _ = elim_pts_to a0 _ in
    let _ = elim_pts_to a1 _ in
    A.elim_varray_pts_to a0 _;
    A.elim_varray_pts_to a1 _;
    let b = A.compare a0 a1 l in
    let _ = A.intro_varray_pts_to a0 in
    let _ = A.intro_varray_pts_to a1 in
    intro_pts_to a0 _ _;
    intro_pts_to a1 _ _;
    return b

let compare (#t:eqtype)
            (#p0 #p1:perm)
            (a0 a1:array t)
            (#s0 #s1:erased (seq t))
            (l:U32.t { U32.v l == length a0 /\ length a0 == length a1 } )
  : ST bool
    (pts_to a0 p0 s0 `star` pts_to a1 p1 s1)
    (fun _ -> pts_to a0 p0 s0 `star` pts_to a1 p1 s1)
    (requires True)
    (ensures fun b -> b <==> eq2 #(Seq.seq t) s0 s1)
  = let b = coerce_steel (fun _ -> compare_pt a0 a1 l) in
    return b
