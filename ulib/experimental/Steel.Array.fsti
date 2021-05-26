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

module Steel.Array
open Steel.Memory
open Steel.FractionalPermission
open Steel.Effect
open Steel.Effect.Atomic
open FStar.Ghost
module U32 = FStar.UInt32

(* escape hatches to avoid normalization by Steel tactics *)

let pfst
  (#t1 #t2: Type)
  (x: (t1 & t2))
: Pure t1
  (requires True)
  (ensures (fun y -> y == fst x))
= fst x

let psnd
  (#t1 #t2: Type)
  (x: (t1 & t2))
: Pure t2
  (requires True)
  (ensures (fun y -> y == snd x))
= snd x

/// A library for arrays in Steel

/// Abstract datatype for a Steel array of type [t]
val array (t:Type u#0) : Type u#0

/// Returns the length of the array. Usable for specification and proof purposes,
/// as modeled by the GTot effect
val len (#t: Type) (a: array t) : GTot U32.t
let length (#t: Type) (a: array t) : GTot nat = U32.v (len a)

/// Separation logic predicate indicating the validity of the array in the current memory
val is_array (#a:Type0) (r:array a) (p: perm) : slprop u#1

/// Selector for Steel arrays. It returns the contents in memory of the array.
/// The contents of an array of type [t] is a sequence of values of type [t]
/// whose length is the length of the array
val array_sel (#a:Type0) (r:array a) (p: perm) : selector (Seq.lseq a (length r)) (is_array r p)

/// Combining the elements above to create an array vprop

[@@ __steel_reduce__]
let varray' #a r p : vprop' =
  {hp = is_array r p;
   t = Seq.lseq a (length r);
   sel = array_sel r p}

[@@ __steel_reduce__]
let varrayp r p = VUnit (varray' r p)

[@@ __steel_reduce__; __reduce__]
let varray r = VUnit (varray' r full_perm)

/// A wrapper to access an array selector more easily.
/// Ensuring that the corresponding array vprop is in the context is done by
/// calling a variant of the framing tactic, as defined in Steel.Effect.Common
/// [@@ __steel_reduce__]
let asel (#a:Type) (#p:vprop) (r:array a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (varray r) /\ True)})
: GTot (Seq.lseq a (length r))
  = h (varray r)


/// Splitting an array into subarrays

val adjacent
  (#t: Type)
  (r1 r2: array t)
: Tot prop

val merge
  (#t: Type)
  (r1 r2: array t)
: Ghost (array t)
  (requires (adjacent r1 r2))
  (ensures (fun r -> length r == length r1 + length r2))

let merge_into
  (#t: Type)
  (r1 r2 r3: array t)
: Tot prop
= adjacent r1 r2 /\
  merge r1 r2 == r3

val merge_assoc
  (#t: Type)
  (r1 r2 r3: array t)
: Lemma
  (requires (adjacent r1 r2 /\ adjacent r2 r3))
  (ensures (
    adjacent r1 r2 /\ adjacent r2 r3 /\
    begin
      let r12 = merge r1 r2 in
      let r23 = merge r2 r3 in
      adjacent r1 r23 /\ adjacent r12 r3 /\
      merge r1 r23 == merge r12 r3
    end
  ))
  [SMTPat (merge (merge r1 r2) r3)]

val merge_zero_left
  (#t: Type)
  (r1 r2: array t)
: Lemma
  (requires (adjacent r1 r2 /\ length r1 == 0))
  (ensures (
    merge_into r1 r2 r2
  ))

val merge_zero_right
  (#t: Type)
  (r1 r2: array t)
: Lemma
  (requires (adjacent r1 r2 /\ length r2 == 0))
  (ensures (
    merge_into r1 r2 r1
  ))

val gsplit
  (#t: Type)
  (r: array t)
  (i: U32.t)
: Ghost (array t & array t)
  (requires (U32.v i <= length r))
  (ensures (fun (rl, rr) ->
    merge_into rl rr r /\
    length rl == U32.v i
  ))

val gsplit_unique
  (#t: Type)
  (r rl rr: array t)
: Lemma
  (requires (merge_into rl rr r))
  (ensures (
    (rl, rr) == gsplit r (len rl)
  ))

val splitp (#opened: _) (#t:Type) (a:array t) (p: perm) (i:U32.t)
  : SteelAtomic (array t & array t) opened
          (varrayp a p)
          (fun res -> varrayp (pfst res) p `star` varrayp (psnd res) p)
          (fun _ -> U32.v i <= length a)
          (fun h res h' ->
            let s = h (varrayp a p) in
            let sl = h' (varrayp (pfst res) p) in
            let sr = h' (varrayp (psnd res) p) in
            U32.v i <= length a /\
            res == gsplit a i /\
            sl == Seq.slice s 0 (U32.v i) /\
            sr == Seq.slice s (U32.v i) (length a) /\
            s == sl `Seq.append` sr
          )

let split (#opened: _) (#t:Type) (a:array t) (i:U32.t)
  : SteelAtomic (array t & array t) opened
          (varray a)
          (fun res -> varray (pfst res) `star` varray (psnd res))
          (fun _ -> U32.v i <= length a)
          (fun h res h' ->
            let s = h (varray a) in
            let sl = h' (varray (pfst res)) in
            let sr = h' (varray (psnd res)) in
            U32.v i <= length a /\
            res == gsplit a i /\
            sl == Seq.slice s 0 (U32.v i) /\
            sr == Seq.slice s (U32.v i) (length a) /\
            s == sl `Seq.append` sr
          )
=
  splitp _ _ i

val joinp (#opened: _) (#t:Type) (al ar:array t)
  (p: perm)
  : SteelAtomic (array t) opened
          (varrayp al p `star` varrayp ar p)
          (fun a -> varrayp a p)
          (fun _ -> adjacent al ar)
          (fun h a h' ->
            let s = h' (varrayp a p) in
            s == (h (varrayp al p) `Seq.append` h (varrayp ar p)) /\
            merge_into al ar a
          )

let join (#opened: _) (#t:Type) (al ar:array t)
  : SteelAtomic (array t) opened
          (varray al `star` varray ar)
          (fun a -> varray a)
          (fun _ -> adjacent al ar)
          (fun h a h' ->
            let s = h' (varray a) in
            s == (h (varray al) `Seq.append` h (varray ar)) /\
            merge_into al ar a
          )
=
  joinp _ _ _

/// A property telling that an array "is a full allocation unit"
/// that can be freed all at once (as opposed to a strict subarray of
/// some other array)
val freeable (#t: Type) (a: array t) : Tot prop

/// Allocates an array of length n, where all elements of the array initially are [x]
val alloc (#t:Type) (x:t) (n:U32.t)
  : Steel (array t)
             emp
             (fun r -> varray r)
             (requires fun _ -> True)
             (ensures fun _ r h1 ->
               asel r h1 == Seq.create (U32.v n) x /\
               freeable r
             )

/// Accesses index [i] in array [r], as long as [i] is in bounds and the array
/// is currently valid in memory

val indexp (#t:Type) (r:array t) (p: perm) (i:U32.t)
  : Steel t
             (varrayp r p)
             (fun _ -> varrayp r p)
             (requires fun _ -> U32.v i < length r)
             (ensures fun h0 x h1 ->
               let s = h1 (varrayp r p) in
               U32.v i < length r /\
               h0 (varrayp r p) == s /\
               x == Seq.index s (U32.v i))

let index (#t:Type) (r:array t) (i:U32.t)
  : Steel t
             (varray r)
             (fun _ -> varray r)
             (requires fun _ -> U32.v i < length r)
             (ensures fun h0 x h1 ->
               let s = asel r h1 in
               U32.v i < length r /\
               asel r h0 == s /\
               x == Seq.index s (U32.v i))
=
  indexp _ _ i

/// Updates index [i] in array [r] with value [x], as long as [i]
/// is in bounds and the array is currently valid in memory
val upd (#t:Type) (r:array t) (i:U32.t) (x:t)
  : Steel unit
             (varray r)
             (fun _ -> varray r)
             (requires fun h -> U32.v i < length r)
             (ensures fun h0 _ h1 ->
               U32.v i < length r /\
               asel r h1 == Seq.upd (asel r h0) (U32.v i) x)

/// Frees array [r], as long as it initially was a valid array in memory
val free (#t:Type) (r:array t)
  : Steel unit
             (varray r)
             (fun _ -> emp)
             (requires fun _ -> freeable r)
             (ensures fun _ _ _ -> True)

val share (#t:Type) (#uses:_) (a:array t) (p: perm)
  : SteelGhost perm uses
           (varrayp a p)
           (fun res -> varrayp a res `star` varrayp a res)
           (fun _ -> True)
           (fun h res h' ->
             h' (varrayp a res) == h (varrayp a p) /\
             res == half_perm p
           )

val gather (#t:Type) (#uses:_) (a:array t) (p1 p2: perm)
  : SteelGhost perm uses
           (varrayp a p1 `star` varrayp a p2)
           (fun res -> varrayp a res)
           (fun _ -> True)
           (fun h res h' ->
             h' (varrayp a res) == h (varrayp a p1) /\
             h' (varrayp a res) == h (varrayp a p2) /\
             res == p1 `sum_perm` p2
           )


(* AF: Non-selector version of the Array module, with permissions,
   currently unused in Steel
   TODO: Port this to the selector version

let contents (t:Type u#0) = erased (FStar.Seq.seq t)
let length #t (r:contents t) : GTot nat = Seq.length r
let perm = perm * erased nat
let full_perm (n:erased nat) : perm = full_perm, n
let is_writeable (p:perm) = fst p == Steel.FractionalPermission.full_perm
let is_freeable #t (r:contents t) (p:perm) = p == full_perm (length r)
let half_perm (p:perm) = half_perm (fst p), snd p
let sum_perm (p q:perm) = sum_perm (fst p) (fst q), snd p

val array (t:Type u#0) : Type u#0

// x:array int;
// is_array x full_perm (Seq.create 20 0) : slprop

val is_array (#t:_) (x:array t) (p:perm) (v:contents t) : slprop u#1

val alloc (#t:Type) (x:t) (n:U32.t)
  : SteelT (array t)
           (requires emp)
           (ensures fun a -> is_array a (full_perm (U32.v n)) (Seq.create (U32.v n) x))

val read (#t:Type) (#p:perm) (#r:contents t) (a:array t) (i:U32.t { U32.v i < length r })
  : Steel t
          (is_array a p r)
          (fun _ -> is_array a p r)
          (fun _ -> True)
          (fun _ x _ -> x == Seq.index r (U32.v i))

val write (#t:Type) (#p:perm{is_writeable p}) (#r:contents t) (a:array t) (i:U32.t { U32.v i < length r }) (x:t)
  : SteelT unit
          (is_array a p r)
          (fun _ -> is_array a p (Seq.upd r (U32.v i) x))

val adjacent (#t:_) (al ar:array t) : prop

val split (#t:Type) (#p:perm) (#r:contents t) (a:array t) (i:U32.t { U32.v i <= length r })
  : Steel (array t & array t)
          (is_array a p r)
          (fun (al, ar) ->
             let prefix, suffix = Seq.split r (U32.v i) in
             is_array al p prefix `star` is_array ar p suffix)
          (fun _ -> True)
          (fun _ (al, ar) _ -> adjacent al ar)

val join (#t:Type) (#p:perm) (#rl #rr:contents t) (al ar:array t)
  : Steel (array t)
          (is_array al p rl `star` is_array ar p rr)
          (fun a -> is_array a p (Seq.append rl rr))
          (fun _ -> adjacent al ar)
          (fun _ _ _ -> True)

val share (#t:Type) (#uses:_) (#p:perm) (#r:contents t) (a:array t) (i:U32.t { U32.v i < length r })
  : SteelGhostT unit uses
           (is_array a p r)
           (fun _ -> is_array a (half_perm p) r `star` is_array a (half_perm p) r)

val gather (#t:Type) (#uses:_) (#p #p':perm) (#r #r':contents t) (a:array t) (i:U32.t { U32.v i < length r })
  : SteelGhostT unit uses
           (is_array a p r `star` is_array a p' r')
           (fun _ -> is_array a (sum_perm p p') r)

val free (#t:Type) (#r:contents t) (#p:perm{is_freeable r p}) (a:array t)
  : SteelT unit
           (is_array a p r)
           (fun _ -> emp)
*)
