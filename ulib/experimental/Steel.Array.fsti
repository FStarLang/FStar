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
open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open FStar.Ghost
open Steel.FractionalPermission
module U32 = FStar.UInt32

/// A library for arrays in Steel

/// The contents of an array of type [t] is a sequence of values of type [t]
let contents (t:Type u#0) (n:nat) = FStar.Seq.lseq t n

/// Abstract datatype for a Steel array of type [t]
val array (t:Type u#0) : Type u#0

/// Returns the length of the array. Usable for specification and proof purposes,
/// as modeled by the GTot effect
val length (#t:_) (r:array t) : GTot nat

/// Separation logic predicate indicating the validity of the array in the current memory, p is the fractional permission on the array
val is_array (#a:Type0) (r:array a) (p:perm) : slprop u#1

/// Selector for Steel arrays. It returns the contents in memory of the array
val array_sel (#a:Type0) (r:array a) (p:perm)
  : selector (contents a (length r)) (is_array r p)

/// Combining the elements above to create an array vprop
[@@ __steel_reduce__]
let varray' #a r p : vprop' =
  {hp = is_array r p;
   t = contents a (length r);
   sel = array_sel r p}

[@@ __steel_reduce__]
unfold
let varray r p = VUnit (varray' r p)

/// A wrapper to access an array selector more easily.
/// Ensuring that the corresponding array vprop is in the context is done by
/// calling a variant of the framing tactic, as defined in Steel.Effect.Common
[@@ __steel_reduce__]
let asel (#a:Type) (#p:vprop) (r:array a) (perm:perm)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (varray r perm) /\ True)})
  = h (varray r perm)

/// We also provide an indexed assertion to represent an array
/// without a selector

/// The main indexed assertion
val varray_pts_to (#t:Type) (a:array t) (p:perm) (x:Seq.lseq t (length a))
  : vprop

type elseq a (n:nat) = Ghost.erased (Seq.lseq a n)

/// Converting a `varray` into a `varray_pts_to`
val intro_varray_pts_to (#t:_)
                        (#opened:inames)
                        (#p:perm)
                        (a:array t)
  : SteelGhost (elseq t (length a)) opened
    (varray a p)
    (fun x -> varray_pts_to a p x)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
      Ghost.reveal x == asel a p h0)

/// Converting a `varray_pts_to` to a `varray`
val elim_varray_pts_to (#t:_)
                       (#opened:inames)
                       (#p:perm)
                       (a:array t)
                       (c:elseq t (length a))
  : SteelGhost unit opened
    (varray_pts_to a p c)
    (fun _ -> varray a p)
    (requires fun _ -> True)
    (ensures fun _ _ h1 ->
      asel a p h1 == Ghost.reveal c)

/// Allocates an array of length n, where all elements of the array initially are [x]
val malloc (#t:Type) (x:t) (n:U32.t)
  : Steel (array t)
          emp
          (fun r -> varray r full_perm)
          (requires fun _ -> True)
          (ensures fun _ r h1 ->
            length r == U32.v n /\
            asel r full_perm h1 == Seq.create (U32.v n) x)

/// Accesses index [i] in array [r], as long as [i] is in bounds and the array
/// is currently valid in memory
val index (#t:Type) (#p:perm) (r:array t) (i:U32.t)
  : Steel t
             (varray r p)
             (fun _ -> varray r p)
             (requires fun h -> U32.v i < length r)
             (ensures fun h0 x h1 ->
               U32.v i < length r /\
               asel r p h0 == asel r p h1 /\
               x == Seq.index (asel r p h1) (U32.v i))

/// Updates index [i] in array [r] with value [x], as long as [i]
/// is in bounds and the array is currently valid in memory
val upd (#t:Type) (r:array t) (i:U32.t) (x:t)
  : Steel unit
             (varray r full_perm)
             (fun _ -> varray r full_perm)
             (requires fun h -> U32.v i < length r)
             (ensures fun h0 _ h1 ->
               U32.v i < length r /\
               asel r full_perm h1 == Seq.upd (asel r full_perm h0) (U32.v i) x)

/// Frees array [r], as long as it initially was a valid array in memory
val free (#t:Type) (r:array t)
  : Steel unit
             (varray r full_perm)
             (fun _ -> emp)
             (requires fun _ -> True)
             (ensures fun _ _ _ -> True)


/// Copies the contents of a0 to a1
val memcpy (#t:_) (#p0:perm)
           (a0 a1:array t)
           (i:U32.t)
  : Steel unit
    (varray a0 p0 `star` varray a1 full_perm)
    (fun _ -> varray a0 p0  `star` varray a1 full_perm)
    (requires fun _ ->
       U32.v i == length a0 /\ length a0 == length a1)
    (ensures fun h0 _ h1 ->
      length a0 == length a1 /\
      asel a0 p0 h0 == asel a0 p0 h1 /\
      asel a1 full_perm h1 == asel a0 p0 h1)

/// Decides whether the contents of a0 and a1 are equal
val compare (#t:eqtype) (#p0 #p1:perm)
            (a0 a1:array t)
            (l:U32.t { length a0 == length a1 /\ U32.v l == length a0})
  : Steel bool
    (varray a0 p0 `star` varray a1 p1)
    (fun _ -> varray a0 p0 `star` varray a1 p1)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
      asel a0 p0 h0 == asel a0 p0 h1 /\
      asel a1 p1 h0 == asel a1 p1 h1 /\
      b = (asel a0 p0 h1 = asel a1 p1 h1))



(* AF: Non-selector version of the Array module, currently unused in Steel
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
