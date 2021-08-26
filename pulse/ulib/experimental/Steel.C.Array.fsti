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

module Steel.C.Array
include Steel.C.StdInt
open Steel.Memory
open Steel.FractionalPermission
open Steel.Effect
open FStar.Ghost
open Steel.Effect.Atomic

open Steel.C.Typedef
open Steel.C.PCM
open Steel.C.Fields
open Steel.C.Typenat

#set-options "--ide_id_info_off"

/// A library for arrays in Steel
/// TODO: add back support for fractional permissions, or even any element view

val array_pcm_carrier (t: Type u#0) (n: Ghost.erased size_t) : Type u#0

val array_pcm (t: Type u#0) (n: Ghost.erased size_t) : Tot (Steel.C.PCM.pcm (array_pcm_carrier t n))

// FIXME: how to produce array type t[n] as the type of some struct field?
let array_view_type (t: Type u#0) (n: size_t)
: Type u#0 =
  Seq.lseq t (size_v n)

/// A variant of array_view_type, which records the length of the
/// array in Type as a Steel.C.Typenat, for extraction
let size_t_of (n': Type u#0) = n:size_t{n' == nat_t_of_nat (size_v n)}
let array_view_type_sized (t: Type u#0) (n': Type u#0) (n: size_t_of n')
: Type u#0
= array_view_type t n

val array_view (t: Type u#0) (n: size_t)
  : Pure (Steel.C.Ref.sel_view (array_pcm t n) (array_view_type t n) false)
    (requires (size_v n > 0))
    (ensures (fun _ -> True))

/// Abstract datatype for a Steel array of type [t]
/// Should extract to t*
val array (base: Type u#0) (t:Type u#0) : Type u#0

/// Returns the length of the array. Usable for specification and proof purposes,
/// as modeled by the GTot effect
val len (#base: Type) (#t: Type) (a: array base t) : GTot size_t
let length (#base: Type) (#t: Type) (a: array base t) : GTot nat = size_v (len a)

// TODO 
val array_is_unit (t: Type0) (n: size_t) (a: array_pcm_carrier t n)
: b:bool{b <==> a == one (array_pcm t n)}

[@@c_struct]
let array_typedef_sized (t: Type0) (n': Type0) (n: size_t_of n'{size_v n > 0}): typedef = {
  carrier = array_pcm_carrier t n;
  pcm = array_pcm t n;
  view_type = array_view_type_sized t n' n;
  view = array_view t n;
  is_unit = array_is_unit t n;
}

/// Combining the elements above to create an array vprop
/// TODO: generalize to any view

// val g_array_as_ref (#base: Type u#0) (#t: Type u#0) (a: array base t)
//   : GTot (Steel.C.Reference.ref base (array_view_type t (len a)) (array_pcm t (len a)))

// [@@ __steel_reduce__]
// let varray (#base: Type) (#t: Type) (x: array base t) : Tot vprop
// = Steel.C.Ref.pts_to_view (g_array_as_ref x) (array_view t (len x))

val varray_hp (#base: Type) (#t: Type) (x: array base t) : Tot (slprop u#1)
val varray_sel (#base: Type) (#t: Type) (x: array base t) : Tot (selector (array_view_type t (len x)) (varray_hp x))

[@@ __steel_reduce__ ]
let varray' (#base: Type) (#t: Type) (x: array base t) : Tot vprop' = {
  hp = varray_hp x;
  t = array_view_type t (len x);
  sel = varray_sel x;
}

[@@ __steel_reduce__ ]
let varray (#base: Type) (#t: Type) (x: array base t) : Tot vprop =
  VUnit (varray' x)

val g_mk_array (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n))
: Ghost (array base t)
  (requires (size_v n > 0))
  (ensures (fun a -> len a == Ghost.reveal n))

val intro_varray (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n))
  (_: squash (size_v n > 0))
: Steel (array base t)
    (Steel.C.Ref.pts_to_view r (array_view t n))
    (fun a -> varray a)
    (requires fun _ -> True)
  (ensures (fun h a h' ->
    a == g_mk_array r /\
    h' (varray a) == h (Steel.C.Ref.pts_to_view r (array_view t n))
  ))

val elim_varray (#inames: _) (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n)) (a: array base t) (_: squash (size_v n > 0))
: SteelGhost unit inames
  (varray a)
  (fun _ -> Steel.C.Ref.pts_to_view r (array_view t n))
  (requires fun _ -> a == g_mk_array r)
  (ensures (fun h _ h' ->
    a == g_mk_array r /\
    h (varray a) == h' (Steel.C.Ref.pts_to_view r (array_view t n))
  ))


/// Splitting an array into subarrays

val adjacent
  (#base: Type)
  (#t: Type)
  (r1 r2: array base t)
: Tot prop

val merge
  (#base: Type)
  (#t: Type)
  (r1 r2: array base t)
: Ghost (array base t)
  (requires (adjacent r1 r2))
  (ensures (fun r -> length r == length r1 + length r2))

let merge_into
  (#base: Type)
  (#t: Type)
  (r1 r2 r3: array base t)
: Tot prop
= adjacent r1 r2 /\
  merge r1 r2 == r3

val merge_assoc
  (#base: Type)
  (#t: Type)
  (r1 r2 r3: array base t)
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

val gsplit
  (#base: Type)
  (#t: Type)
  (r: array base t)
  (i: size_t)
: Ghost (array base t & array base t)
  (requires (size_v i <= length r))
  (ensures (fun (rl, rr) ->
    merge_into rl rr r /\
    length rl == size_v i
  ))

[@erasable]
noeq
type gpair (a b: Type) = | GPair: (fst: a) -> (snd: b) -> gpair a b

val split (#opened: _) (#base: Type) (#t:Type) (a:array base t) (i:size_t)
  : SteelGhost (array base t `gpair` array base t) opened
          (varray a)
          (fun res -> varray (GPair?.fst res) `star` varray (GPair?.snd res))
          (fun _ -> size_v i <= length a)
          (fun h res h' ->
            let s = h (varray a) in
            let sl = h' (varray (GPair?.fst res)) in
            let sr = h' (varray (GPair?.snd res)) in
            size_v i <= length a /\
            GPair?.fst res == fst (gsplit a i) /\
            GPair?.snd res == snd (gsplit a i) /\
            sl == Seq.slice s 0 (size_v i) /\
            sr == Seq.slice s (size_v i) (length a) /\
            s == sl `Seq.append` sr
          )

val split_left (#base: _) (#t:Type) (#opened: _) (a:array base t) (i:size_t)
  : SteelAtomicBase (array base t) false opened Unobservable
          (varray a)
          (fun _ -> varray a)
          (fun _ -> size_v i <= length a)
          (fun h res h' ->
            h' (varray a) == h (varray a) /\
            size_v i <= length a /\
            res == fst (gsplit a i)
          )

val split_right (#base: _) (#t:Type) (#opened: _) (a:array base t) (i:size_t)
  : SteelAtomicBase (array base t) false opened Unobservable
          (varray a)
          (fun _ -> varray a)
          (fun _ -> size_v i <= length a)
          (fun h res h' ->
            h' (varray a) == h (varray a) /\
            size_v i <= length a /\
            res == snd (gsplit a i)
          )

val join' (#opened: _) (#base: _) (#t:Type) (al ar:array base t)
  : SteelGhost (Ghost.erased (array base t)) opened
          (varray al `star` varray ar)
          (fun a -> varray a)
          (fun _ -> adjacent al ar)
          (fun h a h' ->
            let s = h' (varray a) in
            s == (h (varray al) `Seq.append` h (varray ar)) /\
            merge_into al ar a
          )

val joinc (#base: _) (#t:Type) (#opened: _) (al ar:array base t)
  : SteelAtomicBase (array base t) false opened Unobservable
          (varray al `star` varray ar)
          (fun a -> varray al `star` varray ar)
          (fun _ -> adjacent al ar)
          (fun h a h' ->
            h' (varray al) == h (varray al) /\
            h' (varray ar) == h (varray ar) /\
            merge_into al ar a
          )

inline_for_extraction
let join (#opened: _) (#base: _) (#t:Type) (al ar:array base t)
  : SteelAtomicBase (array base t) false opened Unobservable
          (varray al `star` varray ar)
          (fun a -> varray a)
          (fun _ -> adjacent al ar)
          (fun h a h' ->
            let s = h' (varray a) in
            s == (h (varray al) `Seq.append` h (varray ar)) /\
            merge_into al ar a
          )
=
  let a = joinc al ar in
  let ga = join' al ar in
  change_equal_slprop
    (varray ga)
    (varray a);
  return a

/// Converting an array into a pointer, after it has been split to an array of size 1
/// Those two functions should extract to identity functions

val g_ref_of_array
  (#base: Type) (#t:Type0) (r:array base t)
: Ghost (Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
  (requires (length r == 1))
  (ensures (fun _ -> True))

val ref_of_array (#base: Type) (#t:Type0) (r:array base t)
  : Steel (Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
             (varray r)
             (fun r' -> Steel.C.Ref.pts_to_view r' (Steel.C.Opt.opt_view t))
             (requires fun _ -> length r == 1)
             (ensures fun h0 r' h1 ->
               let s = h0 (varray r) in
               Seq.length s == 1 /\
               g_ref_of_array r == r' /\
               h1 (Steel.C.Ref.pts_to_view r' (Steel.C.Opt.opt_view t)) == Seq.index s 0
             )

val array_of_ref (#inames: _) (#base: Type) (#t:Type0) (r': array base t) (r: Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
  : SteelGhost unit inames
             (Steel.C.Ref.pts_to_view r (Steel.C.Opt.opt_view t))
             (fun _ -> varray r')
             (requires fun _ -> length r' == 1 /\ g_ref_of_array r' == r)
             (ensures fun h0 _ h1 ->
               let s = h1 (varray r') in
               Seq.length s == 1 /\
               g_ref_of_array r' == r /\
               h0 (Steel.C.Ref.pts_to_view r (Steel.C.Opt.opt_view t)) == Seq.index s 0
             )

// this function should be used only to pass a pointer as an argument to a function that expects an array

val mk_array_of_ref (#base: Type) (#t:Type0) (r: Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
  : Steel (array base t)
             (Steel.C.Ref.pts_to_view r (Steel.C.Opt.opt_view t))
             (fun r' -> varray r')
             (requires fun _ -> True)
             (ensures fun h0 r' h1 ->
               let s = h1 (varray r') in
               Seq.length s == 1 /\
               g_ref_of_array r' == r /\
               h0 (Steel.C.Ref.pts_to_view r (Steel.C.Opt.opt_view t)) == Seq.index s 0
             )


/// Accesses index [i] in array [r], as long as [i] is in bounds and the array
/// is currently valid in memory

val index (#base: Type) (#t:Type) (r:array base t) (i:size_t)
  : Steel t
             (varray r)
             (fun _ -> varray r)
             (requires fun _ -> size_v i < length r)
             (ensures fun h0 x h1 ->
               let s = h1 (varray r) in
               size_v i < length r /\
               h0 (varray r) == s /\
               x == Seq.index s (size_v i))

/// Updates index [i] in array [r] with value [x], as long as [i]
/// is in bounds and the array is currently valid in memory
val upd (#base: Type) (#t:Type) (r:array base t) (i:size_t) (x:t)
  : Steel unit
             (varray r)
             (fun _ -> varray r)
             (requires fun h -> size_v i < length r)
             (ensures fun h0 _ h1 ->
               size_v i < length r /\
               h1 (varray r) == Seq.upd (h0 (varray r)) (size_v i) x)
