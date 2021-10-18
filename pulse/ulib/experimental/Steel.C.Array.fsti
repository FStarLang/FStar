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
include Steel.C.StdInt.Base
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
/// We model it as three parts:
/// - a pure part, which represents the beginning of the array, and should extract to t*
/// - a ghost part, which represents the end of the array, and should be erased at extraction
/// - a refinement, because KReMLin does not support inlining of dependent pair types where one part is ghost.
val array_or_null_from (base: Type0) (t: Type0) : Tot Type0
[@@erasable]
val array_or_null_to (base: Type0) (t: Type0) : Tot Type0
val array_or_null_spec (#base: Type0) (#t: Type0) (x: (array_or_null_from base t & array_or_null_to base t)) : Tot prop
inline_for_extraction
let array_or_null (base: Type u#0) (t: Type u#0) : Type u#0 = (x: (array_or_null_from base t & array_or_null_to base t) { array_or_null_spec x })

/// Returns the length of the array. Usable for specification and proof purposes,
/// as modeled by the GTot effect
val len (#base: Type) (#t: Type) (a: array_or_null base t) : GTot size_t
let length (#base: Type) (#t: Type) (a: array_or_null base t) : GTot nat = size_v (len a)


val null_from (base: Type u#0) (t: Type u#0) : Tot (array_or_null_from base t) 
val null_to (base: Type u#0) (t: Type u#0) : Pure (array_or_null_to base t) (requires True) (ensures (fun r0 ->
  array_or_null_spec (null_from base t, r0) /\
  len (null_from base t, r0) == zero_size))

inline_for_extraction
let null (base: Type u#0) (t: Type u#0) : Pure (array_or_null base t) (requires True) (ensures (fun r -> len r == zero_size))
= (null_from base t, null_to base t)
val g_is_null (#base: Type) (#t: Type) (a: array_or_null base t) : Ghost bool (requires True) (ensures (fun res -> res == true <==> a == null base t))
inline_for_extraction
noextract
let array (base: Type u#0) (t:Type u#0) : Type u#0 = (a: array_or_null base t { g_is_null a == false })

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

val varray_hp (#base: Type0) (#t: Type0) (x: array base t) : Tot (slprop u#1)

val varray_sel (#base: Type0) (#t: Type0) (x: array base t) : GTot (selector (array_view_type t (len x)) (varray_hp x))

[@@ __steel_reduce__ ]
let varray' (#base: Type) (#t: Type) (x: array base t) : GTot vprop' = {
  hp = varray_hp x;
  t = array_view_type t (len x);
  sel = varray_sel x;
}

[@@ __steel_reduce__ ]
let varray (#base: Type) (#t: Type) (x: array base t) : Tot vprop =
  VUnit (varray' x)

val g_mk_array (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n))
  (a: array base t)
: Tot prop

val g_mk_array_weak
  (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n))
  (a: array base t)
: Lemma
  (requires (g_mk_array r a))
  (ensures (
    size_v n > 0 /\
    len a == Ghost.reveal n
  ))
  [SMTPat (g_mk_array r a)]

val g_mk_array_from
  (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n))
  (a: array_or_null_from base t)
: Tot prop

val g_mk_array_to
  (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n))
  (a: array_or_null_from base t)
: Pure (array_or_null_to base t)
  (requires (g_mk_array_from r a))
  (ensures (fun a' ->
    let a0 = (a, a') in
    array_or_null_spec a0 /\
    g_is_null a0 == false /\
    g_mk_array r a0
  ))

val intro_varray_from (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n))
  (_: squash (size_v n > 0))
: Steel (al: array_or_null_from base t { g_mk_array_from r al })
    (Steel.C.Ref.pts_to_view r (array_view t n))
    (fun al -> varray (al, g_mk_array_to r al))
    (requires fun _ -> True)
  (ensures (fun h al h' ->
    let a = (al, g_mk_array_to r al) in
    g_mk_array r a /\
    h' (varray a) == h (Steel.C.Ref.pts_to_view r (array_view t n))
  ))

inline_for_extraction
let intro_varray (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n))
  (_: squash (size_v n > 0))
: Steel (array base t)
    (Steel.C.Ref.pts_to_view r (array_view t n))
    (fun a -> varray a)
    (requires fun _ -> True)
  (ensures (fun h a h' ->
    g_mk_array r a /\
    h' (varray a) == h (Steel.C.Ref.pts_to_view r (array_view t n))
  ))
=
  let al = intro_varray_from r () in
  let a = (al, g_mk_array_to r al) in
  change_equal_slprop
    (varray (al, g_mk_array_to r al))
    (varray a);
  return a

val elim_varray (#inames: _) (#base: Type u#0) (#t: Type u#0) (#n: size_t) (r: Steel.C.Reference.ref base (array_view_type t n) (array_pcm t n)) (a: array base t) (_: squash (size_v n > 0))
: SteelGhost unit inames
  (varray a)
  (fun _ -> Steel.C.Ref.pts_to_view r (array_view t n))
  (requires fun _ -> g_mk_array r a)
  (ensures (fun h _ h' ->
    g_mk_array r a /\
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
  (ensures (fun r ->
    length r == length r1 + length r2 /\
    fst r == fst r1 // this property justifies array_or_null_from _ t being extracted to t*
  ))

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
  (requires (
    (adjacent r1 r2 /\ (adjacent r2 r3 \/ adjacent (merge r1 r2) r3)) \/
    (adjacent r2 r3 /\ adjacent r1 (merge r2 r3))
  ))
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

val merge_inj_right
  (#base: Type)
  (#t: Type)
  (a b1 b2: array base t)
: Lemma
  (requires (adjacent a b1 /\ adjacent a b2 /\ merge a b1 == merge a b2))
  (ensures (b1 == b2))

val merge_inj_left
  (#base: Type)
  (#t: Type)
  (a1 a2 b: array base t)
: Lemma
  (requires (adjacent a1 b /\ adjacent a2 b /\ merge a1 b == merge a2 b))
  (ensures (a1 == a2))

val no_self_merge_1 (#base #t: Type) (a b: array base t) : Lemma
  (~ (merge_into a b a))

val no_self_merge_2 (#base #t: Type) (a b: array base t) : Lemma
  (~ (merge_into a b b))

[@erasable]
noeq
type gpair (a b: Type) = | GPair: (fst: a) -> (snd: b) -> gpair a b

val gsplit
  (#base: Type)
  (#t: Type)
  (r: array base t)
  (i: size_t)
: Ghost (array base t `gpair` array base t)
  (requires (size_v i <= length r))
  (ensures (fun (GPair rl rr) ->
    merge_into rl rr r /\
    length rl == size_v i
  ))

val split' (#opened: _) (#base: Type) (#t:Type) (a:array base t) (i:size_t)
  : SteelGhost (array base t `gpair` array base t) opened
          (varray a)
          (fun res -> varray (GPair?.fst res) `star` varray (GPair?.snd res))
          (fun _ -> size_v i <= length a)
          (fun h res h' ->
            let s = h (varray a) in
            let sl = h' (varray (GPair?.fst res)) in
            let sr = h' (varray (GPair?.snd res)) in
            size_v i <= length a /\
            res == gsplit a i /\
            sl == Seq.slice s 0 (size_v i) /\
            sr == Seq.slice s (size_v i) (length a) /\
            s == sl `Seq.append` sr
          )

inline_for_extraction
let split_left (#base: _) (#t:Type) (#opened: _) (a:array base t)
  (al ar: Ghost.erased (array base t))
  : SteelAtomicBase (array base t) false opened Unobservable
          (varray al)
          (fun res -> varray res)
          (fun _ ->
            merge_into al ar a
          )
          (fun h res h' ->
            res == Ghost.reveal al /\
            h' (varray res) == h (varray al)
          )
= match a with
  | (a_, _) ->
    let res = (a_, snd al) in
    change_equal_slprop
      (varray al)
      (varray res);
    return res

val split_right_from_prop (#base: _) (#t:Type) (a:array base t) (i:size_t) (from: array_or_null_from base t)
: Tot prop

val split_right_to (#base: _) (#t:Type) (a:array base t) (i:size_t) (sq: squash (size_v i <= length a)) (from: array_or_null_from base t)
: Pure (array_or_null_to base t)
  (requires (split_right_from_prop a i from))
  (ensures (fun y ->
    let res = (from, y) in
    array_or_null_spec res /\
    g_is_null res == false /\
    res == GPair?.snd (gsplit a i)
  ))

val split_right_from (#base: _) (#t:Type) (#opened: _) (a:array base t) (i:size_t)
  : SteelAtomicBase (array_or_null_from base t) false opened Unobservable
          (varray a)
          (fun _ -> varray a)
          (fun _ -> size_v i <= length a)
          (fun h res h' ->
            h' (varray a) == h (varray a) /\
            size_v i <= length a /\
            split_right_from_prop a i res
          )

inline_for_extraction
let split_right (#base: _) (#t:Type) (#opened: _) (a:array base t) (i:size_t)
  : SteelAtomicBase (array base t) false opened Unobservable
          (varray a)
          (fun _ -> varray a)
          (fun _ -> size_v i <= length a)
          (fun h res h' ->
            h' (varray a) == h (varray a) /\
            size_v i <= length a /\
            res == GPair?.snd (gsplit a i)
          )
= let from = split_right_from a i in
  let res = (from, split_right_to a i () from) in
  return res

inline_for_extraction
let split (#opened: _) (#base: Type) (#t:Type) (a:array base t) (i:size_t) (sq: squash (size_v i <= length a))
  : SteelAtomicBase (array base t) false opened Unobservable
          (varray a)
          (fun res -> varray (Ghost.reveal (Ghost.hide (GPair?.fst (gsplit a i))))
          `star` varray res)
          (fun _ -> size_v i <= length a)
          (fun h res h' ->
            let s = h (varray a) in
            let sl = h' (varray (GPair?.fst (gsplit a i))) in
            let sr = h' (varray res) in
            size_v i <= length a /\
            res == GPair?.snd (gsplit a i) /\
            sl == Seq.slice s 0 (size_v i) /\
            sr == Seq.slice s (size_v i) (length a) /\
            s == sl `Seq.append` sr
          )
=
  let sr = split_right a i in
  let g = split' a i in
  change_equal_slprop
    (varray (GPair?.fst g))
    (varray (Ghost.reveal (Ghost.hide (GPair?.fst (gsplit a i)))));
  change_equal_slprop
    (varray (GPair?.snd g))
    (varray sr);
  return sr

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

inline_for_extraction
let joinc (#base: _) (#t:Type) (#opened: _) (al ar:array base t)
  : SteelAtomicBase (array base t) false opened Unobservable
          (varray al `star` varray ar)
          (fun a -> varray al `star` varray ar)
          (fun _ -> adjacent al ar)
          (fun h a h' ->
            h' (varray al) == h (varray al) /\
            h' (varray ar) == h (varray ar) /\
            merge_into al ar a
          )
= match al with
  | (a, _) ->
    let res = (a, snd (merge al ar)) in
    return res

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

val v_ref_of_array
  (#base: Type) (#t:Type0) (r:array base t)
: Ghost vprop
  (requires (length r == 1))
  (ensures (fun _ -> True))

val ref_of_array_ghost (#inames: _) (#base: Type) (#t:Type0) (r:array base t) (sq: squash (length r == 1))
  : SteelGhost unit inames
             (varray r)
             (fun _ -> Steel.C.Ref.pts_to_view (g_ref_of_array r) (Steel.C.Opt.opt_view t) `star` v_ref_of_array r)
             (requires fun _ -> True)
             (ensures fun h0 _ h1 ->
               let r' = g_ref_of_array r in
               let s = h0 (varray r) in
               Seq.length s == 1 /\
               h1 (Steel.C.Ref.pts_to_view r' (Steel.C.Opt.opt_view t)) == Seq.index s 0
             )

val ref_of_array_from (#base: Type) (#t:Type0) (r_from:array_or_null_from base t) (r_to: array_or_null_to base t) (sq: squash (let r = (r_from, r_to) in array_or_null_spec r /\ length r == 1))
  : Steel (Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
             (varray (r_from, r_to))
             (fun r' -> Steel.C.Ref.pts_to_view r' (Steel.C.Opt.opt_view t) `star` v_ref_of_array (r_from, r_to))
             (requires fun _ -> True)
             (ensures fun h0 r' h1 ->
               let r = (r_from, r_to) in
               let s = h0 (varray r) in
               Seq.length s == 1 /\
               g_ref_of_array r == r' /\
               h1 (Steel.C.Ref.pts_to_view r' (Steel.C.Opt.opt_view t)) == Seq.index s 0
             )

inline_for_extraction
let ref_of_array (#base: Type) (#t:Type0) (r:array base t) (sq: squash (length r == 1))
  : Steel (Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
             (varray r)
             (fun r' -> Steel.C.Ref.pts_to_view r' (Steel.C.Opt.opt_view t) `star` v_ref_of_array r)
             (requires fun _ -> True)
             (ensures fun h0 r' h1 ->
               let s = h0 (varray r) in
               Seq.length s == 1 /\
               g_ref_of_array r == r' /\
               h1 (Steel.C.Ref.pts_to_view r' (Steel.C.Opt.opt_view t)) == Seq.index s 0
             )
= match r with
  | (r_from, r_to) ->
    change_equal_slprop
      (varray r)
      (varray (r_from, r_to));
    let res = ref_of_array_from r_from r_to () in
    change_equal_slprop
      (v_ref_of_array (r_from, r_to))
      (v_ref_of_array r);
    return res

val array_of_ref (#inames: _) (#base: Type) (#t:Type0) (r': array base t) (r: Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t)) (sq: squash (length r' == 1))
  : SteelGhost unit inames
             (Steel.C.Ref.pts_to_view r (Steel.C.Opt.opt_view t) `star` v_ref_of_array r')
             (fun _ -> varray r')
             (requires fun _ -> g_ref_of_array r' == r)
             (ensures fun h0 _ h1 ->
               let s = h1 (varray r') in
               Seq.length s == 1 /\
               g_ref_of_array r' == r /\
               h0 (Steel.C.Ref.pts_to_view r (Steel.C.Opt.opt_view t)) == Seq.index s 0
             )

// this function should be used only to pass a pointer as an argument to a function that expects an array

val mk_array_of_ref_from_spec
  (#base: Type) (#t:Type0) (r: Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
  (from: array_or_null_from base t)
: Tot prop

val mk_array_of_ref_to
  (#base: Type) (#t:Type0) (r: Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
  (from: array_or_null_from base t)
: Pure (array_or_null_to base t)
  (requires (mk_array_of_ref_from_spec r from))
  (ensures (fun to ->
    let r' = (from, to) in
    array_or_null_spec r' /\
    g_is_null r' == false
  ))

val mk_array_of_ref_from (#base: Type) (#t:Type0) (r: Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
  : Steel (r0: array_or_null_from base t { mk_array_of_ref_from_spec r r0 })
             (Steel.C.Ref.pts_to_view r (Steel.C.Opt.opt_view t))
             (fun r0 -> varray (r0, mk_array_of_ref_to r r0))
             (requires fun _ -> True)
             (ensures fun h0 r0 h1 ->
               let r' = (r0, mk_array_of_ref_to r r0) in
               let s = h1 (varray r') in
               Seq.length s == 1 /\
               g_ref_of_array r' == r /\
               h0 (Steel.C.Ref.pts_to_view r (Steel.C.Opt.opt_view t)) == Seq.index s 0
             )

inline_for_extraction
let mk_array_of_ref (#base: Type) (#t:Type0) (r: Steel.C.Reference.ref base t (Steel.C.Opt.opt_pcm #t))
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
= let from = mk_array_of_ref_from r in
  let r' = (from, mk_array_of_ref_to r from) in
  change_equal_slprop
    (varray (from, mk_array_of_ref_to r from))
    (varray r');
  return r'

/// Accesses index [i] in array [r], as long as [i] is in bounds and the array
/// is currently valid in memory

val index_from (#base: Type) (#t:Type) (r:array_or_null_from base t) (r' : array_or_null_to base t { array_or_null_spec (r, r') /\ g_is_null (r, r') == false }) (i:size_t)
  : Steel t
             (varray (r, r'))
             (fun _ -> varray (r, r'))
             (requires fun _ -> size_v i < length (r, r'))
             (ensures fun h0 x h1 ->
               let s = h1 (varray (r, r')) in
               size_v i < length (r, r') /\
               h0 (varray (r, r')) == s /\
               x == Seq.index s (size_v i))

inline_for_extraction
let index (#base: Type) (#t:Type) (r:array base t) (i:size_t)
  : Steel t
             (varray r)
             (fun _ -> varray r)
             (requires fun _ -> size_v i < length r)
             (ensures fun h0 x h1 ->
               let s = h1 (varray r) in
               size_v i < length r /\
               h0 (varray r) == s /\
               x == Seq.index s (size_v i))
= match r with
  | (r0, r') ->
    change_equal_slprop
      (varray r)
      (varray (r0, r'));
    let res = index_from r0 r' i in
    change_equal_slprop
      (varray (r0, r'))
      (varray r);
    return res
  

/// Updates index [i] in array [r] with value [x], as long as [i]
/// is in bounds and the array is currently valid in memory


val upd_from (#base: Type) (#t:Type) (r:array_or_null_from base t) (r' : array_or_null_to base t { array_or_null_spec (r, r') /\ g_is_null (r, r') == false }) (i:size_t) (x:t)
  : Steel unit
             (varray (r, r'))
             (fun _ -> varray (r, r'))
             (requires fun h -> size_v i < length (r, r'))
             (ensures fun h0 _ h1 ->
               size_v i < length (r, r') /\
               h1 (varray (r, r')) == Seq.upd (h0 (varray (r, r'))) (size_v i) x)

inline_for_extraction
let upd (#base: Type) (#t:Type) (r:array base t) (i:size_t) (x:t)
  : Steel unit
             (varray r)
             (fun _ -> varray r)
             (requires fun h -> size_v i < length r)
             (ensures fun h0 _ h1 ->
               size_v i < length r /\
               h1 (varray r) == Seq.upd (h0 (varray r)) (size_v i) x)
= match r with
  | (r0, r') ->
    change_equal_slprop
      (varray r)
      (varray (r0, r'));
    upd_from r0 r' i x;
    change_equal_slprop
      (varray (r0, r'))
      (varray r)

let varray_or_null (#base: Type0) (#t: Type0) (x: array_or_null base t) : Tot vprop =
  if g_is_null x then emp else varray x

/// Allocates an array of size [n] where all cells have initial value [x]

val freeable
  (#base: Type0)
  (#t: Type0)
  (a: array base t)
: Tot prop

val malloc_to
  (#t: Type0)
  (x: t)
  (n: size_t)
  (from: array_or_null_from (array_pcm_carrier t n) t)
: Pure (array_or_null_to (array_pcm_carrier t n) t)
    (requires (size_v n > 0))
    (ensures (fun to -> array_or_null_spec (from, to)))

val malloc_from
  (#t: Type0)
  (x: t)
  (n: size_t)
  (sq: squash (size_v n > 0))
: Steel (array_or_null_from (array_pcm_carrier t n) t)
    emp
    (fun r -> varray_or_null (r, malloc_to x n r))
    (requires fun _ -> True)
    (ensures fun _ r0 h' ->
      size_v n > 0 /\
      begin let r : array_or_null (array_pcm_carrier t n) t = (r0, malloc_to x n r0) in
      g_is_null r == false ==> (freeable r /\ h' (varray r) == Seq.create (size_v n) x)
      end
    )

inline_for_extraction
let malloc
  (#t: Type0)
  (x: t)
  (n: size_t)
: Steel (array_or_null (array_pcm_carrier t n) t)
    emp
    (fun r -> varray_or_null r)
    (requires fun _ -> size_v n > 0)
    (ensures fun _ r h' ->
      g_is_null r == false ==> (freeable r /\ h' (varray r) == Seq.create (size_v n) x)
    )
= let r0 = malloc_from x n () in
  let r = (r0, malloc_to x n r0) in
  change_equal_slprop
    (varray_or_null (r0, malloc_to x n r0))
    (varray_or_null r);
  return r

val free_from
  (#base: Type0)
  (#t: Type0)
  (a: array_or_null_from base t)
  (a' : array_or_null_to base t)
  (sq: squash (array_or_null_spec (a, a') /\ g_is_null (a, a') == false))
: Steel unit
    (varray (a, a'))
    (fun _ -> emp)
    (requires (fun _ -> freeable (a,a')))
    (ensures (fun _ _ _ -> True))

inline_for_extraction
let free
  (#base: Type0)
  (#t: Type0)
  (a: array base t)
: Steel unit
    (varray a)
    (fun _ -> emp)
    (requires (fun _ -> freeable a))
    (ensures (fun _ _ _ -> True))
= match a with
  | (af, a') ->
    change_equal_slprop
      (varray a)
      (varray (af, a'));
    free_from af a' ()

val is_null_from
  (#base: Type0)
  (#t: Type0)
  (a: array_or_null_from base t)
  (a' : array_or_null_to base t)
  (sq: squash (array_or_null_spec (a, a')))
: Steel bool
    (varray_or_null (a, a'))
    (fun _ -> varray_or_null (a, a'))
    (requires fun _ -> True)
    (ensures fun h res h' ->
      res == g_is_null (a, a') /\
      h' (varray_or_null (a, a')) == h (varray_or_null (a, a'))
    )

inline_for_extraction
let is_null
  (#base: Type0)
  (#t: Type0)
  (a: array_or_null base t)
: Steel bool
    (varray_or_null a)
    (fun _ -> varray_or_null a)
    (requires fun _ -> True)
    (ensures fun h res h' ->
      res == g_is_null a /\
      h' (varray_or_null a) == h (varray_or_null a)
    )
= match a with
  | (af, a') ->
    change_equal_slprop
      (varray_or_null a)
      (varray_or_null (af, a'));
    let res = is_null_from af a' () in
    change_equal_slprop
      (varray_or_null (af, a'))
      (varray_or_null a);
    return res
