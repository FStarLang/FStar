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

module Steel.ArrayStruct

module SizeT = Steel.SizeT
module Map = FStar.Map


open FStar.FunctionalExtensionality
open Steel.PCM
module PCMBase = Steel.PCM.Base

open Steel.Effect.Fake
open Steel.Memory

/// This module defines a mechanism for extracting arraystructs compatible with separation logic
/// into C arraystructs via Kremlin. This is a rough sketch of Proposal 5 as described here
/// https://github.com/FStarLang/FStar/wiki/Array-Structs-in-Steel

#set-options "--fuel 0 --ifuel 0"


(*** arraystruct types *)

/// The core of proposal 5 is to define a grammar of attributes for memory actions that Kremlin can
/// recognize and extract as C arraystruct manipulation primitives. As such, these extractable memory
/// actions should operate on types that represent C arraystructs, like Seq.lseq for arrays or F* structs for structs.

/// The types manipulated by extractable Steel programs have to be restrained to F* structs and Seq.lseq, because
/// these translate to C structs and arrays. To let the user freely work on user-defined, high-level types while
/// maintaining a connection to low-level extractable types, one can use the projection system that comes with Steel.

(*
  Ongoing example: foo_low is the low-level representation of [foo_view],
  compatible with Kremlin extraction
*)
type u32_pair : Type u#1 = {
  x: UInt32.t;
  y: UInt32.t;
}

open FStar.Tactics

(**
  This tactics checks whether a declared type falls into the subset allowed by Kremlin.
  Can also be done at extraction but less useful error messages
*)
let check_low (src: string) : Tac unit =
  exact (`(()))

(* Ongoing example : this check could be inserted via some metaprogramming or surface language *)
let _ : unit  = _ by (check_low (`%u32_pair))

(*** The attribute grammar in actions *)

/// Let us now illustrate what the attribute language will look like by annotating memory actions,
/// either generic for all low/view pairs or on our ongoing example [foo].

open FStar.Tactics.Typeclasses

(** We are going to use pre/post conditions for specifications in Steel, so we need this helper *)
let href (#a: Type u#a) (#pcm: pcm a) (r: ref a pcm) : slprop u#a =
  h_exists (pts_to r)

(** Let us give a simple PCM for the pair *)
let u32_pair_pcm : pcm (option u32_pair) = PCMBase.exclusive_pcm

/// To ensure that the attribute grammar typechecks, we have to define dummy functions so that
/// the names are recognized.

val extract_update: unit -> Tot unit
val extract_get: unit -> Tot unit
val extract_explode: unit -> Tot unit
val extract_recombine: unit -> Tot unit
val op_String_Access : unit -> Tot unit
val generic_index: unit -> Tot unit

(**** update *)

/// Let us also suppose that we want to update the [x] field of the pair, but the action actually
/// takes the whole object. However, we only want
/// this update to be extracted to an update of the [x] field in C. This is how we would write it:

[@@ extract_update u32_pair.x]
val update_x (r: ref (option u32_pair) u32_pair_pcm) (new_val: UInt32.t)
    : Steel unit (href r) (fun _ -> href r)
    (fun h0 -> if Some? (sel r h0) then True else False) (fun h0 _ h1 ->
     Some? (sel r h1) /\ Some? (sel r h0) /\
     Some?.v (sel r h1) == { Some?.v (sel r h0) with x = new_val }
    )

/// What should the attribute `[@@extract_update u32_pair]` checks for the signature of
/// `update_z` ?
///  - `extract_update` means that `update_x` should have two arguments, the first being the
///     reference and the second being the new value
///  - `u32_pair` means that the reference should point to a option u32_pair
///  - `x` can actually be a path into the low-level structs, a sequence of field accesses and
///     array indexes. The type of the new value for update should correspond to the low-level type
///     at the end of the path in the low-level structure
///  -  pre and post-ressource should be `uref r`, return type unit
///  -  finally, the postcondition of `update_x` should imply the following semantic definition
///     of a low-level update:
///     ```
///     Some?.v (selref r h1) == { Some?.v (selref r h0) with x = new_val }
///     ```
///
/// While the first 4 checks are completely syntactic, the last one can be discharged to SMT. Please
/// note that the bijection is important here because it will allow us to prove this last semantic
/// obligation, by "lifting" the equality in the low-level world to the high-level views where
/// the real postcondition of the function is specified.

(* Ongoing example: sketch on how to use a tactic for checking what is described above *)
let check_extract_update (src: string) : Tac unit =
  exact (`(()))

let _ : unit  = _ by (check_extract_update (`%update_x))

/// Some comments about the meta-arguments that justify the soundness of extraction, given an
/// update with attribute that respect all of the above conditions.
///
/// We now thanks to separation logic that `update_x` can only modify the memory location of
/// reference [r], and nothing else.
/// This meta-argument justifies the fact that it is admissible to compile `update_z` with a mere
/// memory update. `update_z` can do other things such as allocating a new address and then ditching
/// it, but this is not observable by another thread in our semantic. So we eliminate by extracting
/// to Kremlin execution traces that are unobservable and didn't change the computation result.
///
/// What if [update_z] assigns first one value then another? Then we claim that it does not matter since this more complicated execution trace will be extracted by Kremlin to a simpler one. In F*
/// you would still have to prove that the F* body of `update_x` is frame perserving, so if you do
/// that then the frame preservedness still holds for the simpler version extracted by Kremlin.


(**** get *)

/// Let us now see what how to annotate a function corresponding to a low-level read.

[@@extract_get u32_pair.y]
val get_x (r: ref (option u32_pair) u32_pair_pcm)
  : Steel UInt32.t
  (href r) (fun _ -> href r)
  (fun h0 -> if Some? (sel r h0) then True else False) (fun h0 v h1 ->
    Some? (sel r h0) /\ Some? (sel r h1) /\
    sel r h0 == sel r h1 /\ v == (Some?.v (sel r h1)).y
  )

/// The attribute `[@@extract_get u32_pair.x]` still has to check syntactically that the
/// signature of `get_x` corresponds to a low-level get (one argument which is a ref, returns
/// a value of the right type).
///
/// So what is the semantic post-condition implication check here ? Let's call `v` the returned value
///
/// ```
/// selref r h0 == selref r h1 /\ v == (Some?.v (selref r h1)).y
/// ```
///

(*** Address taking *)

/// Let us now tackle an important feature requested for our extraction and object manipulation
/// language: first-class pointers to parts of a arraystruct.

(**** The pointer typeclass *)

/// This entails a switch from the good old `ref` type, because now the pointers that we manipulate
/// are no longer only addresses inside the memory, we need to add the info of the path inside the
/// reference. Because we want functions not to care whether they receive a pointer that is a full
/// reference or just part of a reference, we create a "pointer" typeclass that will define the
/// interface that our pointers should implement.

let rw_pointer_get_sig
  (a: Type u#a)
  (ref: Type u#0)
  (slref: ref -> slprop)
  (sel: (r:ref) -> hmem (slref r) -> GTot a)
  =
  r:ref ->
    Steel a
      (slref r)
      (fun _ -> slref r)
      (fun h0 -> True)
      (fun h0 x h1 -> sel r h0 == sel r h1 /\ x == sel r h0)

let rw_pointer_upd_sig
  (a: Type u#a)
  (ref: Type u#0)
  (slref: ref -> slprop)
  (sel: (r:ref) -> hmem (slref r) -> GTot a)
  =
  r: ref ->
  new_val: a ->
    Steel unit
      (slref r)
      (fun _ -> slref r)
      (fun h0 -> True)
      (fun h0 _ h1 -> sel r h1 == new_val)

/// The `a` parameter to the typeclass has to be a Low*-compatible value, something that can be
/// assigned atomically in an update statement.
#push-options "--admit_smt_queries true" (* fails, points to subcomp_pre in Steel.Effect.fsti? *)
class rw_pointer (a: Type u#a) = {
  pointer_ref:  Type u#0;
  pointer_slref: pointer_ref -> slprop;
  pointer_sel: (r:pointer_ref) -> hmem (pointer_slref r) -> GTot a;
  pointer_get: rw_pointer_get_sig a pointer_ref pointer_slref pointer_sel;
  pointer_upd: rw_pointer_upd_sig a pointer_ref pointer_slref pointer_sel;
}
#pop-options

/// The goal of this typeclass is to be able to write generic functions like

val increment_generic (#cls: rw_pointer UInt32.t) (r: cls.pointer_ref) : Steel unit
  (cls.pointer_slref r) (fun _ -> cls.pointer_slref r)
  (fun _ -> True)
  (fun h0 _ h1 ->
    UInt32.v (cls.pointer_sel r h1) == UInt32.v (cls.pointer_sel r h0) + 1
  )

(**** Instantiating the pointer typeclass *)

/// Lets us now instantiate this typeclass of the fields of of our u32_pair. What will be the ref
/// type ? We have to introduce a new piece of information inside the memory reference, to allow us
/// to distinguish which part of the reference we are owning inside a thread.


type u32_pair_path =
| Full
| XField
| YField

let u32_pair_stored = option (u32_pair & u32_pair_path)

/// Now, we have to define a PCM that will render possible the fact to share the ownership on the
/// fields of the struct.

#push-options "--ifuel 1"
let u32_pair_composable : symrel (u32_pair_stored) = fun a b -> match a, b with
  | Some (a, a_path), Some (b, b_path) -> begin
    match a_path, b_path with
    | XField, YField
    | YField, XField -> True
    | _ -> False
  end
  | _ -> True
#pop-options

/// The compose operation "recombines" the values owned in different memories. Even though each memory
/// contain a full pair, only the part of the pair designated by the path matters.

let u32_pair_compose
  (a: u32_pair_stored)
  (b: u32_pair_stored{a `u32_pair_composable` b})
  : u32_pair_stored =
  match a, b with
  | Some (a, a_path), Some (b, b_path) -> begin
    match a_path, b_path with
    | XField, YField -> Some (({ x = a.x; y = b.y}), Full)
    | YField, XField -> Some (({ x = b.x; y = a.y}), Full)
  end
  | None, Some _ -> b
  | Some _, None -> a
  | None, None -> None

#push-options "--z3rlimit 15 --ifuel 1"
let u32_pair_stored_pcm : pcm u32_pair_stored = {
  p = {
    composable = u32_pair_composable;
    op = u32_pair_compose;
    one = None;
  };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
}
#pop-options

let u32_pair_ref = Steel.Memory.ref u32_pair_stored u32_pair_stored_pcm

/// We can now instantiate the pointer typeclass! Let's begin by a pointer to

let slu32_pair (r: u32_pair_ref) : slprop =
  h_exists (fun (v: u32_pair_stored) -> pts_to r v `star` pure (Some? v /\ snd (Some?.v v) == Full))

val slu32_pair_elim (r: u32_pair_ref) (h: hmem (slu32_pair r)) :
  Lemma (interp (ptr r) h /\ begin let v = sel r h in
    Some? v /\ snd (Some?.v v) == Full
  end)

let u32_pair_sel (r: u32_pair_ref) (h: hmem (slu32_pair r)) : GTot u32_pair =
    slu32_pair_elim r h;
    fst (Some?.v (sel r h))

val u32_pair_get : rw_pointer_get_sig u32_pair u32_pair_ref slu32_pair u32_pair_sel

val u32_pair_post: rw_pointer_upd_sig u32_pair u32_pair_ref slu32_pair u32_pair_sel

instance u32_pair_pointer : rw_pointer u32_pair = {
  pointer_ref = u32_pair_ref;
  pointer_slref = slu32_pair;
  pointer_sel = u32_pair_sel;
  pointer_get = u32_pair_get;
  pointer_upd = u32_pair_post;
}

/// But we can also instantiate it for the leaves of our structure

let u32_pair_x_field_ref = u32_pair_ref

let slu32_pair_x_field (r: u32_pair_x_field_ref) : slprop =
  h_exists (fun (v: u32_pair_stored) -> pts_to r v `star` pure (Some? v /\ snd (Some?.v v) == XField))

val slu32_pair_x_field_elim (r: u32_pair_x_field_ref) (h: hmem (slu32_pair_x_field r)) :
  Lemma (interp (ptr r) h /\ begin let v = sel r h in
    Some? v /\ snd (Some?.v v) == XField
  end)

let u32_pair_x_field_sel
  (r: u32_pair_x_field_ref)
  (h: hmem (slu32_pair_x_field r))
    : GTot UInt32.t
  =
  slu32_pair_x_field_elim r h;
  (fst (Some?.v (sel r h))).x

val u32_pair_x_field_get
  : rw_pointer_get_sig UInt32.t u32_pair_x_field_ref slu32_pair_x_field u32_pair_x_field_sel

val u32_pair_x_field_upd
  : rw_pointer_upd_sig UInt32.t u32_pair_x_field_ref slu32_pair_x_field u32_pair_x_field_sel

instance u32_pair_x_field_pointer : rw_pointer UInt32.t = {
  pointer_ref = u32_pair_x_field_ref;
  pointer_slref = slu32_pair_x_field;
  pointer_sel = u32_pair_x_field_sel;
  pointer_get = u32_pair_x_field_get;
  pointer_upd = u32_pair_x_field_upd;
}

let u32_pair_y_field_ref = u32_pair_ref

let slu32_pair_y_field (r: u32_pair_y_field_ref) =
  h_exists (fun (v: u32_pair_stored) -> pts_to r v `star` pure (Some? v /\ snd (Some?.v v) == YField))

val slu32_pair_y_field_elim (r: u32_pair_y_field_ref) (h: hmem (slu32_pair_y_field r)) :
  Lemma (interp (ptr r) h /\ begin let v = sel r h in
    Some? v /\ snd (Some?.v v) == YField
  end)

let u32_pair_y_field_sel
  (r: u32_pair_y_field_ref)
  (h: hmem (slu32_pair_y_field r))
    : GTot UInt32.t
  =
  slu32_pair_y_field_elim r h;
  (fst (Some?.v (sel r h))).y

val u32_pair_y_field_get
  : rw_pointer_get_sig UInt32.t u32_pair_y_field_ref slu32_pair_y_field u32_pair_y_field_sel

val u32_pair_y_field_upd
  : rw_pointer_upd_sig UInt32.t u32_pair_y_field_ref slu32_pair_y_field u32_pair_y_field_sel


instance u32_pair_y_field_pointer : rw_pointer UInt32.t = {
  pointer_ref = u32_pair_y_field_ref;
  pointer_slref = slu32_pair_y_field;
  pointer_sel = u32_pair_y_field_sel;
  pointer_get = u32_pair_y_field_get;
  pointer_upd = u32_pair_y_field_upd;
}

(**** explode/recombine *)

/// The explode/recombine functions are specialized to each struct, and to each pattern of struct
/// explosion that is allowed by the PCM. We'll show here an example for our pair of integers.

val recombinable (r: u32_pair_ref) (r12: u32_pair_x_field_ref & u32_pair_y_field_ref) : prop
[@@ extract_explode u32_pair_pointer ->
  (u32_pair_x_field_pointer, u32_pair_y_field_pointer) ->
  recombinable
]
val explose_u32_pair_into_x_y (r: u32_pair_ref)
  : Steel (u32_pair_x_field_ref & u32_pair_y_field_ref)
  (slu32_pair r)
  (fun (r1, r2) ->
    slu32_pair_x_field r1 `star`
    slu32_pair_y_field r2)
  (fun _ -> True)
  (fun h0 (r1, r2) h1 ->
    (u32_pair_sel r h0 == {
      x = u32_pair_x_field_sel r1 h1;
      y = u32_pair_y_field_sel r2 h1;
    } /\ recombinable r (r1,r2))
  )

/// How to implement this function? We should not have to allocate a new ref, instead we're going
/// to use the same address in memory but in /two different memories/, that we will later join
/// together to produce the `star` in the postressource. Each one of these memory will contain
/// a different value at the same address; memoryX will contain the value of field X along with
/// FieldX path and memoryY will contain the value of the field Y along with FieldY path.
/// These two memory are composable thanks to the PCM that we've defined for `u32_pair_stored`.

[@@ extract_recombine u32_pair_pointer -> u32_pair_x_field_pointer -> u32_pair_y_field_pointer ]
val recombine_u32_pair_from_x_y
  (r: u32_pair_ref)
  (r1: u32_pair_x_field_ref)
  (r2: u32_pair_y_field_ref)
  : Steel unit
  (slu32_pair_x_field r1 `star` slu32_pair_y_field r2)
  (fun _ -> slu32_pair r)
  (fun _ -> recombinable r (r1, r2))
  (fun (h0: hmem (slu32_pair_x_field r1 `star` slu32_pair_y_field r2)) _ h1 ->
    u32_pair_sel r h1 == {
    x = u32_pair_x_field_sel r1 h0;
    y = u32_pair_y_field_sel r2 h0;
  })

(**** focus *)

/// We can also derive a `focus` operation that "forgets" the rest of
/// the fields for a given time.

val focus_u32_pair_x_field
  (r: u32_pair_ref)
  : Steel (u32_pair_x_field_ref)
  (slu32_pair r)
  (fun r1 -> slu32_pair_x_field r1 `star` (slu32_pair_x_field r1 `wand` slu32_pair r))
  (fun _ -> True)
  (fun h0 r1 h1 ->
   wand_elim (slu32_pair_x_field r1) (slu32_pair r) h1;
   u32_pair_sel r h0 == { u32_pair_sel r h1 with x = u32_pair_x_field_sel r1 h1 }
  )

/// Things to talk with Nik :
///  - (if Some? (selref r h0) then True else False) weird universe bug
///  - we want custom paths for our structs because with a generic thing it'll have to be recursive
///    and that will not play out well with the SMT
///  - whole arrays cannot be updated at once in C, the checking tactic can make sure it is not
///    the case
