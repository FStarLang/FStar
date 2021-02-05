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
open FStar.PCM

open Steel.Effect
open Steel.Memory

/// This module defines a mechanism for extracting arraystructs compatible with separation logic
/// into C arraystructs via Kremlin. This is a rough sketch of Proposal 5 as described here
/// https://github.com/FStarLang/FStar/wiki/Array-Structs-in-Steel

#set-options "--fuel 0 --ifuel 1"

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

/// To ensure that the attribute grammar typechecks, we have to define dummy functions so that
/// the names are recognized.

val extract_update: unit -> Tot unit
val extract_get: unit -> Tot unit
val extract_explode: unit -> Tot unit
val extract_recombine: unit -> Tot unit
val op_String_Access : unit -> Tot unit
val generic_index: unit -> Tot unit

(*** Address taking *)

/// Let us now tackle an important feature requested for our extraction and object manipulation
/// language: first-class pointers to parts of a arraystruct.


type u32_pair_stored =
| Full of u32_pair
| XField of UInt32.t
| YField of UInt32.t
| Nothing

/// Now, we have to define a PCM that will render possible the fact to share the ownership on the
/// fields of the struct.
let u32_pair_composable : symrel (u32_pair_stored) = fun a b -> match a, b with
  | XField _, YField _
  | YField _, XField _
  | Nothing, _
  | _, Nothing -> True
  | _ -> False

/// The compose operation "recombines" the values owned in different memories. Even though each memory
/// contain a full pair, only the part of the pair designated by the path matters.

let u32_pair_compose
  (a: u32_pair_stored)
  (b: u32_pair_stored{a `u32_pair_composable` b})
  : u32_pair_stored =
  match a, b with
  | XField x, YField y -> Full ({ x = x; y = y})
  | YField y, XField x -> Full ({ x = x; y = y})
  | Nothing, Nothing -> Nothing
  | Nothing, _ -> b
  | _, Nothing -> a


let u32_pair_stored_pcm : pcm u32_pair_stored = {
  p = {
    composable = u32_pair_composable;
    op = u32_pair_compose;
    one = Nothing;
  };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun  x -> Nothing?x \/ Full? x)
}

let u32_pair_ref = Steel.Memory.ref u32_pair_stored u32_pair_stored_pcm

/// We can now instantiate the pointer typeclass! Let's begin by a pointer to

let slu32_pair (r: u32_pair_ref) (v: u32_pair) : slprop =
  pts_to r (Full v)

(**** update *)

/// Let us also suppose that we want to update the [x] field of the pair, but the action actually
/// takes the whole object. However, we only want
/// this update to be extracted to an update of the [x] field in C. This is how we would write it:

[@@ extract_update u32_pair.x]
val update_x (r: ref u32_pair_stored u32_pair_stored_pcm) (old_pair: Ghost.erased u32_pair) (new_val: UInt32.t)
    : SteelT unit
    (pts_to r (Full (Ghost.reveal old_pair)))
    (fun _ -> pts_to r (Full ({ old_pair with x = new_val})))


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
/// The frame perservation is the reason why we don't have race conditions. Having no race conditions
/// is the correct argument about why the meta-argument of correctness is valid.


(**** get *)

/// Let us now see what how to annotate a function corresponding to a low-level read.

[@@extract_get u32_pair.y]
val get_x (r: ref u32_pair_stored u32_pair_stored_pcm) (pair: Ghost.erased u32_pair)
  : SteelT (x:UInt32.t{pair.x == x})
  (pts_to r (Full (Ghost.reveal pair))) (fun x -> (pts_to r (Full (Ghost.reveal pair))))

/// The attribute `[@@extract_get u32_pair.x]` still has to check syntactically that the
/// signature of `get_x` corresponds to a low-level get (one argument which is a ref, returns
/// a value of the right type).
///
/// So what is the semantic post-condition implication check here ? Let's call `v` the returned value
///
/// ```
/// selref r h0 == selref r h1 /\ v == (Some?.v (selref r h1)).y
/// ```


(**** The pointer typeclass *)

/// This entails a switch from the good old `ref` type, because now the pointers that we manipulate
/// are no longer only addresses inside the memory, we need to add the info of the path inside the
/// reference. Because we want functions not to care whether they receive a pointer that is a full
/// reference or just part of a reference, we create a "pointer" typeclass that will define the
/// interface that our pointers should implement.

let rw_pointer_get_sig
  (a: Type u#a)
  (ref: Type u#0)
  (slref: ref -> a -> slprop)
  =
  r:ref -> x:Ghost.erased a ->
    SteelT (y:a{Ghost.reveal x == y})
      (slref r x)
      (fun _ -> slref r x)

let rw_pointer_upd_sig
  (a: Type u#a)
  (ref: Type u#0)
  (slref: ref -> a -> slprop)
  =
  r: ref ->
  old_val: Ghost.erased a ->
  new_val: a ->
    SteelT unit
      (slref r old_val)
      (fun _ -> slref r new_val)

/// The `a` parameter to the typeclass has to be a Low*-compatible value, something that can be
/// assigned atomically in an update statement.
///
//TODO: enrich the GitHub issue (#1355) about typechecking projectors where the typechecking
//involves calling the subcomp of an effect
#push-options "--__temp_no_proj Steel.ArrayStruct"
class rw_pointer (pointer_ref : Type u#0) (a: Type u#a) = {
  rw_pointer_slref: pointer_ref -> a -> slprop;
  rw_pointer_get: rw_pointer_get_sig a pointer_ref rw_pointer_slref;
  rw_pointer_upd: rw_pointer_upd_sig a pointer_ref rw_pointer_slref;
}
#pop-options

//TODO: typeclass inheritance with https://github.com/project-everest/hacl-star/blob/polubelova_bignum/code/rsapss/Hacl.Bignum.Montgomery.fsti#L130
#push-options "--__temp_no_proj Steel.ArrayStruct"
noeq type r_pointer (pointer_ref : Type u#0) (a: Type u#a) = {
  r_pointer_slref: pointer_ref -> a -> slprop;
  r_pointer_get: rw_pointer_get_sig a pointer_ref r_pointer_slref;
}
#pop-options

/// The goal of this typeclass is to be able to write generic functions like

val increment_generic
  (#pt_t: Type u#0)
  (#cls: rw_pointer pt_t UInt32.t)
  (r: pt_t)
  (v: Ghost.erased UInt32.t{UInt32.v v + 1 <= UInt.max_int 32})
    : SteelT unit
      (cls.rw_pointer_slref r v)
      (fun _ -> cls.rw_pointer_slref r (UInt32.add v 1ul))


/// How will this be reinterpreted for KreMLin extraction? It will extract to uint32_t* because it
/// will see that there is the rw_pointer typeclass whose 2 argument is Uint32.t. If it were
/// r_pointer it would have extracted to const *uint32_t

(**** Instantiating the pointer typeclass *)

/// Lets us now instantiate this typeclass of the fields of of our u32_pair. What will be the ref
/// type ? We have to introduce a new piece of information inside the memory reference, to allow us
/// to distinguish which part of the reference we are owning inside a thread.



/// But we can also instantiate it for the leaves of our structure

(* This should be abstract and decorated with an attribute that says "can be extracted
to a pointer to uint32 *)
let u32_pair_x_field_ref = u32_pair_ref

let slu32_pair_x_field (r: u32_pair_x_field_ref) (v: UInt32.t) : slprop =
   pts_to r (XField v)

val u32_pair_x_field_get
  : rw_pointer_get_sig UInt32.t u32_pair_x_field_ref slu32_pair_x_field

val u32_pair_x_field_upd
  : rw_pointer_upd_sig UInt32.t u32_pair_x_field_ref slu32_pair_x_field

instance u32_pair_x_field_pointer : rw_pointer u32_pair_x_field_ref UInt32.t = {
  pointer_slref = slu32_pair_x_field;
  pointer_get = u32_pair_x_field_get;
  pointer_upd = u32_pair_x_field_upd;
}

let u32_pair_y_field_ref = u32_pair_ref

let slu32_pair_y_field (r: u32_pair_y_field_ref) (v: UInt32.t) =
  pts_to r (YField v)

val u32_pair_y_field_get
  : rw_pointer_get_sig UInt32.t u32_pair_y_field_ref slu32_pair_y_field

val u32_pair_y_field_upd
  : rw_pointer_upd_sig UInt32.t u32_pair_y_field_ref slu32_pair_y_field


instance u32_pair_y_field_pointer : rw_pointer UInt32.t = {
  pointer_ref = u32_pair_y_field_ref;
  pointer_slref = slu32_pair_y_field;
  pointer_get = u32_pair_y_field_get;
  pointer_upd = u32_pair_y_field_upd;
}


(**** explode/recombine *)

val u32_pair_get : rw_pointer_get_sig u32_pair u32_pair_ref slu32_pair

val u32_pair_upd: rw_pointer_upd_sig u32_pair u32_pair_ref slu32_pair

instance u32_pair_pointer : rw_pointer u32_pair = {
  pointer_ref = u32_pair_ref;
  pointer_slref = slu32_pair;
  pointer_get = u32_pair_get;
  pointer_upd = u32_pair_upd;
}


/// The explode/recombine functions are specialized to each struct, and to each pattern of struct
/// explosion that is allowed by the PCM. We'll show here an example for our pair of integers.

val recombinable (r: u32_pair_ref) (r12: u32_pair_x_field_ref & u32_pair_y_field_ref) : prop

[@@ extract_explode recombinable]
val explose_u32_pair_into_x_y (r: u32_pair_ref) (pair: u32_pair)
  : SteelT (r12:(u32_pair_x_field_ref & u32_pair_y_field_ref){recombinable r r12})
  (slu32_pair r pair)
  (fun (r1, r2) ->
    slu32_pair_x_field r1 pair.x `star`
    slu32_pair_y_field r2 pair.y)

/// How to implement this function? We should not have to allocate a new ref, instead we're going
/// to use the same address in memory but in /two different memories/, that we will later join
/// together to produce the `star` in the postressource. Each one of these memory will contain
/// a different value at the same address; memoryX will contain the value of field X along with
/// FieldX path and memory will contain the value of the field Y along with FieldY path.
/// These two memory are composable thanks to the PCM that we've defined for `u32_pair_stored`.

[@@ extract_recombine ]
val recombine_u32_pair_from_x_y
  (r: u32_pair_ref)
  (r1: u32_pair_x_field_ref)
  (v1: UInt32.t)
  (r2: u32_pair_y_field_ref{recombinable r (r1, r2)})
  (v2: UInt32.t)
  : SteelT unit
    (slu32_pair_x_field r1 v1 `star` slu32_pair_y_field r2 v2)
    (fun _ -> slu32_pair r ({ x = v1; y = v2}))

// TODO example: write a program that allocates a pair, explodes it, increment both fields,
// recombine it. From this program, imagine how it will be extracted to KreMLin and if
// it has sufficient information to do so
