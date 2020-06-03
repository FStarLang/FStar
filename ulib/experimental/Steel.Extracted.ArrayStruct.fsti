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

module Steel.Extracted.ArrayStruct

module AS = Steel.PCM.ArrayStruct
module Mem = Steel.PCM.Memory
module SizeT = Steel.SizeT
module Map = FStar.Map


open FStar.FunctionalExtensionality
open Steel.PCM
module UPCM = Steel.PCM.Unitless
module UPCMBase = Steel.PCM.Unitless.Base
module PCMBase = Steel.PCM.Base

open Steel.PCM.Effect
open Steel.PCM.Memory

/// This module defines a mechanism for extracting arraystructs compatible with separation logic
/// into C arraystructs via Kremlin. This is a rough sketch of Proposal 5 as described here
/// https://github.com/FStarLang/FStar/wiki/Array-Structs-in-Steel

#set-options "--fuel 0 --ifuel 0"


(*** The arraystruct typeclass *)

/// The core of proposal 5 is to define a grammar of attributes for memory actions that Kremlin can
/// recognize and extract as C arraystruct manipulation primitives. As such, these extractable memory
/// actions should operate on types that represent C arraystructs, like Seq.lseq for arrays or F* structs for structs.

/// However, we don't want to restrict the type manipulated by extractable Steel programs to just
/// Seq.lseq or F* structs. To let the user freely work on user-defined, high-level types while
/// maintaining a connection to low-level extractable types, we define a typeclass.

(* Ongoing example: foo_view is the high-level view of what you're storing *)
type foo_view : Type u#1 = {
  view_x: UInt32.t;
  view_y: UInt32.t;
  view_z: UInt64.t
}

(*
  Ongoing example: foo_low is the low-level representation of [foo_view],
  compatible with Kremlin extraction
*)
type foo_low : Type u#1 = {
  low_xy: Seq.lseq UInt32.t 2;
  low_z: UInt64.t
}

open FStar.Tactics

(**
  This tactics checks whether a declared type falls into the subset allowed by Kremlin.
  Can also be done at extraction but less useful error messages
*)
let check_low (src: string) : Tac unit =
  exact (`(()))

(* Ongoing example : this check could be inserted via some metaprogramming or surface language *)
let _ : unit  = _ by (check_low (`%foo_low))

/// Now to finish relating the view and the low-level representation, we need a bijection.

(* Ongoing example: bijection between [foo_low] and [foo_view] *)
let foo_low_to_view (l: foo_low) : foo_view = {
  view_x = Seq.index l.low_xy 0;
  view_y = Seq.index l.low_xy 1;
  view_z = l.low_z;
}
let foo_view_to_low (v: foo_view) : foo_low = {
  low_xy = Seq.init 2 (fun i -> if i = 0 then v.view_x else v.view_y);
  low_z = v.view_z
}


(**
  This typeclass contains all the informations the extraction grammar needs to extract view
  manipulations into low-level C primitives
*)
class low_level (view: Type u#a) = {
  low: Type u#a;
  view_to_low: view -> low;
  low_to_view: low -> view;
  bijection_one: (x: view) -> Lemma (low_to_view (view_to_low x) == x);
  bijection_two: (x: low) -> Lemma (view_to_low (low_to_view x) == x)
}

(* Ongoing example: this is the [foo] instance of the type class *)
instance low_level_foo : low_level foo_view = {
  low = foo_low;
  view_to_low = foo_view_to_low;
  low_to_view = foo_low_to_view;
  bijection_one = (fun _ -> ());
  bijection_two = (fun l ->
    let new_l = foo_view_to_low (foo_low_to_view l) in
    assert(new_l.low_xy `Seq.equal` l.low_xy)
  )
}

/// Please note that if you are working with types that are already extractable by Kremlin, then
/// it is trivial to implement that typeclass by taking everything as identity. The typeclass
/// implementation can then be metaprogrammed.

(*** The attribute grammar in actions *)

/// Let us now illustrate what the attribute language will look like by annotating memory actions,
/// either generic for all low/view pairs or on our ongoing example [foo].

open FStar.Tactics.Typeclasses

(** We are going to use pre/post conditions for specifications in Steel, so we need this helper *)
let slref (#a: Type u#a) (#pcm: pcm a) (r: ref a pcm) : slprop u#a =
  h_exists (pts_to r)

(**
  Also this helper [sel] function will allow use to retrieve the values of references witout
  while we don't have selectors.
*)
val sel (#a: Type) (#pcm: pcm a) (r: ref a pcm) (h: hmem (slref r)) : GTot a

(** We pretend we have a PCM for the view of [foo] *)
val foo_pcm : pcm foo_view

(** We don't bother proving the self-framedness of pre/postconditions in this sketch *)
val admitted_post
  (#a: Type) (#pre:slprop) (#post: a -> slprop)
  (p:(hmem pre -> x:a -> hmem (post x) -> prop))
  : GTot (p:(hmem pre -> x:a -> hmem (post x) -> prop){respects_binary_fp p})

val admitted_pre
  (#pre:slprop)
  (p:(hmem pre -> prop))
  : GTot (p:(hmem pre -> prop){respects_fp p})

/// To ensure that the attribute grammar typechecks, we have to define dummy functions so that
/// the names are recognized.

val extract_update: unit -> Tot unit
val extract_get: unit -> Tot unit
val extract_explode: unit -> Tot unit
val extract_recombine: unit -> Tot unit
val op_String_Access : unit -> Tot unit
val generic_index: unit -> Tot unit

(**** alloc *)

/// The alloc action can be specified generically to all view/low type pairs, no need for an
/// attribute here.

val alloc
  (#a: Type u#1)
  (#[FStar.Tactics.Typeclasses.tcresolve ()] ca: low_level a)
  (pcm: pcm a)
  (v: a)
  (#[FStar.Tactics.exact (quote (ca.view_to_low v))] v_low: ca.low)
    : Steel (ref a pcm) emp (fun r -> slref r) (fun _ -> True) (admitted_post (fun _ r h1 -> sel r h1 == v))

(**** update *)

/// The update operation is more complicated, since the way you can update your view depend on the
/// PCM that is attached to it. This is where the attribute grammar for extraction is going to be
/// useful. Let us say that [foo_pcm] requires us to maintain the following invariant:
/// ```
/// f.view_x + f.view_y <= f.view_z
/// ```
/// Let us also suppose that we want to update the [z] field of the object, then the action should
/// take the whole object in order to ensure the invariant is respected. However, we only want
/// this update to be extracted to an update of the [z] field in C. This is how we would write it:

[@@ extract_update foo_low.low_z]
val update_z (r: ref foo_view foo_pcm) (new_val: UInt64.t)
    : Steel unit (slref r) (fun _ -> slref r)
    (admitted_pre (fun h0 -> (* Question : why do we need the if here? Universes? *)
      if UInt64.v new_val >= UInt32.v (sel r h0).view_x + UInt32.v (sel r h0).view_y then
        True else False
    )) (admitted_post (fun h0 _ h1 ->
     (sel r h1) == { sel r h0 with view_z = new_val }
    ))

/// What should the attribute `[@@extract_update foo_low.low_z]` check for the signature of
/// `update_z` ?
///  - `extract_update` means that `update_z` should have two arguments, the first being the
///     reference and the second being the new value
///  - `low_foo` means that the reference should point to a type for which `low_foo` is an instance
///     of the `low_level` typeclass
///  - `low_z` can actually be a path into the low-level structs, a sequence of field accesses and
///     array indexes. The type of the new value for update should correspond to the low-level type
///     at the end of the path in the low-level structure
///  -  pre and post-ressource should be `slref r`, return type unit
///  -  finally, the postcondition of `update_z` should imply the following semantic definition
///     of a low-level update:
///     ```
///     foo_view_to_low (sel h1 r) == { foo_view_to_low (sel h0 r) with z = new_val }
///     ```
///
/// While the first 4 checks are completely syntactic, the last one can be discharged to SMT. Please
/// note that the bijection is important here because it will allow us to prove this last semantic
/// obligation, by "lifting" the equality in the low-level world to the high-level views where
/// the real postcondition of the function is specified.

(* Ongoing example: sketch on how to use a tactic for checking what is described above *)
let check_extract_update (src: string) : Tac unit =
  exact (`(()))

let _ : unit  = _ by (check_extract_update (`%update_z))

/// Some comments about the meta-arguments that justify the soundness of extraction, given an
/// update with attribute that respect all of the above conditions.
///
/// We now thanks to separation logic that `update_z` can only modify the memory location of
/// reference [r], and nothing else.
/// This meta-argument justifies the fact that it is admissible to compile `update_z` with a mere
/// memory update. `update_z` can do other things such as allocating a new address and then ditching
/// it, but this is not observable by another thread in our semantic. So we eliminate by extracting
/// to Kremlin execution traces that are unobservable and didn't change the computation result.
///
/// What if [update_z] assigns first one value then another? Then we claim that it does not matter since this more complicated execution trace will be extracted by Kremlin to a simpler one. In F*
/// you would still have to prove that the F* body of `update_z` is frame perserving, so if you do
/// that then the frame preservedness still holds for the simpler version extracted by Kremlin.
///
/// The bijection is also key for our meta-argument here. Let's imagine in the low version we have
/// an additional field that is useless, i.e. it is not mapped to a view filed. Because of the
/// bijection between the view and the low-level type, then the value of the useless field has to be
/// constant; otherwise you couldn't prove the bijection.
/// So your update function  could write anything that it wants on that useless field, but it's
/// generally forbidden because the useless field needs to have always the same value. You could write
/// the same value into it but that would fall under redundant write elimination.

(**** get *)

/// Let us now see what how to annotate a function corresponding to a low-level read.

[@@extract_get foo_low.low_xy.[0]]
val get_x (r: ref foo_view foo_pcm)
  : Steel UInt32.t
  (slref r) (fun _ -> slref r)
  (fun _ -> True) (admitted_post (fun h0 v h1 ->
    sel r h0 == sel r h1 /\ v == (sel r h1).view_x
  ))

/// The attribute `[@@extract_get foo_low.low_xy.[0]]` still has to check syntactically that the
/// signature of `get_x` corresponds to a low-level get (one argument which is a ref, returns
/// a value of the right type).
///
/// You can see here that the inner path that we use is more complex (`.low_xy.[0]`). So what is the
/// semantic post-condition implication check here ? Let's call `v` the returned value
///
/// ```
///   foo_view_to_low (sel h0 r) == foo_view_to_low (sel h1 r) /\
///   v == foo_view_to_low (sel h1 r).x.[0]
/// ```
///

(**** low-level array indexing *)

/// The last example updates an array cell with a constant index, but let's see what a get function
/// working on a generic index would look like.

[@@extract_get foo_low.low_xy.[generic_index]]
val get_xy_i (r: ref foo_view foo_pcm) (i: SizeT.t)
  : Steel UInt32.t
  (slref r) (fun _ -> slref r)
  (admitted_pre (fun _ -> if SizeT.v i < 2 then True else False)) (admitted_post (fun h0 ret h1 ->
    sel r h0 == sel r h1 /\ (
      if SizeT.v i = 0 then
        ret == (sel r h1).view_x
      else if SizeT.v i = 1 then
        ret == (sel r h1).view_y
      else False
  )))

/// On top of the syntactic checks, the attribute should check that the precondition implies that the
/// index argument is withing the bounds of the low-level array. The postcondition should imply that,
/// if v is the returned value,
///
/// ```
///  foo_view_to_low (sel r h1) == foo_view_to_low (sel r h1) /\
///  v == Seq.index (foo_view_to_low (sel r h1)).low_xy i
/// ```

(*** Address taking *)

/// Let us now tackle an important feature requested for our extraction and object manipulation
/// language: first-class pointers to parts of a arraystruct.
///
/// For that, we have to define instances of the `low_level` typeclass for all the parts of our
/// arraystructs that we want to have first-class references to.

(* Ongoing example : typeclass instance to the [x] and [y] fields of [foo_view] *)
instance low_level_xy : low_level (Seq.lseq u#1 (Universe.raise_t UInt32.t) 2) = {
  low = (Seq.lseq (Universe.raise_t UInt32.t) 2);
  view_to_low = (fun x -> x);
  low_to_view = (fun x -> x);
  bijection_one = (fun _ -> ());
  bijection_two = (fun _ -> ());
}

(* Ongoing example : typeclass instance to the [z] field of [foo_view] *)
instance low_level_z : low_level (Universe.raise_t u#0 u#1 UInt64.t) = {
  low = (Universe.raise_t u#0 u#1 UInt64.t);
  view_to_low = (fun x -> x);
  low_to_view = (fun x -> x);
  bijection_one = (fun _ -> ());
  bijection_two = (fun _ -> ());
}

val xy_pcm : pcm (Seq.lseq u#1 (Universe.raise_t UInt32.t) 2)
val u64_pcm : pcm (Universe.raise_t u#0 u#1 UInt64.t)

/// Now, we need functions that will be extracted to a low-level address taking of a part of an array
/// struct. These functions should also be compatible with separation logic mechanisms, in the
/// following sense: what happens with the big object once you've taken the address and ownership to
/// a sub-object ? We'll see two patterns, `explode` and `focus`.

(**** explode *)

/// For explode, we want to decompose a arraystruct into multiple parts. This decomposition should
/// be total, meaning that you can recompose the parts to get your arraystruct later. To qualify the
/// totalness of this decomposition, we instantiante the same `low_level` typeclass which qualifies
/// a bijection.

/// Let us see what it gives with our ongoing example. Let's suppose our decomposition is simply

let exploded_foo =
  Seq.lseq u#1 (Universe.raise_t UInt32.t) 2 & (Universe.raise_t u#0 u#1 UInt64.t)

/// Tuples would receive special treatment by Kremlin, as they would be extracted to multiple pointer
/// values.

(* Here is the bijection of the decomposition *)
instance low_level_decomposition_foo : low_level foo_view  =
  let view_to_low : foo_view -> exploded_foo = fun v ->
    (
      Seq.init 2 (fun i ->
        if i = 0 then Universe.raise_val v.view_x else Universe.raise_val v.view_y
      ),
      Universe.raise_val v.view_z
    )
  in
  let low_to_view : exploded_foo -> foo_view = fun (v1, v2) ->
    {
      view_x = Universe.downgrade_val (Seq.index v1 0);
      view_y = Universe.downgrade_val (Seq.index v1 1);
      view_z = Universe.downgrade_val v2;
    }
  in
  {
  low = exploded_foo;
  view_to_low = view_to_low;
  low_to_view = low_to_view;
  bijection_one = (fun _ -> ());
  bijection_two = (fun l ->
    let new_l = view_to_low (low_to_view l) in
    assert((fst new_l) `Seq.equal` (fst l));
    assert((snd new_l) == (snd l));
    assert(new_l == l)
  );
}

/// Now that we have specified how our view should be decomposed, we can write our explode function,
/// with an attribute.

[@@ extract_explode foo_low -> low_level_decomposition_foo -> (low_level_xy, low_level_z)]
val explode_foo (r: ref foo_view foo_pcm)
  : Steel (
    ref (Seq.lseq (Universe.raise_t UInt32.t) 2) xy_pcm &
    ref (Universe.raise_t UInt64.t) u64_pcm
  )
  (slref r) (fun (r1, r2) ->
    slref r1 `star` slref r2
  )
  (fun _ -> True) (admitted_post (fun h0 (r1, r2) h1 ->
    sel r h0 == low_level_decomposition_foo.low_to_view (sel r1 h1, sel r2 h1)
  ))

/// How can this function be implemented? Simply by allocating two new references inside the memory
/// model corresponding to r1 and r2, then copying the contents of r into r1 and r2. But then
/// we still have `slref r` in the post-resource, whereas the function only talks about `r1` and `r2`.
///
/// The solution is that we simply drop `slref r` by affinity of the memory model. There again we
/// need a meta-argument to justify that this can safely be extracted to an address taking
/// instruction, whereas this is implemented in F* by allocating and dropping memory.

[@@ extract_recombine (low_level_xy, low_level_z) -> low_level_decomposition_foo -> foo_low]
val recombine_foo
  (r1: ref (Seq.lseq (Universe.raise_t UInt32.t) 2) xy_pcm)
  (r2: ref (Universe.raise_t UInt64.t) u64_pcm)
  : Steel (ref foo_view foo_pcm)
  (slref r1 `star` slref r2) (fun r -> slref r)
  (fun _ -> True) (admitted_post (fun (h0 : hmem (slref r1 `star` slref r2)) r h1 ->
    sel r h1 == low_level_decomposition_foo.low_to_view (sel r1 h0, sel r2 h0)
  ))
