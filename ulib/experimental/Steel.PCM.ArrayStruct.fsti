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

module Steel.PCM.ArrayStruct

module SizeT = Steel.SizeT
module DepMap = FStar.DependentMap

open FStar.FunctionalExtensionality
open Steel.PCM
open Steel.PCM.Unitless

/// The C language allows the definition of flat data structure composed of nested struts and arrays.
/// These flat data structures are used everywhere in systems programming, as their size can be
/// computed at compile time and they can be statically or stack-allocated. In the following, we will
/// refer to these data structures as arraystructs.
///
/// This module defines the memory-model-compatible representation of arraystructs:
/// - the `arraystruct` type that will be stored inside memory references
/// - helper functions to build partial commutative monoids for arraystructs
/// - examples of use

(*** The [arraystruct] type *)

(**** Descriptors *)

/// Since an arraystruct can contain multiple levels of nested arrays and struct, we need to be able
/// to describe precisely the nesting structure. That is what a descriptor achieves.

(** The field of structs are designated by a string (the name of the field) *)
type field_id = string

(**
  The descriptor contains all the information necessary to derive the type of the values
  corresponding to an arraystruct.
*)
noeq
type array_struct_descriptor : Type u#(a + 1) =
  | DBase : a: Type u#a -> array_struct_descriptor
  | DArray : cell_descriptor: array_struct_descriptor u#a -> len: SizeT.t -> array_struct_descriptor
  | DStruct : field_descriptors: (field_id ^-> array_struct_descriptor u#a)
    -> array_struct_descriptor

(**** [arraystruct] values type *)

(** The type of an array value is an [lseq] *)
let array_type (cell_type: Type u#a) (len: SizeT.t) : Type u#a = Seq.lseq cell_type (SizeT.v len)

(** The type of a struct type is a dependent map *)
let struct_type (field_typs: (field_id -> Type u#a)) : Type u#a = DepMap.t field_id field_typs

(** Helper function to prove that the recursive call of the next function is decreasing *)
unfold
let struct_field_type'
      (field_descriptors: (field_id ^-> array_struct_descriptor u#a))
      (array_struct_type:
          (descriptor: array_struct_descriptor u#a {descriptor << field_descriptors}
              -> Tot (Type u#a)))
      (field: field_id)
    : Tot (Type u#a) =
  let descr = field_descriptors field in
  FStar.WellFounded.axiom1 field_descriptors field;
  array_struct_type descr

(** This functions achives the [descriptor -> Type] correspondence *)
let rec array_struct_type (descriptor: array_struct_descriptor u#a)
    : Tot (Type u#a) (decreases descriptor) =
  match descriptor with
  | DBase a -> a
  | DArray descriptor' len ->
    let typ' = array_struct_type descriptor' in
    array_type typ' len
  | DStruct field_descriptors ->
    let typs' = struct_field_type' field_descriptors array_struct_type in
    struct_type typs'

(** Gets the type of values of the field of a struct *)
unfold
let struct_field_type
      (field_descriptors: (field_id ^-> (array_struct_descriptor u#a)))
      (field: field_id)
    : Tot (Type u#a) = struct_field_type' field_descriptors array_struct_type field

(** The type of a struct value is a dependent map *)
val struct_field_type_unroll_lemma (field_descriptors: (field_id ^-> array_struct_descriptor u#a))
    : Lemma
      (DependentMap.t u#a field_id (struct_field_type u#a field_descriptors) ==
        array_struct_type u#a (DStruct u#a field_descriptors))
      [SMTPat (array_struct_type u#a (DStruct u#a field_descriptors))]

(**** The main [array_struct] type *)

(**
  [arraystruct] encapsulates the descriptor, a value corresponding to the descriptor as well as
  a sub-PCM to govern the values corresponding to the descriptor. Note that the sub-PCM is unitless,
  meaning that we don't require a unit value with its corresponding lemma. Indeed, the unit value
  always comes from the [None] case of a base [option] type. We need a full-fledged PCM with a unit
  value to store in the memory model, which is going to govern values of type [option array_struct].
  But for the sub-PCM inside the [array_struct], we don't need a unit value.
*)
noeq
type array_struct : Type u#(a + 1) =
  | ArrayStruct : 
      descriptor: array_struct_descriptor u#a ->
      pcm: unitless_pcm (array_struct_type descriptor) ->
      value: array_struct_type descriptor
    -> array_struct

/// Now, let's proceed to build the PCM that govern all arraystruct values stored inside the memory.

(**
  Composability is then based on the composability of the sub-PCM. Only arraystruct that have
  the same descriptor and sub-PCM can be composed.
*)
let composable_array_struct:symrel u#(a + 1) (array_struct u#a) =
  fun (s0: array_struct u#a) (s1: array_struct u#a) ->
    s0.descriptor == s1.descriptor /\ s0.pcm == s1.pcm /\
    s0.pcm.unitless_p.unitless_composable s0.value s1.value

(** The composition also uses the sub-PCM's composition *)
let compose_array_struct
      (s0: array_struct u#a)
      (s1: array_struct u#a {s0 `composable_array_struct` s1})
    : array_struct u#a =
  let new_val = s0.pcm.unitless_p.unitless_op s0.value s1.value in
  ArrayStruct s0.descriptor s0.pcm new_val

(** We can now define the unitless PCM for all [arraystruct] *)
let array_struct_unitless_pcm:unitless_pcm u#(a + 1) (array_struct u#a) =
  {
    unitless_p
    =
    { unitless_composable = composable_array_struct u#a; unitless_op = compose_array_struct u#a };
    unitless_comm = (fun s0 s1 -> s0.pcm.unitless_comm s0.value s1.value);
    unitless_assoc = (fun s0 s1 s2 -> s0.pcm.unitless_assoc s0.value s1.value s2.value);
    unitless_assoc_r = (fun s0 s1 s2 -> s0.pcm.unitless_assoc_r s0.value s1.value s2.value)
  }

(** To get a full-fledged PCM, we just add the [None] case *)
let array_struct_pcm:pcm u#(a + 1) (option u#(a + 1) (array_struct u#a)) =
  to_full_pcm_with_unit array_struct_unitless_pcm

(*** Building a sub-PCM *)

(**** For an array *)

(**
  This retrieves the composability for an array cell, given a base PCM governing the cells of
  the array.
*)
let composable_array_cell
      (#cell_type: Type u#a)
      (#len: SizeT.t)
      (base_pcm: unitless_pcm cell_type)
      (x y: array_type cell_type len)
      (i: nat{i < SizeT.v len})
    : prop =
  let xi = Seq.index x i in
  let yi = Seq.index y i in
  base_pcm.unitless_p.unitless_composable xi yi

(** Composability for an array is pointwise composability of its cells *)
let composable_array (#cell_type: Type u#a) (#len: SizeT.t) (base_pcm: unitless_pcm cell_type)
    : symrel (array_type cell_type len) =
  fun x y -> forall (i: nat{i < SizeT.v len}). composable_array_cell base_pcm x y i

(** Composition for an array is pointwise composition of its cells*)
let compose_array
      (#cell_type: Type u#a)
      (#len: SizeT.t)
      (base_pcm: unitless_pcm cell_type)
      (x: array_type cell_type len)
      (y: array_type cell_type len {composable_array base_pcm x y})
    : array_type cell_type len =
  Seq.init (SizeT.v len)
    (fun i ->
        let xi = Seq.index x i in
        let yi = Seq.index y i in
        base_pcm.unitless_p.unitless_op xi yi)

(**
  From those composability and compose predicates we can build a sub-PCM for an array given the
  sub-PCM governing its cells.
*)
val pointwise_array_pcm (cell_type: Type u#a) (len: SizeT.t) (base_pcm: unitless_pcm cell_type)
    : unitless_pcm (array_type cell_type len)

val reveal_pointwise_array_pcm
      (cell_type: Type u#a)
      (len: SizeT.t)
      (base_pcm: unitless_pcm cell_type)
    : Lemma
      (let pcm = pointwise_array_pcm cell_type len base_pcm in
        pcm.unitless_p.unitless_composable == composable_array base_pcm /\
        pcm.unitless_p.unitless_op == compose_array base_pcm)
      [SMTPat (pointwise_array_pcm cell_type len base_pcm)]

(**** For a struct *)

(**
  This retrieves the composability for a struct field, given a base PCM governing the fields of
  the struct.
*)
let composable_struct_field
      (#field_types: (field_id -> Type u#a))
      (base_pcms: (field: field_id -> unitless_pcm (field_types field)))
      (field: field_id)
      (x y: struct_type field_types)
    : prop =
  let xf = DepMap.sel x field in
  let yf = DepMap.sel y field in
  (base_pcms field).unitless_p.unitless_composable xf yf

(** Composability for a struct is pointwise composability of its fields *)
let composable_struct
      (#field_types: (field_id -> Type u#a))
      (base_pcms: (field: field_id -> unitless_pcm (field_types field)))
    : symrel (struct_type field_types) =
  fun x y -> forall (field: field_id). composable_struct_field base_pcms field x y

(** Composition for a struct is pointwise composition of its fields *)
let compose_struct
      (#field_types: (field_id -> Type u#a))
      (base_pcms: (field: field_id -> unitless_pcm (field_types field)))
      (x: struct_type field_types)
      (y: struct_type field_types {composable_struct base_pcms x y})
    : struct_type field_types =
  DepMap.create (fun field ->
        let xf = DepMap.sel x field in
        let yf = DepMap.sel y field in
        (base_pcms field).unitless_p.unitless_op xf yf)

(**
  From those composability and compose predicates we can build a sub-PCM for a struct given the
  sub-PCMs governing its fields.
*)
val pointwise_struct_pcm
      (field_types: (field_id -> Type u#a))
      (base_pcms: (field: field_id -> unitless_pcm (field_types field)))
    : unitless_pcm (struct_type field_types)

val reveal_pointwise_struct_pcm
      (field_types: (field_id -> Type u#a))
      (base_pcms: (field: field_id -> unitless_pcm (field_types field)))
    : Lemma
      (let pcm = pointwise_struct_pcm field_types base_pcms in
        pcm.unitless_p.unitless_composable == composable_struct base_pcms /\
        pcm.unitless_p.unitless_op == compose_struct base_pcms)
      [SMTPat (pointwise_struct_pcm field_types base_pcms)]

(*** Examples *)

open Steel.PCM.FractionalPermission
open Steel.PCM.Unitless.Base

let array_with_frac_perm_on_all_indexes (t: Type u#a) (len: SizeT.t) (v: t) : array_struct u#a =
  ArrayStruct (DArray (DBase (with_perm u#a t)) len)
    (pointwise_array_pcm (with_perm t) len frac_perm_pcm)
    (Seq.init u#a (SizeT.v len) (fun _ -> { value = v; perm = perm_one }))

let immutable_splittable_array (t: Type u#a) (len: SizeT.t) (v: t) : array_struct u#a =
  ArrayStruct (DArray (DBase t) len)
    (pointwise_array_pcm t len immutable_unitless_pcm)
    (Seq.init u#a (SizeT.v len) (fun _ -> v))

let two_fields_restricted_func
      (#a: Type u#a)
      (field1: string)
      (field2: string{field2 <> field1})
      (value1 value2 by_default: a)
    : (field_id ^-> a) =
  on _
    (fun field -> if field = field1 then value1 else if field = field2 then value2 else by_default)

#push-options "--fuel 2 --ifuel 2"
let two_fields_dep_map
      (a: (field_id -> Type u#a))
      (field1: string)
      (field2: string{field2 <> field1})
      (value1: a field1)
      (value2: a field2)
      (by_default: (field: field_id{field <> field1 /\ field <> field2} -> a field))
    : (DepMap.t field_id a) =
  DepMap.create #field_id
    #a
    (fun field ->
        if field = field1 then value1 else if field = field2 then value2 else by_default field)

let point_2d:array_struct =
  let field_descriptors = two_fields_restricted_func "x" "y" (DBase int) (DBase int) (DBase unit) in
  let field_types:(field_id -> Type0) = struct_field_type field_descriptors in
  let field_pcms:(field: field_id -> unitless_pcm (field_types field)) =
    fun field ->
      if field = "x"
      then exclusive_unitless_pcm
      else if field = "y" then immutable_unitless_pcm else exclusive_unitless_pcm
  in
  struct_field_type_unroll_lemma field_descriptors;
  ArrayStruct (DStruct field_descriptors)
    (pointwise_struct_pcm field_types field_pcms)
    (two_fields_dep_map field_types "x" "y" 0 1 (fun _ -> ()))

