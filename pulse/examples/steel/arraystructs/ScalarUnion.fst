module ScalarUnion

open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Connection
open Steel.C.StructLiteral
open Steel.C.UnionLiteral
open Steel.C.Typedef
open FStar.FunctionalExtensionality
open Steel.Effect
open Steel.Effect.Atomic
open Steel.C.Fields
open Steel.C.Ref
open Steel.C.Reference
open Steel.C.TypedefNorm

open FStar.FSet
open Steel.C.Typestring
open Steel.C.Typenat

module U32 = FStar.UInt32
module U16 = FStar.UInt16

(** A union is encoded by what amounts to a list of (field name,
    typedef) pairs.  In this example, we define a union named
    u32_or_u16 with one u32 field and one u16 field; to do so we need
    typedefs for u32s and u16s. *)

[@@c_typedef]
noextract inline_for_extraction
let u32: typedef = {
  carrier = option U32.t;
  pcm = opt_pcm #U32.t;
  view_type = U32.t;
  view = opt_view U32.t;
  is_unit = (fun x -> None? x);
}

[@@c_typedef]
noextract inline_for_extraction
let u16: typedef = {
  carrier = option U16.t;
  pcm = opt_pcm #U16.t;
  view_type = U16.t;
  view = opt_view U16.t;
  is_unit = (fun x -> None? x);
}

module T = FStar.Tactics

(** Like structs, unions are labelled by tags to enforce nominality.
    For a more detailed explanation see PointStruct.fst *)

noextract inline_for_extraction
//[@@FStar.Tactics.Effect.postprocess_for_extraction_with(fun () ->
//     T.norm [delta; iota; zeta_full; primops]; T.trefl ())]
let u32_or_u16_tag = normalize (mk_string_t "ScalarUnion.u32_or_u16")

(** The fields of a u32_or_u16. *)
[@@c_struct]
noextract inline_for_extraction
let u32_or_u16_fields: c_fields =
  fields_cons "as_u32" u32 (
  fields_cons "as_u16" u16 (
  fields_nil))

(** The type of (union u32_or_u16) values. *)
noextract inline_for_extraction
let u32_or_u16 = union u32_or_u16_tag u32_or_u16_fields

(** A way to view PCM carrier values as (union u32_or_u16) values. *)
noextract inline_for_extraction
let u32_or_u16_view = union_view u32_or_u16_tag u32_or_u16_fields

(** The PCM that models (union u32_or_u16) values. *)
noextract inline_for_extraction
let u32_or_u16_pcm = union_pcm u32_or_u16_tag u32_or_u16_fields

(** A typedef for u32_or_u16, useful in case it is needed as a field of a struct or union *)
[@@c_typedef]
noextract inline_for_extraction
let c_u32_or_u16: typedef = typedef_union u32_or_u16_tag u32_or_u16_fields

(** Define the union. Like with mk_c_struct, Kremlin detects this
    definition at extraction type and emits the corresponding typedef. *)
let _ = norm norm_c_typedef (mk_c_union u32_or_u16_tag u32_or_u16_fields)

#push-options "--fuel 0"

#push-options "--print_universes --print_implicits"
// --z3rlimit 30"

(** Switch a case of the union to the u16 case, by writing x to it. *)
val switch_to_u16
  (p: ref unit u32_or_u16 u32_or_u16_pcm)
  (x: U16.t)
: Steel unit
    (p `pts_to_view` u32_or_u16_view)
    (fun _ -> p `pts_to_view` u32_or_u16_view)
    (requires fun _ -> True)
    (ensures fun h q h' -> True)

#push-options "--fuel 0"

let switch_to_u16 p x =
  let h = get () in // Needed to prove switch_union_field's precondition
  switch_union_field "as_u16" x p;
  return ()

(** Helper function that zeros the memory location pointed to by p. *)
let zero_u32_ref (p:ref 'a U32.t (opt_pcm #U32.t))
: Steel unit
  (p `pts_to_view` opt_view _)
  (fun _ -> p `pts_to_view` opt_view _)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
= opt_write_sel p 0ul

(** Given a union in the u32 case, set the u32 to zero. *)
val zero_u32_of_union (p: ref unit u32_or_u16 u32_or_u16_pcm)
: Steel unit
    (p `pts_to_view` u32_or_u16_view)
    (fun _ -> p `pts_to_view` u32_or_u16_view)
    (requires fun h -> dfst (dtuple2_of_union (h (p `pts_to_view` u32_or_u16_view))) == "as_u32")
    (ensures fun h q h' -> True)

let zero_u32_of_union p =
  let q: ref _ U32.t _ = addr_of_union_field "as_u32" p in
  zero_u32_ref q;
  unaddr_of_union_field "as_u32" p q;
  return ()
