module HaclExample

open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Connection
open Steel.C.StructLiteral
open Steel.C.Typedef
open FStar.FunctionalExtensionality
open Steel.Effect
open Steel.Effect.Atomic
open Steel.C.Fields
open Steel.C.Opt
open Steel.C.Ref
open Steel.C.Reference
open Steel.C.TypedefNorm
open Steel.C.Array

open FStar.FSet
open Steel.C.Typenat
open Steel.C.Typestring

module U64 = FStar.UInt64
module I = Steel.C.StdInt

(** In this file we demonstrate how Steel could be used to manipulate the following data type used in Hacl*:
      https://github.com/project-everest/hacl-star/blob/master/code/poly1305/Hacl.Impl.Poly1305.fsti#L18
    This Low* definition amounts to the struct definition
      struct poly1305_ctx { uint64_t limbs[5]; uint64_t precomp[20]; };
    and, with our new model of structs and arrays and pointer-to-field, can be expresesd directly in Steel.

    See PointStruct.fst for more detailed explanations of the various definitions needed below.
*)

module T = FStar.Tactics

noextract inline_for_extraction
//[@@FStar.Tactics.Effect.postprocess_for_extraction_with(fun () ->
//     T.norm [delta; iota; zeta_full; primops]; T.trefl ())]
let comp_tag = normalize (mk_string_t "HaclExample.comp")

module U32 = FStar.UInt32

#push-options "--z3rlimit 30 --fuel 30"
noextract inline_for_extraction let five' = normalize (nat_t_of_nat 5)
noextract inline_for_extraction let five: size_t_of five' = mk_size_t (U32.uint_to_t 5)
noextract inline_for_extraction let twenty' = normalize (nat_t_of_nat 20)
noextract inline_for_extraction let twenty: size_t_of twenty' = mk_size_t (U32.uint_to_t 20)
#pop-options

(** uint64_t[5] *)
[@@c_struct]
noextract inline_for_extraction
let five_u64s: typedef = array_typedef_sized U64.t five' five

(** uint64_t[20] *)
[@@c_struct]
noextract inline_for_extraction
let twenty_u64s: typedef = array_typedef_sized U64.t twenty' twenty

(** struct comp { uint64_t limbs[5]; uint64_t precomp[20]; }; *)

[@@c_struct]//;c_typedef]
noextract inline_for_extraction
let comp_fields: c_fields =
  fields_cons "limbs" five_u64s (
  fields_cons "precomp" twenty_u64s (
  fields_nil))

noextract inline_for_extraction
let comp = struct comp_tag comp_fields

noextract inline_for_extraction
let comp_view = struct_view comp_tag comp_fields

noextract inline_for_extraction
let comp_pcm = struct_pcm comp_tag comp_fields

[@@c_typedef]
noextract inline_for_extraction
let c_comp: typedef = typedef_struct comp_tag comp_fields

let _ = norm norm_c_typedef (mk_c_struct comp_tag comp_fields)

(** To demonstrate how our model could be used, we write a simple
    function that takes pointers to the limbs and precomp fields and
    passes them to helper functions (which in this case simply set on
    element of the corresponding array to zero) *)

let do_something_with_limbs
  (a: array U64.t)
: Steel unit
    (varray a)
    (fun _ -> varray a)
    (requires fun _ -> length a == 5)
    (ensures fun _ _ _ -> True)
= upd a (mk_size_t (U32.uint_to_t 2)) (U64.uint_to_t 0);
  return ()

let do_something_with_precomp
  (a: array U64.t)
: Steel (array_or_null U64.t)
    (varray a)
    (fun _ -> varray a)
    (requires fun _ -> length a == 20)
    (ensures fun _ _ _ -> True)
= upd a (mk_size_t (U32.uint_to_t 19)) (U64.uint_to_t 0);
  return (null _)

let test_alloc_free
  ()
: SteelT unit
    emp
    (fun _ -> emp)
=
  let a = malloc true (mk_size_t 42ul) in
  if Steel.C.Array.is_null a
  then begin
    Steel.C.Array.elim_varray_or_null_none a
  end else begin
    Steel.C.Array.elim_varray_or_null_some a;
    free a
  end;
  return ()

#push-options "--fuel 0 --print_universes --print_implicits --z3rlimit 30"

let test
  (p: ref comp comp_pcm)
: SteelT unit
    (p `pts_to_view` comp_view emptyset)
    (fun _ -> p `pts_to_view` comp_view emptyset)
= let q = addr_of_struct_field "limbs" p in
  let a = intro_varray q () in
  let r = addr_of_struct_field "precomp" p in
  let b = intro_varray r () in
  do_something_with_limbs a;
  let _ = do_something_with_precomp b in
  elim_varray q a ();
  elim_varray r b ();
  unaddr_of_struct_field "precomp" p r;
  unaddr_of_struct_field "limbs" p q;
  change_equal_slprop (p `pts_to_view` _) (p `pts_to_view` _);
  return ()

#pop-options
