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

[@@c_typedef]
noextract inline_for_extraction
let u64: typedef = {
  carrier = option U64.t;
  pcm = opt_pcm #U64.t;
  view_type = U64.t;
  view = opt_view U64.t;
  is_unit = (fun x -> None? x);
}

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

[@@c_struct]
noextract inline_for_extraction
let five_u64s: typedef = array_typedef_sized U64.t five' five

[@@c_struct]
noextract inline_for_extraction
let twenty_u64s: typedef = array_typedef_sized U64.t twenty' twenty

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

//let x : unit -> norm norm_list (mk_c_struct comp_tag comp_fields) = fun _ -> admit(); magic()
let _ = norm norm_c_typedef (mk_c_struct comp_tag comp_fields)

let do_something_with_limbs
  (a: array 'a U64.t)
: Steel unit
    (varray a)
    (fun _ -> varray a)
    (requires fun _ -> length a == 5)
    (ensures fun _ _ _ -> True)
= // let alar = split a (mk_size_t (U32.uint_to_t 1)) in
  // let q = split_left a (mk_size_t (U32.uint_to_t 1)) in
  // let p = ref_of_array q in
  // p `opt_write_sel` (U64.uint_to_t 0);
  // array_of_ref q p;
  // join' (GPair?.fst alar) (GPair?.snd alar);
  upd a (mk_size_t (U32.uint_to_t 2)) (U64.uint_to_t 0);
  return ()

let do_something_with_precomp
  (a: array 'a U64.t)
: Steel unit
    (varray a)
    (fun _ -> varray a)
    (requires fun _ -> length a == 20)
    (ensures fun _ _ _ -> True)
= upd a (mk_size_t (U32.uint_to_t 19)) (U64.uint_to_t 0);
  return ()

#push-options "--fuel 0 --print_universes --print_implicits --z3rlimit 30"

let test
  (p: ref 'a comp comp_pcm)
: SteelT unit
    (p `pts_to_view` comp_view emptyset)
    (fun _ -> p `pts_to_view` comp_view emptyset)
= let q = addr_of_struct_field "limbs" p in
  let a = intro_varray q () in
  let r = addr_of_struct_field "precomp" p in
  let b = intro_varray r () in
  do_something_with_limbs a;
  do_something_with_precomp b;
  elim_varray q a ();
  elim_varray r b ();
  unaddr_of_struct_field "precomp" p r;
  unaddr_of_struct_field "limbs" p q;
  change_equal_slprop (p `pts_to_view` _) (p `pts_to_view` _);
  return ()

#pop-options
