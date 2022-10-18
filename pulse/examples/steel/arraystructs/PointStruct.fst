module PointStruct

open Steel.C.Model.PCM
open Steel.C.Opt
open Steel.C.Model.Connection
open Steel.C.Model.Struct
open Steel.C.StructLiteral
open Steel.C.Typedef
open FStar.FunctionalExtensionality
open Steel.Effect
open Steel.Effect.Atomic
open Steel.C.Fields
open Steel.C.Reference
open Steel.C.TypedefNorm

open FStar.FSet
open Steel.C.Typestring

module U32 = FStar.UInt32

(** A struct is encoded by what amounts to a list of (field name, typedef) pairs.
    In this example, we define a struct named point with two u32 fields; to do so
    we need a typedef for u32s, which can be found in Steel.C.StdInt. *)
module I = Steel.C.StdInt

module T = FStar.Tactics

(** To enforce nominality, structs are labelled by struct tags, which
    are represented by strings encoded as F* types. This encoding allows
    struct tags to stick around after erasure to OCaml.
    
    TODO the normalization is only needed for extraction, and so it
    should be possible to use postprocess_for_extraction_with instead
    of normalize. However, at present it seems that
    postprocess_for_extraction_with does not run on definitions of
    type Type. *)

noextract inline_for_extraction
//[@@FStar.Tactics.Effect.postprocess_for_extraction_with(fun () ->
//     T.norm [delta; iota; zeta_full; primops]; T.trefl ())]
let point_tag = normalize (mk_string_t "PointStruct.point")

(** point_fields is a representation of the list of (field name,
    typedef) pairs of the point struct we are defining.  For a more
    detailed explanation for why this list is constructed using
    fields_cons and fields_nil rather than as a normal F* list, see
    Steel.C.Fields.fsti *)

[@@c_struct]
noextract inline_for_extraction
let point_fields: c_fields =
  fields_cons "x" I.uint32 (
  fields_cons "y" I.uint32 (
  fields_nil))

(** The type of (struct point) values *)
noextract inline_for_extraction
let point = struct point_tag point_fields

(** A way of viewing (struct point) PCM carrier values as (struct point) values *)
noextract inline_for_extraction
let point_view = struct_view point_tag point_fields

(** The PCM used to model the point struct *)
noextract inline_for_extraction
let point_pcm = struct_pcm point_tag point_fields

(** A typedef for the point struct (useful if this struct needs to be nested inside another struct definition) *)
[@@c_typedef]
noextract inline_for_extraction
let c_point: typedef = typedef_struct point_tag point_fields

(** Define the point struct. Karamel detects this definition and
    emits a corresponding C typedef at extraction time.  See
    Steel.C.StructLiteral.mk_c_struct for more information. *)
let _ = norm norm_c_typedef (mk_c_struct point_tag point_fields)

(** There is some flexibility in how these definitions can be constructed.
    Below, we define
      struct line { struct point first; struct point second; };
    but split the list of (field name, typedef) pairs across two
    definitions: .second is declared in the definition below, while
    .first is declared "inline" in the call to mk_c_struct parsed by
    Karamel.

    This code is just to illustrate that extraction is fairly
    flexible: all Karamel cares about is that the call to mk_c_struct
    normalizes (under rules norm_c_typedef) to a valid struct
    definition. In practice, it isn't recommended to split the list of
    fields like this. *)
noextract inline_for_extraction
let line_fields_second_half: c_fields =
  fields_cons "second" c_point fields_nil

noextract inline_for_extraction
let line_tag = normalize (mk_string_t "PointStruct.line")

let _ = norm norm_c_typedef (mk_c_struct line_tag (fields_cons "first" c_point line_fields_second_half))

#push-options "--fuel 0"

#push-options "--print_universes --print_implicits --z3rlimit 100 --query_stats"

open Steel.C.Reference

(** To illustrate pointer-to-field in action, we write a function swap
    that swaps x and y coordinates of a point struct. *)
val swap (p: ref point point_pcm)
: Steel unit
    (p `pts_to_view` point_view emptyset)
    (fun _ -> p `pts_to_view` point_view emptyset)
    (requires fun _ -> True)
    (ensures fun h q h' ->
      h' (p `pts_to_view` point_view emptyset) `struct_get` "x"
      == h (p `pts_to_view` point_view emptyset) `struct_get` "y" /\
      h' (p `pts_to_view` point_view emptyset) `struct_get` "y"
      == h (p `pts_to_view` point_view emptyset) `struct_get` "x")

let swap p =
  let initial_point = gget (p `pts_to_view` point_view emptyset) in
  (** Take pointers to the "x" and "y" fields *)
  let q = addr_of_struct_field "x" p in
  let r = addr_of_struct_field "y" p in
  let x = opt_read_sel q in
  let y = opt_read_sel r in
  q `opt_write_sel` y;
  r `opt_write_sel` x;
  (** Give ownership of x and y fields back to p *)
  unaddr_of_struct_field "y" p r;
  unaddr_of_struct_field "x" p q;
  (** The view for structs is parameterized by a set of fields that have been loaned out.
      When these loans are returned to p, the corresponding field names are removed from the set of loaned fields.
      However, this new set is not definitionally equal to emptyset, the following equality needs to be proved by SMT: *)
  change_equal_slprop
    (p `pts_to_view` point_view (remove "x" (remove "y" (insert "y" (insert "x" emptyset)))))
    (p `pts_to_view` point_view emptyset);
    (** TOOD in the future, may want to make struct_view smt_fallback in its first argument and mark point_view as unfold *)
  (** For some reason these assertions is necessary to get the program
      to verify. It's unclear why, since such assertions are normally
      easily provable by SMT *)
  let final_point = gget (p `pts_to_view` point_view emptyset) in
  assert (struct_get #point_tag #point_fields #emptyset final_point "x" ==
    struct_get #point_tag #point_fields #emptyset initial_point "y");
  assert (struct_get #point_tag #point_fields #emptyset final_point "y" ==
    struct_get #point_tag #point_fields #emptyset initial_point "x");
  return ()

(** We can also define swap by calling a helper function that swaps
    any two pointers.  This demonstrates that one can manipulate
    pointers in a generic way: the helper function does not need to
    know that its inputs are pointers to fields of a struct in order
    to work. *)
let generic_swap_sel (p:ref 'c (opt_pcm #'c)) (q:ref 'c (opt_pcm #'c))
: Steel unit
  ((p `pts_to_view` opt_view _) `star` (q `pts_to_view` opt_view _))
  (fun _ -> (p `pts_to_view` opt_view _) `star` (q `pts_to_view` opt_view _))
  (requires (fun _ -> True))
  (ensures (fun h _ h' ->
    h' (p `pts_to_view` opt_view _) == h (q `pts_to_view` opt_view _) /\
    h' (q `pts_to_view` opt_view _) == h (p `pts_to_view` opt_view _)
  ))
= (* A tmp = *p; *)
  let tmp = opt_read_sel p in
  (* *p = *q; *)
  let vy = opt_read_sel q in
  opt_write_sel p vy;
  (* *q = tmp *)
  opt_write_sel q tmp;
  return ()

val swap' (p: ref point point_pcm)
: Steel (ptr point point_pcm)
    (p `pts_to_view` point_view emptyset)
    (fun _ -> p `pts_to_view` point_view emptyset)
    (requires fun _ -> True)
    (ensures fun h q h' ->
      //h' (p `pts_to_view` point_view emptyset) `struct_get` "x"
      //== h (p `pts_to_view` point_view emptyset) `struct_get` "y" /\
      //h' (p `pts_to_view` point_view emptyset) `struct_get` "y"
      //== h (p `pts_to_view` point_view emptyset) `struct_get` "x")
      True)

let swap' p =
  let q = addr_of_struct_field "x" p in
  let r = addr_of_struct_field "y" p in
  generic_swap_sel q r;
  unaddr_of_struct_field "y" p r;
  unaddr_of_struct_field "x" p q;
  change_equal_slprop (p `pts_to_view` _) (p `pts_to_view` _);
  return (null _ _)

let test_malloc_free () : SteelT unit emp (fun _ -> emp) =
  let c = malloc 42ul in
  if is_null c _
  then begin
    elim_pts_to_view_or_null_null c (opt_view _);
    return ()
  end else begin
    elim_pts_to_view_or_null_not_null c (opt_view _);
    free c
  end;
  return ()

