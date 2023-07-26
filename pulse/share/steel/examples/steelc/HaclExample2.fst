module HaclExample2
open Steel.ST.GenElim
open Steel.ST.C.Types
open Steel.C.Typenat
open Steel.C.Typestring

module SZ = FStar.SizeT
module U64 = FStar.UInt64

(** In this file we demonstrate how Steel could be used to manipulate the following data type used in Hacl*:
      https://github.com/project-everest/hacl-star/blob/master/code/poly1305/Hacl.Impl.Poly1305.fsti#L18
    This Low* definition amounts to the struct definition
      struct poly1305_ctx { uint64_t limbs[5]; uint64_t precomp[20]; };
    and, with our new model of structs and arrays and pointer-to-field, can be expresesd directly in Steel.

    See PointStruct.fst for more detailed explanations of the various definitions needed below.
*)

noextract inline_for_extraction let five = normalize (nat_t_of_nat 5)
noextract inline_for_extraction let twenty = normalize (nat_t_of_nat 20)
noextract inline_for_extraction let comp_name = normalize (mk_string_t "HaclExample2.comp")

noextract
inline_for_extraction
[@@norm_field_attr]
let comp_fields =
  field_description_cons "limbs" (base_array0 five (scalar U64.t) 5sz) (
  field_description_cons "precomp" (base_array0 twenty (scalar U64.t) 20sz) (
  field_description_nil
  ))

noextract inline_for_extraction
let comp = struct0 comp_name "HaclExample2.comp" comp_fields

let _ = define_struct0 comp_name "HaclExample2.comp" comp_fields

(** To demonstrate how our model could be used, we write a simple
    function that takes pointers to the limbs and precomp fields and
    passes them to helper functions (which in this case simply set on
    element of the corresponding array to zero) *)

let do_something_with_limbs
  (#v: Ghost.erased (Seq.seq (scalar_t U64.t)))
  (a: array (scalar U64.t))
: ST (Ghost.erased (Seq.seq (scalar_t U64.t)))
    (array_pts_to a v)
    (fun v' -> array_pts_to a v')
    (requires
      array_length a == 5 /\
      full_seq (scalar U64.t) v
    )
    (ensures (fun v' ->
      full_seq (scalar U64.t) v'
    ))
= let p = array_cell a 2sz in
  write p 0uL;
  unarray_cell _ _ _;
  drop (has_array_cell _ _ _); 
  return _

let do_something_with_precomp
  (#v: Ghost.erased (Seq.seq (scalar_t U64.t)))
  (a: array (scalar U64.t))
: ST (ptr (scalar U64.t))
    (array_pts_to a v)
    (fun _ -> exists_ (fun (v': Seq.seq (scalar_t U64.t)) ->
      array_pts_to a v' `star`
      pure (full_seq (scalar U64.t) v')
    ))
    (requires
      array_length a == 20 /\
      full_seq (scalar U64.t) v
    )
    (ensures fun _ -> True)
= let p = array_cell a 19sz in
  write p 0uL;
  unarray_cell _ _ _;
  drop (has_array_cell _ _ _);
  noop ();
  return (null _)

let test_alloc_free
  ()
: STT unit
    emp
    (fun _ -> emp)
=
  let a = array_alloc (scalar bool) 42sz in
  let _ = gen_elim () in
  if array_is_null a
  then begin
    rewrite (array_pts_to_or_null _ _) emp;
    rewrite (freeable_or_null_array _) emp;
    noop ()
  end else begin
    let s = vpattern_replace (array_pts_to_or_null _) in
    rewrite (array_pts_to_or_null _ _) (array_pts_to a s);
    rewrite (freeable_or_null_array _) (freeable_array a);
    array_free a
  end

#push-options "--fuel 0 --print_universes --print_implicits --z3rlimit 128"
#restart-solver

let test
  (#v: Ghost.erased (typeof comp))
  (p: ref comp)
: ST (Ghost.erased (typeof comp))
    (p `pts_to` v)
    (fun v' -> p `pts_to` v')
    (full comp v)
    (fun v' -> full comp v')
= let q = struct_field p "limbs" #_ #(base_array0 five (scalar U64.t) 5sz) () in
  let a = array_of_base q in
  let r = struct_field p "precomp" #_ #(base_array0 twenty (scalar U64.t) 20sz) () in
  let _ = vpattern_replace (pts_to p) in // FIXME: WHY WHY WHY?
  let b = array_of_base r in
  let _ = do_something_with_limbs a in
  let _ = do_something_with_precomp b in
  let _ = gen_elim () in
  let _ = unarray_of_base q a in
  let _ = unarray_of_base r b in
  let _ = unstruct_field_alt p "precomp" r in
  let _ = unstruct_field_alt p "limbs" q in
  drop (has_struct_field p "limbs" q);
  drop (has_struct_field p "precomp" r);
  return _

#pop-options
