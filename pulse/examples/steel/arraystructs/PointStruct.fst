module PointStruct

open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Connection
open Steel.C.Struct
open Steel.C.StructLiteral
open Steel.C.Typedef
open FStar.FunctionalExtensionality
open Steel.Effect
open Steel.Effect.Atomic
open Steel.C.Fields
open Steel.C.Reference

open FStar.FSet
open Typestring

module U32 = FStar.UInt32

unfold let int' = FStar.UInt32.t

[@@c_typedef]
noextract inline_for_extraction
let c_int': typedef = {
  carrier = option int';
  pcm = opt_pcm #int';
  view_type = int';
  view = opt_view int';
  is_unit = (fun x -> None? x);
}

module T = FStar.Tactics

noextract inline_for_extraction
//[@@FStar.Tactics.Effect.postprocess_for_extraction_with(fun () ->
//     T.norm [delta; iota; zeta_full; primops]; T.trefl ())]
let point_tag = normalize (mk_string_t "point")

[@@c_struct]
noextract inline_for_extraction
let point_fields: c_fields =
  fields_cons "x" c_int' (
  fields_cons "y" c_int' (
  fields_nil))

noextract inline_for_extraction
let point = struct point_tag point_fields

noextract inline_for_extraction
let point_view = struct_view point_tag point_fields

noextract inline_for_extraction
let point_pcm = struct_pcm point_tag point_fields

[@@c_typedef]
noextract inline_for_extraction
let c_point: typedef = typedef_struct point_tag point_fields

let _ = normalize (mk_c_struct point_tag point_fields)

noextract inline_for_extraction
let line_fields_second_half: c_fields =
  fields_cons "second" c_point fields_nil

noextract inline_for_extraction
let line_tag = normalize (mk_string_t "line")

unfold let norm_list =
  [delta_only
    [`%mk_c_struct;
     `%c_fields_t;
     `%List.Tot.fold_right;
     `%Typestring.mk_string_t;
     `%c_struct;
     ];
   iota; zeta; primops]

let _ = normalize (mk_c_struct line_tag (fields_cons "first" c_point line_fields_second_half))

#push-options "--fuel 0"

(*
let x_conn
: connection point_pcm (opt_pcm #int)
= struct_field point_tag point_fields "x"
*)

#push-options "--print_universes --print_implicits --z3rlimit 100 --query_stats"

open Steel.C.Reference

val swap (p: ref 'a point point_pcm)
: Steel unit
    (p `pts_to_view` point_view emptyset)
    (fun _ -> p `pts_to_view` point_view emptyset)
    (requires fun _ -> True)
    (ensures fun h q h' ->
      h' (p `pts_to_view` point_view emptyset) `struct_get` "x"
      == h (p `pts_to_view` point_view emptyset) `struct_get` "y" /\
      h' (p `pts_to_view` point_view emptyset) `struct_get` "y"
      == h (p `pts_to_view` point_view emptyset) `struct_get` "x")
      //True)

let swap p =
  let initial_point = gget (p `pts_to_view` point_view emptyset) in
  let q = addr_of_struct_field "x" p in
  let r = addr_of_struct_field "y" p in
  let x = opt_read_sel q in
  let y = opt_read_sel r in
  q `opt_write_sel` y;
  r `opt_write_sel` x;
  unaddr_of_struct_field "y" p r;
  unaddr_of_struct_field "x" p q;
  change_equal_slprop
    (p `pts_to_view` point_view (remove "x" (remove "y" (insert "y" (insert "x" emptyset)))))
    (p `pts_to_view` point_view emptyset);
  let final_point = gget (p `pts_to_view` point_view emptyset) in
  assert (struct_get #point_tag #point_fields #emptyset final_point "x" ==
    struct_get #point_tag #point_fields #emptyset initial_point "y");
  assert (struct_get #point_tag #point_fields #emptyset final_point "y" ==
    struct_get #point_tag #point_fields #emptyset initial_point "x");
  return ()

(*
assume val addr_of_struct_field_ref'
  (#tag: Type0) (#fields: c_fields) (#excluded: excluded_fields)
  (field: field_of fields)
  (p: ref 'a (struct_pcm tag fields))
: Steel (ref 'a (fields.get_field field).pcm)
    (p `pts_to_view` struct_view tag fields excluded)
    (fun q ->
      (p `pts_to_view` struct_view tag fields (insert field excluded)) `star`
      (q `pts_to_view` (fields.get_field field).view))
    (requires fun _ -> not (excluded field))
    (ensures fun h q h' -> 
      not (excluded field) /\
      q == Steel.C.Ref.ref_focus p (struct_field tag fields field) /\
      extract_field tag fields excluded field
        (h (p `pts_to_view` struct_view tag fields excluded))
       ==
        (h' (p `pts_to_view` struct_view tag fields (insert field excluded)),
         h' (q `pts_to_view` (fields.get_field field).view)))
*)

let generic_swap_sel (p:ref 'a 'c (opt_pcm #'c)) (q:ref 'b 'c (opt_pcm #'c))
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

val swap' (p: ref 'a point point_pcm)
: Steel unit
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
  return ()

(*
ref 'a (struct tag fields)
ref 'a (fields.get_field field).view_type
ref 'a view_t ...

struct: s:string -> x:Type{x == y:string{y == s}} -> c_fields -> Type
point = s:string{s == point_tag}

[@@c_typedef]
s = struct ..

[@@c_struct]
point_fields = fields_cons "a" s

[@@c_typedef]
point = struct point_tag point_fields

mark get_field, view_type, ... c_struct

norm [unfold c_typedef] point

p: ref 'a point  ...
---> (PointStruct.point, unit) struct

p: ref 'a int ...
*)

(*
TO PROVE:
extract_field v field = (w, x) 
get v field = x
get v field' = get w field' for all field' =!= field
*)

(* struct tag { point_fields ... } *)

(*

struct tag *p ;

int *q = &p->x;

q: ref (struct tag) #int (int_pcm)

EAddrOf (
  EField (
    TQualified "Example.t",
    (EBufRead (<<p>>, 0)),
    "x"))


Read:
    EBufRead (<<p>>, 0)

Write:
    EBufWrite (<<e>>, 0, <<e'>>)
or
    EAssign (EBufRead (<<e>>, 0), <<e'>>)

addr_of_struct_field "x" (p: ref 'a #(struct_pcm_carrier tag point_fields) (struct_pcm tag point_fields))
(* &(((struct tag)(*p)).x)

*)




*)

/// make pts_to_view stuff smt_fallback?
let addr_of_x' #a p excluded =
  let q = addr_of_struct_field #_ #point_tag #point_fields #excluded "x" p in
  //change_equal_slprop (q `pts_to_view` _) (q `pts_to_view` opt_view int);
  //change_equal_slprop (p `pts_to_view` _) (p `pts_to_view` point_view (insert "x" excluded));
  //slassert ((p `pts_to_view` point_view (insert "x" excluded)) `star`
  //     (q `pts_to_view` opt_view int));
  change_equal_slprop (q `pts_to_view` _)
    (pts_to_view #a #(option int) #(opt_pcm #int) q #int #false (opt_view int));
  change_equal_slprop (p `pts_to_view` _)
    (pts_to_view #a #point #point_pcm p
          #(struct' point_tag point_fields (insert #string "x" excluded)) #false 
         (point_view (insert "x" excluded)));
  //slassert ((pts_to_view #a #point #point_pcm p
  //        #(struct' point_tag point_fields (insert #string "x" excluded)) #false 
  //       (point_view (insert "x" excluded))) `star`
  //     (pts_to_view #a #(option int) #(opt_pcm #int) q #int #false (opt_view int)));
  //sladmit();
  return q

let point_fields k = match k with
  | X -> option int
  | Y -> option int
let point = restricted_t point_field point_fields

let point_fields_pcm k : pcm (point_fields k) = match k with
  | X -> opt_pcm #int
  | Y -> opt_pcm #int
let point_pcm = prod_pcm point_fields_pcm

let mk_point_f (x y: option int) (k: point_field): point_fields k = match k with
  | X -> x
  | Y -> y
  
let mk_point (x y: option int): point =
  on_domain point_field (mk_point_f x y)

let _x = struct_field point_fields_pcm X
let _y = struct_field point_fields_pcm Y

/// Taking pointers to the x and y fields of a point

let point_without_x x y
: Lemma (struct_without_field point_fields_pcm X (mk_point x y) `feq` Ghost.reveal (mk_point none y))
  [SMTPat (mk_point x y)]
= ()

let point_with_x x y
: Lemma (struct_with_field point_fields_pcm X x (mk_point None y) `feq`
         mk_point x y)
  [SMTPat (mk_point x y)]
= ()

let point_without_y x y
: Lemma (struct_without_field point_fields_pcm Y (mk_point x y) `feq` mk_point x None)
  [SMTPat (mk_point x y)]
= ()

let point_with_y x y
: Lemma (struct_with_field point_fields_pcm Y y (mk_point x None) `feq`
         mk_point x y)
  [SMTPat (mk_point x y)]
= ()

let addr_of_x #a #x #y p =
  let q = addr_of_struct_field p X (mk_point x y) in
  change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point None y);
  change_equal_slprop (q `pts_to` _) (q `pts_to` x);
  return q
  
let unaddr_of_x #a #x #y p q =
  unaddr_of_struct_field #_ #_ #_ #point_fields_pcm X q p (mk_point None y) x; // FIXME: WHY WHY WHY does F* infer the constant function (due to the type of q) instead?
  change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_y #a #x #y p =
  let q = addr_of_struct_field p Y (mk_point x y) in
  change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point x None);
  change_equal_slprop (q `pts_to` _) (q `pts_to` y);
  return q

let unaddr_of_y #a #x #y p q =
  unaddr_of_struct_field #_ #_ #_ #point_fields_pcm Y q p (mk_point x None) y; // same here
  change_equal_slprop (p `pts_to` _) (p `pts_to` _)
