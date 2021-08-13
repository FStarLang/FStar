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

noextract inline_for_extraction
//[@@FStar.Tactics.Effect.postprocess_for_extraction_with(fun () ->
//     T.norm [delta; iota; zeta_full; primops]; T.trefl ())]
let u32_or_u16_tag = normalize (mk_string_t "ScalarUnion.u32_or_u16")

[@@c_struct]
noextract inline_for_extraction
let u32_or_u16_fields: c_fields =
  fields_cons "as_u32" u32 (
  fields_cons "as_u16" u16 (
  fields_nil))

noextract inline_for_extraction
let u32_or_u16 = union u32_or_u16_tag u32_or_u16_fields

noextract inline_for_extraction
let u32_or_u16_view = union_view u32_or_u16_tag u32_or_u16_fields

noextract inline_for_extraction
let u32_or_u16_pcm = union_pcm u32_or_u16_tag u32_or_u16_fields

[@@c_typedef]
noextract inline_for_extraction
let c_u32_or_u16: typedef = typedef_union u32_or_u16_tag u32_or_u16_fields

let _ = norm norm_c_typedef (mk_c_union u32_or_u16_tag u32_or_u16_fields)

#push-options "--fuel 0"

(*
let x_conn
: connection u32_or_u16_pcm (opt_pcm #int)
= struct_field u32_or_u16_tag u32_or_u16_fields "x"
*)

#push-options "--print_universes --print_implicits"
// --z3rlimit 30"

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

let zero_u32_ref (p:ref 'a U32.t (opt_pcm #U32.t))
: Steel unit
  (p `pts_to_view` opt_view _)
  (fun _ -> p `pts_to_view` opt_view _)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)
= opt_write_sel p 0ul

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

(*
ref 'a (struct tag fields)
ref 'a (fields.get_field field).view_type
ref 'a view_t ...

struct: s:string -> x:Type{x == y:string{y == s}} -> c_fields -> Type
u32_or_u16 = s:string{s == u32_or_u16_tag}

[@@c_typedef]
s = struct ..

[@@c_struct]
u32_or_u16_fields = fields_cons "a" s

[@@c_typedef]
u32_or_u16 = struct u32_or_u16_tag u32_or_u16_fields

mark get_field, view_type, ... c_struct

norm [unfold c_typedef] u32_or_u16

p: ref 'a u32_or_u16  ...
---> (U32_Or_U16Struct.u32_or_u16, unit) struct

p: ref 'a int ...
*)

(*
TO PROVE:
extract_field v field = (w, x) 
get v field = x
get v field' = get w field' for all field' =!= field
*)

(* struct tag { u32_or_u16_fields ... } *)

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

addr_of_struct_field "x" (p: ref 'a #(struct_pcm_carrier tag u32_or_u16_fields) (struct_pcm tag u32_or_u16_fields))
(* &(((struct tag)(*p)).x)

*)




*)

/// make pts_to_view stuff smt_fallback?
let addr_of_x' #a p excluded =
  let q = addr_of_struct_field #_ #u32_or_u16_tag #u32_or_u16_fields #excluded "x" p in
  //change_equal_slprop (q `pts_to_view` _) (q `pts_to_view` opt_view int);
  //change_equal_slprop (p `pts_to_view` _) (p `pts_to_view` u32_or_u16_view (insert "x" excluded));
  //slassert ((p `pts_to_view` u32_or_u16_view (insert "x" excluded)) `star`
  //     (q `pts_to_view` opt_view int));
  change_equal_slprop (q `pts_to_view` _)
    (pts_to_view #a #(option int) #(opt_pcm #int) q #int #false (opt_view int));
  change_equal_slprop (p `pts_to_view` _)
    (pts_to_view #a #u32_or_u16 #u32_or_u16_pcm p
          #(struct' u32_or_u16_tag u32_or_u16_fields (insert #string "x" excluded)) #false 
         (u32_or_u16_view (insert "x" excluded)));
  //slassert ((pts_to_view #a #u32_or_u16 #u32_or_u16_pcm p
  //        #(struct' u32_or_u16_tag u32_or_u16_fields (insert #string "x" excluded)) #false 
  //       (u32_or_u16_view (insert "x" excluded))) `star`
  //     (pts_to_view #a #(option int) #(opt_pcm #int) q #int #false (opt_view int)));
  //sladmit();
  return q

let u32_or_u16_fields k = match k with
  | X -> option int
  | Y -> option int
let u32_or_u16 = restricted_t u32_or_u16_field u32_or_u16_fields

let u32_or_u16_fields_pcm k : pcm (u32_or_u16_fields k) = match k with
  | X -> opt_pcm #int
  | Y -> opt_pcm #int
let u32_or_u16_pcm = prod_pcm u32_or_u16_fields_pcm

let mk_u32_or_u16_f (x y: option int) (k: u32_or_u16_field): u32_or_u16_fields k = match k with
  | X -> x
  | Y -> y
  
let mk_u32_or_u16 (x y: option int): u32_or_u16 =
  on_domain u32_or_u16_field (mk_u32_or_u16_f x y)

let _x = struct_field u32_or_u16_fields_pcm X
let _y = struct_field u32_or_u16_fields_pcm Y

/// Taking u32_or_u16ers to the x and y fields of a u32_or_u16

let u32_or_u16_without_x x y
: Lemma (struct_without_field u32_or_u16_fields_pcm X (mk_u32_or_u16 x y) `feq` Ghost.reveal (mk_u32_or_u16 none y))
  [SMTPat (mk_u32_or_u16 x y)]
= ()

let u32_or_u16_with_x x y
: Lemma (struct_with_field u32_or_u16_fields_pcm X x (mk_u32_or_u16 None y) `feq`
         mk_u32_or_u16 x y)
  [SMTPat (mk_u32_or_u16 x y)]
= ()

let u32_or_u16_without_y x y
: Lemma (struct_without_field u32_or_u16_fields_pcm Y (mk_u32_or_u16 x y) `feq` mk_u32_or_u16 x None)
  [SMTPat (mk_u32_or_u16 x y)]
= ()

let u32_or_u16_with_y x y
: Lemma (struct_with_field u32_or_u16_fields_pcm Y y (mk_u32_or_u16 x None) `feq`
         mk_u32_or_u16 x y)
  [SMTPat (mk_u32_or_u16 x y)]
= ()

let addr_of_x #a #x #y p =
  let q = addr_of_struct_field p X (mk_u32_or_u16 x y) in
  change_equal_slprop (p `pts_to` _) (p `pts_to` mk_u32_or_u16 None y);
  change_equal_slprop (q `pts_to` _) (q `pts_to` x);
  return q
  
let unaddr_of_x #a #x #y p q =
  unaddr_of_struct_field #_ #_ #_ #u32_or_u16_fields_pcm X q p (mk_u32_or_u16 None y) x; // FIXME: WHY WHY WHY does F* infer the constant function (due to the type of q) instead?
  change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_y #a #x #y p =
  let q = addr_of_struct_field p Y (mk_u32_or_u16 x y) in
  change_equal_slprop (p `pts_to` _) (p `pts_to` mk_u32_or_u16 x None);
  change_equal_slprop (q `pts_to` _) (q `pts_to` y);
  return q

let unaddr_of_y #a #x #y p q =
  unaddr_of_struct_field #_ #_ #_ #u32_or_u16_fields_pcm Y q p (mk_u32_or_u16 x None) y; // same here
  change_equal_slprop (p `pts_to` _) (p `pts_to` _)
