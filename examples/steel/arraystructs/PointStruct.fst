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
open Steel.C.Ref

open FStar.FSet
//open Steel.C.Reference

[@@c_typedef]
//noextract
//inline_for_extraction
let c_int: typedef = {
  carrier = option int;
  pcm = opt_pcm #int;
  view_type = int;
  view = opt_view int;
}

[@@c_struct]
//noextract
//inline_for_extraction
let point_fields: struct_fields = 
  fields_cons "x" c_int (
  fields_cons "y" c_int (
  fields_nil))

//noextract
//inline_for_extraction
let point = struct "point" point_fields

//noextract
//inline_for_extraction
let point_view = struct_view "point" point_fields

//let point = struct_pcm_carrier "point" point_fields

//noextract
//inline_for_extraction
let point_pcm = struct_pcm "point" point_fields

[@@c_typedef]
//noextract
//inline_for_extraction
let c_point: typedef = typedef_struct "point" point_fields

assume val a: Type0
assume val b: Type0
assume val c: Type0
assume val d: Type0
assume val e: Type0
assume val f: Type0
assume val g: Type0
assume val h: Type0
assume val i: Type0
assume val j: Type0
assume val k: Type0
assume val l: Type0
assume val m: Type0
assume val n: Type0
assume val o: Type0
assume val p: Type0
assume val q: Type0
assume val r: Type0
assume val s: Type0
assume val t: Type0
assume val u: Type0
assume val v: Type0
assume val w: Type0
assume val x: Type0
assume val y: Type0
assume val z: Type0
assume val zero: Type0
assume val one: Type0
assume val two: Type0
assume val three: Type0
assume val four: Type0
assume val five: Type0
assume val six: Type0
assume val seven: Type0
assume val eight: Type0
assume val nine: Type0
assume val underscore: Type0

assume val string_nil: Type0
assume val string_cons (c: Type0) (s: Type0): Type0

assume val struct_fields_nil: Type0
assume val struct_fields_cons
  (field: Type0) (t: Type0) (fields: Type0)
: Type0

assume val mk_c_typedef (viewtype: Type0) (field_descriptions: Type0): Type0

open FStar.String

let char_t_of_char (ch: char): Type0 =
  match ch with
  | 'a' -> a
  | 'b' -> b
  | 'c' -> c
  | 'd' -> d
  | 'e' -> e
  | 'f' -> f
  | 'g' -> g
  | 'h' -> h
  | 'i' -> i
  | 'j' -> j
  | 'k' -> k
  | 'l' -> l
  | 'm' -> m
  | 'n' -> n
  | 'o' -> o
  | 'p' -> p
  | 'q' -> q
  | 'r' -> r
  | 's' -> s
  | 't' -> t
  | 'u' -> u
  | 'v' -> v
  | 'w' -> w
  | 'x' -> x
  | 'y' -> y
  | 'z' -> z
  | '0' -> zero
  | '1' -> one
  | '2' -> two
  | '3' -> three
  | '4' -> four
  | '5' -> five
  | '6' -> six
  | '7' -> seven
  | '8' -> eight
  | '9' -> nine
  | '_' -> underscore
  | _ -> underscore

let rec string_t_of_chars (s: list char): Type0 =
  match s with
  | [] -> string_nil
  | c :: s -> string_cons (char_t_of_char c) (string_t_of_chars s)

let typedef_fields_of (fields: struct_fields) =
  List.Tot.fold_right
    (fun field fields' ->
      struct_fields_cons
        (string_t_of_chars (String.list_of_string field))
        (fields.get_field field).view_type
        fields')
    fields.cfields
    struct_fields_nil

unfold let norm_typedef_list =
  [delta_only
   [`%typedef_fields_of;
    `%List.Tot.fold_right;
    `%string_t_of_chars;
    `%char_t_of_char;
    `%String.list_of_string;
    `%Mktypedef?.view_type;
    `%Mkstruct_fields?.get_field;
    `%Mkstruct_fields?.cfields;
   ];
   iota; zeta; primops]

let _ =
  mk_c_typedef
    point
    (norm norm_typedef_list
      (typedef_fields_of (fields_cons "test_field" c_point point_fields)))
// TODO what effects?

#push-options "--fuel 0"

(*
let x_conn
: connection point_pcm (opt_pcm #int)
= struct_field "point" point_fields "x"
*)

#push-options "--print_universes --print_implicits"
// --z3rlimit 30"

open Steel.C.Reference

(*
val swap (p: ref 'a point point_pcm)
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

let swap #a p =
  let q: ref _ int _ = addr_of_struct_field "x" p in
  let r: ref _ int _ = addr_of_struct_field "y" p in
  let x = opt_read_sel q in
  let y = opt_read_sel r in
  q `opt_write_sel` y;
  r `opt_write_sel` x;
  unaddr_of_struct_field "y" p r;
  unaddr_of_struct_field "x" p q;
  change_equal_slprop (p `pts_to_view` _) (p `pts_to_view` _);
  return ()
  *)

(*
ref 'a (struct tag fields)
ref 'a (fields.get_field field).view_type
ref 'a view_t ...

struct: s:string -> x:Type{x == y:string{y == s}} -> struct_fields -> Type
point = s:string{s == "point"}

[@@c_typedef]
s = struct ..

[@@c_struct]
point_fields = fields_cons "a" s

[@@c_typedef]
point = struct "point" point_fields

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
  let q = addr_of_struct_field #_ #"point" #point_fields #excluded "x" p in
  //change_equal_slprop (q `pts_to_view` _) (q `pts_to_view` opt_view int);
  //change_equal_slprop (p `pts_to_view` _) (p `pts_to_view` point_view (insert "x" excluded));
  //slassert ((p `pts_to_view` point_view (insert "x" excluded)) `star`
  //     (q `pts_to_view` opt_view int));
  change_equal_slprop (q `pts_to_view` _)
    (pts_to_view #a #(option int) #(opt_pcm #int) q #int #false (opt_view int));
  change_equal_slprop (p `pts_to_view` _)
    (pts_to_view #a #point #point_pcm p
          #(struct' "point" point_fields (insert #string "x" excluded)) #false 
         (point_view (insert "x" excluded)));
  //slassert ((pts_to_view #a #point #point_pcm p
  //        #(struct' "point" point_fields (insert #string "x" excluded)) #false 
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
