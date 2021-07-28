module PointStructSelectors

open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Connection
open Steel.C.Struct
open FStar.FunctionalExtensionality

open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic

open Steel.C.Ref
open Steel.C.Typedef
open Steel.C.StructLiteral
open FStar.List.Tot
open FStar.FunctionalExtensionality

(** ** BEGIN TODO impl and move to StructLiteral *)

(*
[@@__reduce__]
let rec iter_star_fields (fields: struct_fields) (f: field_of fields -> vprop): vprop =
  match fields with
  | [(field, _)] -> f field
  | (field, _) :: fields -> f field `star` iter_star_fields fields f
*)

[@@__steel_reduce__]
let pts_to_field_vprop
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
  (field: field_of fields)
: vprop
= ref_focus p (struct_field tag fields field) `pts_to_view` struct_views fields field

[@@__reduce__;__steel_reduce__;iter_unfold]
let rec pts_to_fields_vprop
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
  (fields': struct_fields)
: vprop
= match fields' with
  | [(field, _)] -> if has_field_bool fields field then pts_to_field_vprop tag fields p field else emp
  | (field, _) :: fields' ->
    if has_field_bool fields field then begin
      pts_to_field_vprop tag fields p field `star`
      pts_to_fields_vprop tag fields p fields'
    end else emp

[@@iter_unfold]
let rec pts_to_fields
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
  (h: rmem (p `pts_to_view` struct_view tag fields))
  (h': rmem (pts_to_fields_vprop tag fields p fields))
  //(prefix: list (string * typedef))
  (fields': struct_fields)
  //(hfields': squash (fields == rev prefix `append` fields'))
: prop
= match fields' with
  | [(field, _)] ->
    if has_field_bool fields field then
      can_be_split 
        (pts_to_fields_vprop tag fields p fields)
        (pts_to_field_vprop tag fields p field) /\
      h' (pts_to_field_vprop tag fields p field) ===
      h (p `pts_to_view` struct_view tag fields) `struct_get` field
    else True
  | (field, _) :: fields' ->
    if has_field_bool fields field then
      can_be_split 
        (pts_to_fields_vprop tag fields p fields)
        (pts_to_field_vprop tag fields p field) /\
      h' (pts_to_field_vprop tag fields p field) ===
      h (p `pts_to_view` struct_view tag fields) `struct_get` field /\
      pts_to_fields tag fields p h h' fields'
    else True

(*
[@@__reduce__;iter_unfold]
let rec iter_and_fields (fields: struct_fields) (f: field_of fields -> prop): prop =
  match fields with
  | [(field, _)] -> f field
  | (field, _) :: fields -> f field /\ iter_and_fields fields f
*)

(*
[@@__steel_reduce__;iter_unfold]
let pts_to_field
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
  (h: rmem (p `pts_to_view` struct_view tag fields))
  (h': rmem (iter_star_fields fields (pts_to_field_vprop tag fields p)))
  (field: field_of fields)
: prop
= can_be_split 
    (iter_star_fields fields (pts_to_field_vprop tag fields p))
    (pts_to_field_vprop tag fields p field) /\
  h' (pts_to_field_vprop tag fields p field) ==
  h (p `pts_to_view` struct_view tag fields) `struct_get` field
  *)

assume val explode (#opened: inames)
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
: SteelGhost unit opened
    (p `pts_to_view` struct_view tag fields)
    (fun _ -> pts_to_fields_vprop tag fields p fields)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      norm [delta_attr [`%iter_unfold]; iota; primops; zeta]
        (pts_to_fields tag fields p h h' fields))
//(iter_and_fields fields (pts_to_field tag fields p h h')))
        
// norm [delta_attr [`%iter_unfold]; iota; primops; zeta]

(*
assume val recombine (#opened: inames)
  (tag: string) (fields: struct_fields)
  (p: ref 'a (struct_pcm tag fields))
: SteelGhost unit opened
    (iter_star_fields fields (pts_to_field_vprop tag fields p))
    (fun _ -> p `pts_to_view` struct_view tag fields)
    (requires fun _ -> True)
    (ensures fun h _ h' -> pts_to_fields tag fields p h' h fields)
    *)
    
(** ** END TODO impl and move to StructLiteral *)

/// Point struct

let c_int: typedef = {
  carrier = option int;
  pcm = opt_pcm #int;
  view_type = int;
  view = opt_view int;
}

[@@__reduce__;iter_unfold]
let point_fields: struct_fields = [
  "x", c_int;
  "y", c_int;
]

let point = struct "point" point_fields

let point_pcm_carrier = struct_pcm_carrier "point" point_fields
let point_pcm: pcm point_pcm_carrier = struct_pcm "point" point_fields

/// (mk_point x y) represents (struct point){.x = x, .y = y}
/// (mk_point_pcm x y) same, but where x and y are PCM carrier values

let mk_point: int -> int -> point = mk_struct "point" point_fields
let mk_point_pcm: option int -> option int -> point_pcm_carrier = mk_struct_pcm "point" point_fields

/// Connections for the fields of a point

val _x: connection point_pcm (opt_pcm #int)
let _x = struct_field "point" point_fields "x"

val _y: connection point_pcm (opt_pcm #int)
let _y = struct_field "point" point_fields "y"

/// View for points

val point_view: sel_view point_pcm point false
let point_view = struct_view "point" point_fields

/// Explode and recombine

(*
val explode' (#opened: inames)
  (p: ref 'a point_pcm)
: SteelGhost unit opened
    (p `pts_to_view` struct_view "point" point_fields)
    (fun _ -> iter_star_fields point_fields (pts_to_field_vprop "point" point_fields p))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      normalize
        (iter_and_fields point_fields (pts_to_field "point" point_fields p h h')))

let explode' p = explode "point" point_fields p
*)

(*
val explode'' (#opened: inames)
  (p: ref 'a point_pcm)
: SteelGhost unit opened
    (p `pts_to_view` point_view)
    (fun _ ->
      (ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      h' (ref_focus p _x `pts_to_view` c_int.view) == h (p `pts_to_view` point_view) `struct_get` "x" /\
      h' (ref_focus p _y `pts_to_view` c_int.view) == h (p `pts_to_view` point_view) `struct_get` "y")

let explode'' p = explode "point" point_fields p
*)

(*
val recombine' (#opened: inames)
  (p: ref 'a point_pcm)
: SteelGhost unit opened
    ((ref_focus p _x `pts_to_view` c_int.view) `star`
     (ref_focus p _y `pts_to_view` c_int.view))
    (fun _ -> p `pts_to_view` point_view)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      h (ref_focus p _x `pts_to_view` c_int.view) == h' (p `pts_to_view` point_view) `struct_get` "x" /\
      h (ref_focus p _y `pts_to_view` c_int.view) == h' (p `pts_to_view` point_view) `struct_get` "y")

let recombine' p = recombine "point" point_fields p
*)

let aux p (h: rmem (p `pts_to_view` point_view))
  (h': rmem
     ((ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view)))
: Lemma
   (requires
      norm [delta_attr [`%iter_unfold]; iota; primops; zeta]
      (pts_to_fields "point" point_fields p h h' point_fields))
   (ensures begin
      let pointprop =
      ((ref_focus p _x `pts_to_view` c_int.view) `star`
      (ref_focus p _y `pts_to_view` c_int.view))
      in
      can_be_split pointprop (ref_focus p _x `pts_to_view` c_int.view) /\
      h' (ref_focus p _x `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get` "x" /\
      can_be_split pointprop (ref_focus p _y `pts_to_view` c_int.view) /\
      h' (ref_focus p _y `pts_to_view` c_int.view) === h (p `pts_to_view` point_view) `struct_get` "y"
   end)
= ()

/// Now, a contrived struct with twice as many fields (to stress-test)

[@@__reduce__;iter_unfold]
let quad_fields: struct_fields = [
  "x", c_int;
  "y", c_int;
  "z", c_int;
  "w", c_int;
]
let quad = struct "quad" quad_fields

let quad_pcm_carrier = struct_pcm_carrier "quad" quad_fields
let quad_pcm: pcm quad_pcm_carrier = struct_pcm "quad" quad_fields

/// (mk_quad x y) represents (struct quad){.x = x, .y = y}
/// (mk_quad_pcm x y) same, but where x and y are PCM carrier values

let mk_quad: int -> int -> int -> int -> quad = mk_struct "quad" quad_fields
let mk_quad_pcm: option int -> option int -> option int -> option int -> quad_pcm_carrier = mk_struct_pcm "quad" quad_fields

/// Connections for the fields of a quad

[@@iter_unfold] let _quad_x: connection quad_pcm (opt_pcm #int) = struct_field "quad" quad_fields "x"
[@@iter_unfold] let _quad_y: connection quad_pcm (opt_pcm #int) = struct_field "quad" quad_fields "y"
[@@iter_unfold] let _quad_z: connection quad_pcm (opt_pcm #int) = struct_field "quad" quad_fields "z"
[@@iter_unfold] let _quad_w: connection quad_pcm (opt_pcm #int) = struct_field "quad" quad_fields "w"

/// View for quads

[@@iter_unfold] let quad_view: sel_view quad_pcm quad false = struct_view "quad" quad_fields

/// Explode and recombine

(*
val explode_quad' (#opened: inames)
  (p: ref 'a quad_pcm)
: SteelGhost unit opened
    (p `pts_to_view` struct_view "quad" quad_fields)
    (fun _ -> iter_star_fields quad_fields (pts_to_field_vprop "quad" quad_fields p))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      norm [delta_attr [`%iter_unfold]; iota; primops; zeta]
        (iter_and_fields quad_fields (pts_to_field "quad" quad_fields p h h')))

let explode_quad' p = explode "quad" quad_fields p
*)

(*
val explode_quad'' (#opened: inames)
  (p: ref 'a quad_pcm)
: SteelGhost unit opened
    (p `pts_to_view` quad_view)
    (fun _ ->
      (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
        (ref_focus p _quad_w `pts_to_view` c_int.view))))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let quadprop =
        (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
          (ref_focus p _quad_w `pts_to_view` c_int.view)))
      in
      can_be_split quadprop (ref_focus p _quad_x `pts_to_view` c_int.view) /\
      h' (ref_focus p _quad_x `pts_to_view` c_int.view) == h (p `pts_to_view` quad_view) `struct_get` "x" /\
      can_be_split quadprop (ref_focus p _quad_y `pts_to_view` c_int.view) /\
      h' (ref_focus p _quad_y `pts_to_view` c_int.view) == h (p `pts_to_view` quad_view) `struct_get` "y" /\
      can_be_split quadprop (ref_focus p _quad_z `pts_to_view` c_int.view) /\
      h' (ref_focus p _quad_z `pts_to_view` c_int.view) == h (p `pts_to_view` quad_view) `struct_get` "z" /\
      can_be_split quadprop (ref_focus p _quad_w `pts_to_view` c_int.view) /\
      h' (ref_focus p _quad_w `pts_to_view` c_int.view) == h (p `pts_to_view` quad_view) `struct_get` "w")
*)

#push-options "--z3rlimit 30 --query_stats"

#pop-options
#push-options "--fuel 2 --query_stats"

[@@iter_unfold] let x: field_of quad_fields = mk_field_of quad_fields "x"
[@@iter_unfold] let y: field_of quad_fields = mk_field_of quad_fields "y"
[@@iter_unfold] let z: field_of quad_fields = mk_field_of quad_fields "z"
[@@iter_unfold] let w: field_of quad_fields = mk_field_of quad_fields "w"

module T = FStar.Tactics

let norm_list = [
  delta_attr [`%iter_unfold];
  delta_only [
    `%map; `%mem; `%fst; `%Mktuple2?._1;
    `%assoc;
    `%Some?.v
  ];
  iota; primops; zeta
]

let quad_aux (p: ref 'a quad_pcm) (h: rmem (p `pts_to_view` quad_view))
  (h': rmem
     ((ref_focus p _quad_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
        (ref_focus p _quad_w `pts_to_view` c_int.view)))))
: squash
   ((
      norm norm_list//[delta_attr [`%iter_unfold]; iota; primops; zeta]
        (pts_to_fields "quad" quad_fields p h h' quad_fields))
   ==
   (begin
      let quadprop =
        (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
          (ref_focus p _quad_w `pts_to_view` c_int.view)))
      in
      (can_be_split quadprop (ref_focus p _quad_x `pts_to_view` c_int.view) /\
       h' (ref_focus p _quad_x `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` x) /\
      ((can_be_split quadprop (ref_focus p _quad_y `pts_to_view` c_int.view) /\
       h' (ref_focus p _quad_y `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` y) /\
       ((can_be_split quadprop (ref_focus p _quad_z `pts_to_view` c_int.view) /\
         h' (ref_focus p _quad_z `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` z) /\
         (can_be_split quadprop (ref_focus p _quad_w `pts_to_view` c_int.view) /\
          h' (ref_focus p _quad_w `pts_to_view` c_int.view) === h (p `pts_to_view` quad_view) `struct_get` w)))
   end))
= _ by (T.trefl ())
//_ by (
//    T.norm norm_list;
//    T.trefl ())

(*
let quad_unfold_iter_star_fields p
: Lemma
    (norm [delta_attr [`%iter_unfold]; iota; primops; zeta]
    (iter_star_fields quad_fields (pts_to_field_vprop "quad" quad_fields p)) ==
     (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
        (ref_focus p _quad_w `pts_to_view` c_int.view))))
= ()
*)

#push-options "--query_stats"

let explode_quad'' p =
  explode "quad" quad_fields p;
  //quad_unfold_iter_star_fields p;
  //change_equal_slprop
  //  (iter_star_fields quad_fields (pts_to_field_vprop "quad" quad_fields p))
  //  ((ref_focus p _quad_x `pts_to_view` c_int.view) `star`
  //   ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
  //    ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
  //     (ref_focus p _quad_w `pts_to_view` c_int.view))));
  ()

(*
val recombine_quad' (#opened: inames)
  (p: ref 'a quad_pcm)
: SteelGhost unit opened
    ((ref_focus p _quad_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
       (ref_focus p _quad_w `pts_to_view` c_int.view))))
    (fun _ -> p `pts_to_view` quad_view)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let quadprop =
        (ref_focus p _quad_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
          (ref_focus p _quad_w `pts_to_view` c_int.view)))
      in
      // assert (can_be_split' quadprop (ref_focus p _quad_x `pts_to_view` c_int.view));
      // assert (can_be_split' quadprop (ref_focus p _quad_y `pts_to_view` c_int.view));
      // assert (can_be_split' quadprop (ref_focus p _quad_z `pts_to_view` c_int.view));
      // assert (can_be_split' quadprop (ref_focus p _quad_w `pts_to_view` c_int.view));
      h (ref_focus p _quad_x `pts_to_view` c_int.view) == h' (p `pts_to_view` quad_view) `struct_get` "x" /\
      h (ref_focus p _quad_y `pts_to_view` c_int.view) == h' (p `pts_to_view` quad_view) `struct_get` "y" /\
      h (ref_focus p _quad_z `pts_to_view` c_int.view) == h' (p `pts_to_view` quad_view) `struct_get` "z" /\
      h (ref_focus p _quad_w `pts_to_view` c_int.view) == h' (p `pts_to_view` quad_view) `struct_get` "w")

let recombine_quad' p =
  quad_unfold_iter_star_fields p;
  change_equal_slprop
    ((ref_focus p _quad_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _quad_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _quad_z `pts_to_view` c_int.view) `star`
       (ref_focus p _quad_w `pts_to_view` c_int.view))))
    (iter_star_fields quad_fields (pts_to_field_vprop "quad" quad_fields p));
  recombine "quad" quad_fields p
*)

/// 5 fields!

[@@__reduce__;iter_unfold]
let quint_fields: struct_fields = [
  "x", c_int;
  "y", c_int;
  "z", c_int;
  "w", c_int;
  "v", c_int;
]
let quint = struct "quint" quint_fields

let quint_pcm_carrier = struct_pcm_carrier "quint" quint_fields
let quint_pcm: pcm quint_pcm_carrier = struct_pcm "quint" quint_fields

let mk_quint: int -> int -> int -> int -> int -> quint = mk_struct "quint" quint_fields
let mk_quint_pcm: option int -> option int -> option int -> option int -> option int -> quint_pcm_carrier = mk_struct_pcm "quint" quint_fields

/// Connections for the fields of a quint

let _quint_x: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "x"
let _quint_y: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "y"
let _quint_z: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "z"
let _quint_w: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "w"
let _quint_v: connection quint_pcm (opt_pcm #int) = struct_field "quint" quint_fields "v"

/// View for quints

let quint_view: sel_view quint_pcm quint false = struct_view "quint" quint_fields

/// Explode and recombine

(*
val explode_quint' (#opened: inames)
  (p: ref 'a quint_pcm)
: SteelGhost unit opened
    (p `pts_to_view` struct_view "quint" quint_fields)
    (fun _ -> iter_star_fields quint_fields (pts_to_field_vprop "quint" quint_fields p))
    (requires fun _ -> True)
    (ensures fun h _ h' -> iter_and_fields quint_fields (pts_to_field "quint" quint_fields p h h'))

let explode_quint' p = explode "quint" quint_fields p
*)

#restart-solver

val explode_quint'' (#opened: inames)
  (p: ref 'a quint_pcm)
: SteelGhost unit opened
    (p `pts_to_view` quint_view)
    (fun _ ->
      (ref_focus p _quint_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
         (ref_focus p _quint_v `pts_to_view` c_int.view)))))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let quintprop =
        (ref_focus p _quint_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
          ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
           (ref_focus p _quint_v `pts_to_view` c_int.view))))
      in
      can_be_split quintprop (ref_focus p _quint_x `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_x `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "x" /\
      can_be_split quintprop (ref_focus p _quint_y `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_y `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "y" /\
      can_be_split quintprop (ref_focus p _quint_z `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_z `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "z" /\
      can_be_split quintprop (ref_focus p _quint_w `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_w `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "w" /\
      can_be_split quintprop (ref_focus p _quint_v `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_v `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "v")

let aux p (h: rmem (p `pts_to_view` quint_view))
  (h': rmem
     ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
         (ref_focus p _quint_v `pts_to_view` c_int.view))))))
: Lemma
   (requires
      norm [delta_attr [`%iter_unfold]; iota; primops; zeta]
      (pts_to_fields "quint" quint_fields p h h' quint_fields))
   (ensures begin
      let quintprop =
        (ref_focus p _quint_x `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
         ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
          ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
           (ref_focus p _quint_v `pts_to_view` c_int.view))))
      in
      can_be_split quintprop (ref_focus p _quint_x `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_x `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "x" /\
      can_be_split quintprop (ref_focus p _quint_y `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_y `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "y" /\
      can_be_split quintprop (ref_focus p _quint_z `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_z `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "z" /\
      can_be_split quintprop (ref_focus p _quint_w `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_w `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "w" /\
      can_be_split quintprop (ref_focus p _quint_v `pts_to_view` c_int.view) /\
      h' (ref_focus p _quint_v `pts_to_view` c_int.view) == h (p `pts_to_view` quint_view) `struct_get` "v"
   end)
= admit()

(*
let quint_unfold_iter_star_fields p
: Lemma
    (iter_star_fields quint_fields (pts_to_field_vprop "quint" quint_fields p) ==
     (ref_focus p _quint_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
         (ref_focus p _quint_v `pts_to_view` c_int.view)))))
= ()
*)

#restart-solver

//#push-options "--z3rlimit 30"

let explode_quint'' p =
  explode "quint" quint_fields p;
  //quint_unfold_iter_star_fields p;
  //change_equal_slprop
  //  (iter_star_fields quint_fields (pts_to_field_vprop "quint" quint_fields p))
  //  ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
  //   ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
  //    ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
  //     ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
  //      (ref_focus p _quint_v `pts_to_view` c_int.view)))));
  ()

//#pop-options

val recombine_quint' (#opened: inames)
  (p: ref 'a quint_pcm)
: SteelGhost unit opened
    ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
        (ref_focus p _quint_v `pts_to_view` c_int.view)))))
    (fun _ -> p `pts_to_view` quint_view)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let quintprop =
        ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
         ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
          ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
           ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
            (ref_focus p _quint_v `pts_to_view` c_int.view)))))
      in
      assert (can_be_split' quintprop (ref_focus p _quint_x `pts_to_view` c_int.view));
      assert (can_be_split' quintprop (ref_focus p _quint_y `pts_to_view` c_int.view));
      assert (can_be_split' quintprop (ref_focus p _quint_z `pts_to_view` c_int.view));
      assert (can_be_split' quintprop (ref_focus p _quint_w `pts_to_view` c_int.view));
      assert (can_be_split' quintprop (ref_focus p _quint_v `pts_to_view` c_int.view));
      h (ref_focus p _quint_x `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "x" /\
      h (ref_focus p _quint_y `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "y" /\
      h (ref_focus p _quint_z `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "z" /\
      h (ref_focus p _quint_w `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "w" /\
      h (ref_focus p _quint_v `pts_to_view` c_int.view) == h' (p `pts_to_view` quint_view) `struct_get` "v")

#push-options "--z3rlimit 20"

let recombine_quint' p =
  quint_unfold_iter_star_fields p;
  change_equal_slprop
    ((ref_focus p _quint_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _quint_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _quint_z `pts_to_view` c_int.view) `star`
       ((ref_focus p _quint_w `pts_to_view` c_int.view) `star`
        (ref_focus p _quint_v `pts_to_view` c_int.view)))))
    (iter_star_fields quint_fields (pts_to_field_vprop "quint" quint_fields p));
  recombine "quint" quint_fields p

#pop-options

/// 8 fields:

let oct_fields: struct_fields = [
  "x", c_int;
  "y", c_int;
  "z", c_int;
  "w", c_int;
  "v", c_int;
  "u", c_int;
  "t", c_int;
  "s", c_int;
]
let oct = struct "oct" oct_fields

let oct_pcm_carrier = struct_pcm_carrier "oct" oct_fields
let oct_pcm: pcm oct_pcm_carrier = struct_pcm "oct" oct_fields

let mk_oct: int -> int -> int -> int -> int -> int -> int -> int -> oct = mk_struct "oct" oct_fields
let mk_oct_pcm: option int -> option int -> option int -> option int -> option int -> option int -> option int -> option int -> oct_pcm_carrier = mk_struct_pcm "oct" oct_fields

/// Connections for the fields of a oct

let _oct_x: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "x"
let _oct_y: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "y"
let _oct_z: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "z"
let _oct_w: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "w"
let _oct_v: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "v"
let _oct_u: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "u"
let _oct_t: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "t"
let _oct_s: connection oct_pcm (opt_pcm #int) = struct_field "oct" oct_fields "s"

/// View for octs

let oct_view: sel_view oct_pcm oct false = struct_view "oct" oct_fields

/// Explode and recombine

val explode_oct' (#opened: inames)
  (p: ref 'a oct_pcm)
: SteelGhost unit opened
    (p `pts_to_view` struct_view "oct" oct_fields)
    (fun _ -> iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p))
    (requires fun _ -> True)
    (ensures fun h _ h' -> iter_and_fields oct_fields (pts_to_field "oct" oct_fields p h h'))

let explode_oct' p = explode "oct" oct_fields p

val explode_oct'' (#opened: inames)
  (p: ref 'a oct_pcm)
: SteelGhost unit opened
    (p `pts_to_view` oct_view)
    (fun _ ->
      ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
            ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
             (ref_focus p _oct_s `pts_to_view` c_int.view)))))))))
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      True)
      // let octprop =
      //   ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      //    ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
      //     ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
      //      ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
      //       ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
      //        ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
      //         ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
      //          (ref_focus p _oct_s `pts_to_view` c_int.view))))))))
      // in
      // assert (can_be_split' octprop (ref_focus p _oct_x `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_y `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_z `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_w `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_v `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_u `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_t `pts_to_view` c_int.view));
      // assert (can_be_split' octprop (ref_focus p _oct_s `pts_to_view` c_int.view));
      // h' (ref_focus p _oct_x `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "x" /\
      // h' (ref_focus p _oct_y `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "y" /\
      // h' (ref_focus p _oct_z `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "z" /\
      // h' (ref_focus p _oct_w `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "w" /\
      // h' (ref_focus p _oct_v `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "v" /\
      // h' (ref_focus p _oct_u `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "u" /\
      // h' (ref_focus p _oct_t `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "t" /\
      // h' (ref_focus p _oct_s `pts_to_view` c_int.view) == h (p `pts_to_view` oct_view) `struct_get` "s")

let oct_unfold_iter_star_fields p
: Lemma
    (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p) ==
     ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_s `pts_to_view` c_int.view)))))))))
= assert_norm (
    iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p) ==
     ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_s `pts_to_view` c_int.view)))))))))

#restart-solver
#push-options "--z3rlimit 40 --query_stats"

let explode_oct'' p =
  explode "oct" oct_fields p;
  // OOMs
  //change_slprop_rel
  //  (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p))
  //  ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
  //    ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
  //     ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
  //      ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
  //       ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
  //        ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
  //         ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
  //          (ref_focus p _oct_s `pts_to_view` c_int.view))))))))
  //  (fun _ _ -> True)
  //  (fun m ->
  //    assert_norm
  //      (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p) ==
  //      ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
  //        ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
  //         ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
  //          ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
  //           ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
  //            ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
  //             ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
  //              (ref_focus p _oct_s `pts_to_view` c_int.view))))))))));
  oct_unfold_iter_star_fields p;
  change_equal_slprop
    (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p))
    ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_s `pts_to_view` c_int.view))))))));
  ()

#pop-options

val recombine_oct' (#opened: inames)
  (p: ref 'a oct_pcm)
: SteelGhost unit opened
    ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
     ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
        (ref_focus p _oct_v `pts_to_view` c_int.view)))))
    (fun _ -> p `pts_to_view` oct_view)
    (requires fun _ -> True)
    (ensures fun h _ h' ->
      let octprop =
        ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_v `pts_to_view` c_int.view)))))
      in
      assert (can_be_split' octprop (ref_focus p _oct_x `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_y `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_z `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_w `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_v `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_u `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_t `pts_to_view` c_int.view));
      assert (can_be_split' octprop (ref_focus p _oct_s `pts_to_view` c_int.view));
      h (ref_focus p _oct_x `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "x" /\
      h (ref_focus p _oct_y `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "y" /\
      h (ref_focus p _oct_z `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "z" /\
      h (ref_focus p _oct_w `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "w" /\
      h (ref_focus p _oct_v `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "v" /\
      h (ref_focus p _oct_u `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "u" /\
      h (ref_focus p _oct_t `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "t" /\
      h (ref_focus p _oct_s `pts_to_view` c_int.view) == h' (p `pts_to_view` oct_view) `struct_get` "s")

#restart-solver
#push-options "--z3rlimit 20"

let recombine_oct' p =
  oct_unfold_iter_star_fields p;
  change_equal_slprop
    ((ref_focus p _oct_x `pts_to_view` c_int.view) `star`
      ((ref_focus p _oct_y `pts_to_view` c_int.view) `star`
       ((ref_focus p _oct_z `pts_to_view` c_int.view) `star`
        ((ref_focus p _oct_w `pts_to_view` c_int.view) `star`
         ((ref_focus p _oct_v `pts_to_view` c_int.view) `star`
          ((ref_focus p _oct_u `pts_to_view` c_int.view) `star`
           ((ref_focus p _oct_t `pts_to_view` c_int.view) `star`
            (ref_focus p _oct_s `pts_to_view` c_int.view))))))))
    (iter_star_fields oct_fields (pts_to_field_vprop "oct" oct_fields p));
  recombine "oct" oct_fields p

#pop-options
