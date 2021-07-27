module PointStruct

open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Connection
open Steel.C.Struct
open FStar.FunctionalExtensionality
open Steel.Effect
module A = Steel.Effect.Atomic

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
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point None y);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` x);
  A.return q
  
let unaddr_of_x #a #x #y p q =
  unaddr_of_struct_field #_ #_ #_ #point_fields_pcm X q p (mk_point none y) x; // FIXME: WHY WHY WHY does F* infer the constant function (due to the type of q) instead?
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_y #a #x #y p =
  let q = addr_of_struct_field p Y (mk_point x y) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point x None);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` y);
  A.return q

let unaddr_of_y #a #x #y p q =
  unaddr_of_struct_field #_ #_ #_ #point_fields_pcm Y q p (mk_point x none) y; // same here
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)
