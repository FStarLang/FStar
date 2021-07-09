module PointStruct

open Aggregates
open AggregateRef
open PCM.POD
open FStar.PCM
open FStar.FunctionalExtensionality
open Steel.Effect
module A = Steel.Effect.Atomic

type point_field = | X | Y
let point_fields k = match k with
  | X -> pod int
  | Y -> pod int
let point = restricted_t point_field point_fields

let point_fields_pcm k : pcm (point_fields k) = match k with
  | X -> pod_pcm int
  | Y -> pod_pcm int
let point_pcm = prod_pcm point_fields_pcm

let mk_point_f (x y: pod int) (k: point_field): point_fields k = match k with
  | X -> x
  | Y -> y
  
let mk_point (x y: Ghost.erased (pod int)): GTot point =
  on_domain point_field (mk_point_f (Ghost.reveal x) (Ghost.reveal y))

let _x = field point_fields_pcm X
let _y = field point_fields_pcm Y

let put_x x' x y
: Lemma (feq (put _x x' (mk_point x y)) (mk_point (Ghost.hide x') y))
  [SMTPat (put _x x' (mk_point x y))]
= ()

let put_y y' x y
: Lemma (feq (put _y y' (mk_point x y)) (mk_point x (Ghost.hide y')))
  [SMTPat (put _y y' (mk_point x y))]
= ()

/// Laws relating mk_point to PCM operations

let one_xy : squash (feq (one point_pcm) (mk_point none none))
= ()

// TODO
let merge_xy (x y: Ghost.erased (pod int)) x' y'
: Lemma
    (requires composable point_pcm
       (Ghost.reveal (mk_point x y))
       (Ghost.reveal (mk_point x' y')))
    (ensures
     feq (op point_pcm (Ghost.reveal (mk_point x y)) (Ghost.reveal (mk_point x' y')))
         (mk_point (op (point_fields_pcm X) (Ghost.reveal x) (Ghost.reveal x'))
                   (op (point_fields_pcm Y) (Ghost.reveal y) (Ghost.reveal y'))))
  [SMTPat (op point_pcm (Ghost.reveal (mk_point x y)) (Ghost.reveal (mk_point x' y')))]
= ()

/// Taking pointers to the x and y fields of a point

let addr_of_x #a #x #y p =
  let q = addr_of_lens p _x (mk_point x y) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point none y);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` x);
  A.return q

let un_addr_of_x #a #x #y p q =
  un_addr_of_lens q p _x (mk_point none y) x;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)

let addr_of_y #a #x #y p =
  let q = addr_of_lens p _y (mk_point x y) in
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` mk_point x none);
  A.change_equal_slprop (q `pts_to` _) (q `pts_to` y);
  A.return q

let un_addr_of_y #a #x #y p q =
  un_addr_of_lens q p _y (mk_point x none) y;
  A.change_equal_slprop (p `pts_to` _) (p `pts_to` _)
