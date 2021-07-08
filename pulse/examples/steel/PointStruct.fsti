module PointStruct

open Aggregates
open AggregateRef
open PCM.POD
open FStar.PCM
//open FStar.FunctionalExtensionality
open Steel.Effect
//module A = Steel.Effect.Atomic

/// Suppose we have the following struct representing 2d points:
///   struct point { int x, y; };
///
/// Carrier of PCM for struct point:

val point : Type0

/// PCM for struct point:

val point_pcm : pcm point

/// (mk_point x y) represents (struct point){.x = x, .y = y}

val mk_point (x y: pod int): point

/// PCM lenses for the fields of a point

val _x : pcm_lens point_pcm (pod_pcm int)
val _y : pcm_lens point_pcm (pod_pcm int)

(*
/// Laws relating _x, _y, and mk_point

val point_put_x (x' x y: pod int)
: Lemma (put _x x' (mk_point x y) == mk_point x' y)
  [SMTPat (put _x x' (mk_point x y))]

val point_get_x (x y: pod int)
: Lemma (get _x (mk_point x y) == x)
  [SMTPat (get _x (mk_point x y))]

val point_put_y (y' x y: pod int)
: Lemma (put _y y' (mk_point x y) == mk_point x y')
  [SMTPat (put _y y' (mk_point x y))]

val point_get_y (x y: pod int)
: Lemma (get _y (mk_point x y) == y)
  [SMTPat (get _y (mk_point x y))]

/// Laws relating mk_point to PCM operations

val point_one : squash (one point_pcm == mk_point none none)

val point_op (x y x' y': pod int)
: Lemma
    (requires composable (pod_pcm int) x x' /\ composable (pod_pcm int) y y')
    (ensures composable point_pcm (mk_point x y) (mk_point x' y') /\
     op point_pcm (mk_point x y) (mk_point x' y') == mk_point (op (pod_pcm int) x x') (op (pod_pcm int) y y'))
  [SMTPat (op point_pcm (mk_point x y) (mk_point x' y'))]
*)

/// Taking pointers to the x and y fields of a point

val addr_of_x (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased (pod int))
: SteelT (q:ref 'a (pod int){q == ref_focus p (pod_pcm int) _x})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point none y) `star`
       (q `pts_to` x))

val un_addr_of_x
  (p: ref 'a point{p.q == point_pcm})
  (q: ref 'a (pod int){q == ref_focus p (pod_pcm int) _x})
  (x y: Ghost.erased (pod int))
: SteelT unit
    ((p `pts_to` mk_point none y) `star` (q `pts_to` x))
    (fun q -> p `pts_to` mk_point x y)

val addr_of_y (p: ref 'a point{p.q == point_pcm}) (x y: Ghost.erased (pod int))
: SteelT (q:ref 'a (pod int){q == ref_focus p (pod_pcm int) _y})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point x none) `star`
       (q `pts_to` y))

val un_addr_of_y
  (p: ref 'a point{p.q == point_pcm})
  (q: ref 'a (pod int){q == ref_focus p (pod_pcm int) _y})
  (x y: Ghost.erased (pod int))
: SteelT unit
    ((p `pts_to` mk_point x none) `star` (q `pts_to` y))
    (fun q -> p `pts_to` mk_point x y)
