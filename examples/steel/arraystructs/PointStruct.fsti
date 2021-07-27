module PointStruct

open FStar.PCM
open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Ref
open Steel.C.Connection
open Steel.Effect

/// Suppose we have the following struct representing 2d points:
///   struct point { int x, y; };
///
/// Carrier of PCM for struct point:

type point_field = | X | Y

val point : Type0

/// PCM for struct point:

val point_pcm : pcm point

/// (mk_point x y) represents (struct point){.x = x, .y = y}

val mk_point (x y: option int): point

/// Connections for the fields of a point

val _x : connection point_pcm (opt_pcm #int)
val _y : connection point_pcm (opt_pcm #int)

/// Taking pointers to the x and y fields of a point

val addr_of_x (#x #y: Ghost.erased (option int)) (p: ref 'a point_pcm)
: Steel (ref 'a (opt_pcm #int))
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point None y) `star`
       (q `pts_to` x))
    (requires fun _ -> True)
    (ensures fun _ q _ -> q == ref_focus p _x)

val unaddr_of_x
  (#x #y: Ghost.erased (option int))
  (p: ref 'a point_pcm)
  (q: ref 'a (opt_pcm #int))
: Steel unit
    ((p `pts_to` mk_point None y) `star` (q `pts_to` x))
    (fun q -> p `pts_to` mk_point x y)
    (requires fun _ -> q == ref_focus p _x)
    (ensures fun _ _ _ -> True)

val addr_of_y (#x #y: Ghost.erased (option int)) (p: ref 'a point_pcm)
: Steel (ref 'a (opt_pcm #int))
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point x None) `star`
       (q `pts_to` y))
    (requires fun _ -> True)
    (ensures fun _ q _ -> q == ref_focus p _y)

val unaddr_of_y
  (#x #y: Ghost.erased (option int))
  (p: ref 'a point_pcm)
  (q: ref 'a (opt_pcm #int))
: Steel unit
    ((p `pts_to` mk_point x None) `star` (q `pts_to` y))
    (fun q -> p `pts_to` mk_point x y)
    (requires fun _ -> q == ref_focus p _y)
    (ensures fun _ _ _ -> True)

