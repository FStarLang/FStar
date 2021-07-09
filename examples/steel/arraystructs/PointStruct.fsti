module PointStruct

open AggregateRef
open FStar.PCM.POD
open FStar.PCM
open FStar.PCM.Extras
open Steel.Effect

/// Suppose we have the following struct representing 2d points:
///   struct point { int x, y; };
///
/// Carrier of PCM for struct point:

val point : Type0

/// PCM for struct point:

val point_pcm : refined_one_pcm point

/// (mk_point x y) represents (struct point){.x = x, .y = y}

val mk_point (x y: Ghost.erased (pod int)): Ghost.erased point

/// PCM lenses for the fields of a point

val _x : pcm_lens point_pcm (pod_pcm int)
val _y : pcm_lens point_pcm (pod_pcm int)

/// Taking pointers to the x and y fields of a point

val addr_of_x (#x #y: Ghost.erased (pod int)) (p: ref 'a point_pcm)
: SteelT (q:ref 'a (pod_pcm int){q == ref_focus p _x})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point none y) `star`
       (q `pts_to` x))

val unaddr_of_x
  (#x #y: Ghost.erased (pod int))
  (p: ref 'a point_pcm)
  (q: ref 'a (pod_pcm int){q == ref_focus p _x})
: SteelT unit
    ((p `pts_to` mk_point none y) `star` (q `pts_to` x))
    (fun q -> p `pts_to` mk_point x y)

val addr_of_y (#x #y: Ghost.erased (pod int)) (p: ref 'a point_pcm)
: SteelT (q:ref 'a (pod_pcm int){q == ref_focus p _y})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point x none) `star`
       (q `pts_to` y))

val unaddr_of_y
  (#x #y: Ghost.erased (pod int))
  (p: ref 'a point_pcm)
  (q: ref 'a (pod_pcm int){q == ref_focus p _y})
: SteelT unit
    ((p `pts_to` mk_point x none) `star` (q `pts_to` y))
    (fun q -> p `pts_to` mk_point x y)
