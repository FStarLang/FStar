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

val mk_point (x y: Ghost.erased (option int)): Ghost.erased point

/// Connections for the fields of a point

val _x : connection point_pcm (opt_pcm #int)
val _y : connection point_pcm (opt_pcm #int)

/// Taking pointers to the x and y fields of a point

val addr_of_x (#x #y: Ghost.erased (option int)) (p: ref 'a point_pcm)
: SteelT (q:ref 'a (opt_pcm #int){q == ref_focus p _x})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point none y) `star`
       (q `pts_to` x))

val unaddr_of_x
  (#x #y: Ghost.erased (option int))
  (p: ref 'a point_pcm)
  (q: ref 'a (opt_pcm #int){q == ref_focus p _x})
: SteelT unit
    ((p `pts_to` mk_point none y) `star` (q `pts_to` x))
    (fun q -> p `pts_to` mk_point x y)

val addr_of_y (#x #y: Ghost.erased (option int)) (p: ref 'a point_pcm)
: SteelT (q:ref 'a (opt_pcm #int){q == ref_focus p _y})
    (p `pts_to` mk_point x y)
    (fun q ->
       (p `pts_to` mk_point x none) `star`
       (q `pts_to` y))

val unaddr_of_y
  (#x #y: Ghost.erased (option int))
  (p: ref 'a point_pcm)
  (q: ref 'a (opt_pcm #int){q == ref_focus p _y})
: SteelT unit
    ((p `pts_to` mk_point x none) `star` (q `pts_to` y))
    (fun q -> p `pts_to` mk_point x y)

/// Views

// let point_view excluded : sel_view point_pcm (k:field_name not in excluded -> fields k)
// = {
//   to_view_prop = (fun x -> Some? x == true);
//   to_view = (fun x -> Some?.v x);
//   to_carrier = (fun z  -> Some z);
//   to_carrier_not_one = (fun _ -> ());
//   to_view_frame = (fun x frame -> ());
// }

// val node_view: sel_view node_pcm _ false

(*
val addr_of_value_sel (p: ref 'a node_pcm)
: Steel (ref 'a (opt_pcm #int))
    (p `pts_to_view` node_view)
    (fun q ->
       (p `pts_to` mk_node none next) `star`
       (q `pts_to` value))
    (requires (fun _ -> True))
    (ensures (fun _ q _ -> q == ref_focus p _value))

val unaddr_of_value
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (ptr node node)))
  (p: ref 'a node_pcm)
  (q: ref 'a (opt_pcm #int))
: Steel unit
    ((p `pts_to` mk_node none next) `star` (q `pts_to` value))
    (fun q -> p `pts_to` mk_node value next)
    (requires (fun _ -> q == ref_focus p _value))
    (ensures (fun _ _ _ -> True))

val addr_of_next
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (ptr node node)))
  (p: ref 'a node_pcm)
: Steel (ref 'a (opt_pcm #(ptr node node)))
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node value none) `star`
       (q `pts_to` next))
    (requires (fun _ -> True))
    (ensures (fun _ q _ -> q == ref_focus p _next))

val unaddr_of_next
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (ptr node node)))
  (p: ref 'a node_pcm)
  (q: ref 'a (opt_pcm #(ptr node node)))
: Steel unit
    ((p `pts_to` mk_node value none) `star` (q `pts_to` next))
    (fun q -> p `pts_to` mk_node value next)
    (requires (fun _ -> q == ref_focus p _next))
    (ensures (fun _ _ _ -> True))
*)
