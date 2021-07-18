module ListNodeOOM

open Steel.Effect
open PointStruct
open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Ref
open Steel.C.Connection
module U = FStar.Universe

/// struct node { int value; struct node *next; };

val node: Type u#0

/// PCM for node:

val node_pcm: pcm node

/// (mk_node value next) represents (struct node){.value = value, .next = next}

val mk_node
  (i: Ghost.erased (option int))
  (next: Ghost.erased (option (option (ref' node node))))
: Ghost.erased node

/// Lenses for fields

val _value: node_pcm `connection` opt_pcm #int
val _next: node_pcm `connection` opt_pcm #(option (ref' node node))

/// Taking pointers to the fields of a node

val addr_of_value
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
: SteelT (q:ref 'a (opt_pcm #int){q == ref_focus p _value})
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node none next) `star`
       (q `pts_to` value))

val addr_of_next
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
: SteelT (q:ref 'a (opt_pcm #(option (ref' node node))){q == ref_focus p _next})
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node value none) `star`
       (q `pts_to` next))
