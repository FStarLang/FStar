module ListNode

open FStar.PCM
open Steel.Effect
open PointStruct
open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Ref
open Steel.C.Connection
module U = FStar.Universe

let ref'_f a b (pb: Ghost.erased (pcm b)) = ref a (Ghost.reveal pb)
let ref' a b = dtuple2 (Ghost.erased (pcm b)) (ref'_f a b)

let int': Type u#1 = U.raise_t int

/// struct node { int value; struct node *next; };

val node: Type u#1

/// PCM for node:

val node_pcm: pcm node

/// (mk_node value next) represents (struct node){.value = value, .next = next}

val mk_node
  (i: Ghost.erased (option int'))
  (next: Ghost.erased (option (option (ref' node node))))
: Ghost.erased node

/// Lenses for fields

val _value: node_pcm `connection` opt_pcm #int'
val _next: node_pcm `connection` opt_pcm #(option (ref' node node))

/// Taking pointers to the fields of a node

val addr_of_value
  (#value:Ghost.erased (option int'))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
: SteelT (q:ref 'a (opt_pcm #int'){q == ref_focus p _value})
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node none next) `star`
       (q `pts_to` value))

val unaddr_of_value
  (#value:Ghost.erased (option int'))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
  (q: ref 'a (opt_pcm #int'){q == ref_focus p _value})
: SteelT unit
    ((p `pts_to` mk_node none next) `star` (q `pts_to` value))
    (fun q -> p `pts_to` mk_node value next)

val addr_of_next
  (#value:Ghost.erased (option int'))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
: SteelT (q:ref 'a (opt_pcm #(option (ref' node node))){q == ref_focus p _next})
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node value none) `star`
       (q `pts_to` next))

val unaddr_of_next
  (#value:Ghost.erased (option int'))
  (#next:Ghost.erased (option (option (ref' node node))))
  (p: ref 'a node_pcm)
  (q: ref 'a (opt_pcm #(option (ref' node node))){q == ref_focus p _next})
: SteelT unit
    ((p `pts_to` mk_node value none) `star` (q `pts_to` next))
    (fun q -> p `pts_to` mk_node value next)
