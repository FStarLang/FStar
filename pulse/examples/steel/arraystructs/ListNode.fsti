module ListNode

open Steel.Effect
open PointStruct
open Steel.C.PCM
open Steel.C.Opt
open Steel.C.Ptr
open Steel.C.Ref
open Steel.C.Connection
module U = FStar.Universe

/// struct node { int value; struct node *next; };

val node: Type u#0

/// PCM for node:

val node_pcm: pcm node

/// (mk_node value next) represents (struct node){.value = value, .next = next}

val mk_node
  (i: option int)
  (next: option (ptr node node))
: node

// val mk_node_tot
//   (i: option int)
//   (next: option (ptr node node))
// : node

// val mk_node_tot_mk_node (i: option int) (next: option (ptr node node))
// : Lemma (mk_node_tot i next == Ghost.reveal (mk_node i next))
//   [SMTPat (mk_node_tot i next)]

open Steel.C.PCM
module P = FStar.PCM

val mk_node_refine (i: option int) (next: option (ptr node node))
: Lemma
    (requires p_refine opt_pcm i /\ p_refine (opt_pcm) next)
    (ensures p_refine node_pcm (mk_node i next))
    [SMTPat (p_refine node_pcm (mk_node i next))]

/// Connections for fields

val _value: node_pcm `connection` opt_pcm #int
val _next: node_pcm `connection` opt_pcm #(ptr node node)

/// Taking pointers to the fields of a node

val addr_of_value
  (#value:Ghost.erased (option int))
  (#next:Ghost.erased (option (ptr node node)))
  (p: ref 'a node_pcm)
: Steel (ref 'a (opt_pcm #int))
    (p `pts_to` mk_node value next)
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
