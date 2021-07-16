module ListExampleOOM

open Steel.C.PCM
open Steel.C.Ref

open Steel.Effect
module A = Steel.Effect.Atomic

open FStar.PCM.POD
open ListNodeOOM

(*
let ok
  (#value:Ghost.erased (pod int'))
  (#next:Ghost.erased (pod (option (ref' node node))))
  (p: ref 'a node_pcm)
: SteelT (q:ref 'a (pod_pcm int'){q == ref_focus p _value})
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node none next) `star`
       (q `pts_to` value))
= addr_of_value #'a #value #next p
*)

let oom
  (#value:Ghost.erased (pod int'))
  (#next:Ghost.erased (pod (option (ref' node node))))
  (p: ref 'a node_pcm)
: SteelT (q:ref 'a (pod_pcm (option (ref' node node))){q == ref_focus p _next})
    (p `pts_to` mk_node value next)
    (fun q ->
       (p `pts_to` mk_node value none) `star`
       (q `pts_to` next))
= addr_of_next #'a #value #next p
