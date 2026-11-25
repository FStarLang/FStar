module CherryEtaAtomic
open FStar.All
module U32 = FStar.UInt32

noeq type node =
  | Leaf : int -> node
  | Node { tm:node; s:list int & bool }

noeq type cell = { n:node; k:int; memo:ref int }

let mk_node (n:node) (k:int) : ML cell = { n; k; memo = alloc 0 }

(* The argument of [mk_node] is not an atom, so this keeps both binders
   rather than being reduced to [fun p -> mk_node (Node ..)], which nothing
   expands back, since that body computes: every call would build a partial
   application of [mk_node] and then apply it. *)
let wrap (p:node & (list int & bool)) (k:int) : ML cell =
  mk_node (Node {tm=fst p; s=snd p}) k

let main () : ML U32.t =
  match (wrap (Leaf 1, ([3], true)) 2).n with
  | Node {tm=Leaf 1; s=([3], true)} -> 0ul
  | _ -> 1ul
