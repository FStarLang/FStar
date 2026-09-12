module CRecType
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* Section 17.3: a type that reaches itself, or reaches a type declared later,
   *through a pointer*.  A C struct cannot contain itself by value and Custard
   rejects that outright, but this is ordinary C -- and it used to be emitted
   as an anonymous [typedef struct { ... } t;], whose fields therefore named
   [t] before [t] existed.  Every struct now carries a tag, and every tag is
   forward-declared before any type is defined.

   Three shapes, because the anonymous typedef broke them in three different
   ways: a variant reaching itself through a record declared *after* it,
   mutual recursion between a record and a variant, and a variant reaching
   itself directly. *)

noeq type tree =
  | Leaf : U32.t -> tree
  | Node : node -> tree

and node = { left : ref tree; right : ref tree }

noeq type ping = { p_n : U32.t; p_next : ref pong }
and pong =
  | PEnd
  | PMore : ref ping -> pong

noeq type chain =
  | Stop
  | Link : U32.t -> ref chain -> chain

let rec sum_chain (c : chain) : ML U32.t =
  match c with
  | Stop -> 0ul
  | Link n r -> U32.add_mod n (sum_chain !r)

let leaf_val (t : tree) : ML U32.t =
  match t with
  | Leaf b -> b
  | Node _ -> 0ul

let root (t : tree) : ML U32.t =
  match t with
  | Leaf b -> b
  | Node n -> U32.add_mod (leaf_val !(n.left)) (leaf_val !(n.right))

let walk (p : ping) : ML U32.t =
  U32.add_mod p.p_n (match !(p.p_next) with
                     | PEnd -> 8ul
                     | PMore _ -> 0ul)

let main () : ML I32.t =
  let t = Node ({ left = alloc (Leaf 3ul); right = alloc (Leaf 4ul) }) in
  let c = Link 5ul (alloc (Link 6ul (alloc Stop))) in
  let p = { p_n = 7ul; p_next = alloc PEnd } in
  if U32.eq (root t) 7ul && U32.eq (sum_chain c) 11ul && U32.eq (walk p) 15ul
  then 0l else 1l
