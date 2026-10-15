module BenchRBMap
(* Red-black tree insertion (the Koka/Lean "rbmap" benchmark): a long-lived
   map built by a million functional inserts, mostly paths of fresh nodes
   whose old cells are garbage at once. *)
module U32 = FStar.UInt32

type color = | Red | Black
type rbt = | Leaf | Node of color & rbt & int & bool & rbt

let balance_l (l: rbt) (k: int) (v: bool) (r: rbt) : rbt =
  match l with
  | Node (Red, Node (Red, a, xk, xv, b), yk, yv, c) ->
    Node (Red, Node (Black, a, xk, xv, b), yk, yv, Node (Black, c, k, v, r))
  | Node (Red, a, xk, xv, Node (Red, b, yk, yv, c)) ->
    Node (Red, Node (Black, a, xk, xv, b), yk, yv, Node (Black, c, k, v, r))
  | _ -> Node (Black, l, k, v, r)

let balance_r (l: rbt) (k: int) (v: bool) (r: rbt) : rbt =
  match r with
  | Node (Red, Node (Red, b, yk, yv, c), zk, zv, d) ->
    Node (Red, Node (Black, l, k, v, b), yk, yv, Node (Black, c, zk, zv, d))
  | Node (Red, b, yk, yv, Node (Red, c, zk, zv, d)) ->
    Node (Red, Node (Black, l, k, v, b), yk, yv, Node (Black, c, zk, zv, d))
  | _ -> Node (Black, l, k, v, r)

let rec ins (t: rbt) (k: int) (v: bool) : rbt =
  match t with
  | Leaf -> Node (Red, Leaf, k, v, Leaf)
  | Node (Red, a, kx, vx, b) ->
    if k < kx then Node (Red, ins a k v, kx, vx, b)
    else if k = kx then Node (Red, a, k, v, b)
    else Node (Red, a, kx, vx, ins b k v)
  | Node (Black, a, kx, vx, b) ->
    if k < kx then balance_l (ins a k v) kx vx b
    else if k = kx then Node (Black, a, k, v, b)
    else balance_r a kx vx (ins b k v)

let insert (t: rbt) (k: int) (v: bool) : rbt =
  match ins t k v with
  | Node (Red, a, k, v, b) -> Node (Black, a, k, v, b)
  | t -> t

let rec mk (n: nat) (t: rbt) : Tot rbt (decreases n) =
  if n = 0 then t else mk (n - 1) (insert t (n - 1) ((n - 1) % 10 = 0))

let rec fold (t: rbt) (acc: int) : int =
  match t with
  | Leaf -> acc
  | Node (_, l, _, v, r) -> fold r (fold l (if v then acc + 1 else acc))

let main () : U32.t =
  let t = mk 1000000 Leaf in
  if fold t 0 = 100000 then 0ul else 1ul
