module CherryTree
module U32 = FStar.UInt32

type tree =
  | Leaf
  | Node of tree & U32.t & tree

let rec insert (x: U32.t) (t: tree) : tree =
  match t with
  | Leaf -> Node (Leaf, x, Leaf)
  | Node (l, y, r) ->
    if U32.lt x y then Node (insert x l, y, r)
    else if U32.gt x y then Node (l, y, insert x r)
    else t

let rec size (t: tree) : U32.t =
  match t with
  | Leaf -> 0ul
  | Node (l, _, r) -> U32.add_mod (size l) (U32.add_mod 1ul (size r))

let rec tsum (t: tree) : U32.t =
  match t with
  | Leaf -> 0ul
  | Node (l, x, r) -> U32.add_mod (tsum l) (U32.add_mod x (tsum r))

let rec mem (x: U32.t) (t: tree) : bool =
  match t with
  | Leaf -> false
  | Node (l, y, r) -> if U32.lt x y then mem x l else if U32.gt x y then mem x r else true

let rec build (n: U32.t) (t: tree) : Tot tree (decreases U32.v n) =
  if n = 0ul then t
  else build (U32.sub n 1ul) (insert (U32.rem (U32.mul_mod n 7ul) 31ul) t)

let main () : U32.t =
  let t = build 40ul Leaf in
  let t2 = insert 100ul t in
  if size t = 31ul && size t2 = 32ul && mem 100ul t2 && not (mem 100ul t)
     && tsum t2 = U32.add_mod (tsum t) 100ul
  then 0ul else 1ul
