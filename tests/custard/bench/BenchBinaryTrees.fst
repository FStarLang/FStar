module BenchBinaryTrees
(* The Benchmarks Game's binary-trees: many short-lived complete trees, and
   one long-lived one alongside. *)
module U32 = FStar.UInt32

type tree = | Nil | Node of tree & tree

let rec make (d: int) : Tot tree (decreases (if d <= 0 then 0 else d)) =
  if d <= 0 then Node (Nil, Nil) else Node (make (d - 1), make (d - 1))

let rec check (t: tree) : int =
  match t with Nil -> 0 | Node (l, r) -> 1 + check l + check r

let rec pow2 (n: int) : Tot int (decreases (if n <= 0 then 0 else n)) =
  if n <= 0 then 1 else 2 * pow2 (n - 1)

let rec iter (i: int) (d: int) (acc: int) : Tot int (decreases (if i <= 0 then 0 else i)) =
  if i <= 0 then acc else iter (i - 1) d (acc + check (make d))

let min_depth = 4
let max_depth = 20

(* Depths min_depth, min_depth + 2, ..., up to max_depth. *)
let rec depths (k: int) (acc: int) : Tot int (decreases (if k <= 0 then 0 else k)) =
  if k <= 0 then acc else
  let d = min_depth + 2 * (k - 1) in
  depths (k - 1) (acc + iter (pow2 (max_depth - d + min_depth)) d 0)

let main () : U32.t =
  let stretch = check (make (max_depth + 1)) in
  let long_lived = make max_depth in
  let s = depths ((max_depth - min_depth) / 2 + 1) 0 in
  if stretch = 4194303 && s = 300591792 && check long_lived = 2097151 then 0ul else 1ul
