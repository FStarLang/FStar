module Mutual

(* Section 6, pass 8.  The extraction loop emits a definition once it has
   finished translating it, which orders an acyclic program correctly but says
   nothing about a cycle; the SCC pass has to find the cycles and group them.
   Both a type cycle and a function cycle are exercised, since OCaml needs
   'and' for each. *)

noeq type tree =
  | Node : int -> forest -> tree
and forest =
  | Nil : forest
  | Cons : tree -> forest -> forest

let rec size_t (t:tree) : Tot int (decreases t) =
  match t with | Node _ f -> 1 + size_f f
and size_f (f:forest) : Tot int (decreases f) =
  match f with | Nil -> 0 | Cons t r -> size_t t + size_f r

(* A three-way cycle, to check that the group is not just a pair, and that a
   member reached only from inside the cycle still comes out in the group. *)
let rec a (n:nat) : Tot nat (decreases n) = if n = 0 then 0 else 1 + b (n - 1)
and b (n:nat) : Tot nat (decreases n) = if n = 0 then 0 else 2 + c (n - 1)
and c (n:nat) : Tot nat (decreases n) = if n = 0 then 0 else 3 + a (n - 1)

let t0 = Node 1 (Cons (Node 2 Nil) (Cons (Node 3 Nil) Nil))


(* Two specializations of the same mutually recursive pair.  Each must form
   its own component: the cycle is between ping@int and pong@int, and between
   ping@bool and pong@bool, never across. *)
class shower (a:Type) = { sh : a -> string }
instance _ : shower int = { sh = string_of_int }
instance _ : shower bool = { sh = (fun b -> if b then "t" else "f") }

let rec ping (#a:Type) {| shower a |} (n:nat) (x:a)
  : Tot string (decreases (2*n+1)) =
  if n = 0 then sh x else pong #a n x
and pong (#a:Type) {| shower a |} (n:nat) (x:a)
  : Tot string (decreases (2*n)) =
  if n = 0 then "" else ping #a (n - 1) x

let main () =
  FStar.IO.print_string (string_of_int (size_t t0) ^ " " ^
                         string_of_int (a 6) ^ " " ^
                         ping #int 3 7 ^ ping #bool 2 true ^ "\n")
