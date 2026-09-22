module RecEffect
open FStar.All

type tree =
  | Leaf : int -> tree
  | Node : tree -> tree -> tree

(* Section 7.3 deletes a discarded pure subterm.  The first call here is
   discarded -- it returns [unit] and its value is thrown away -- so whether it
   survives depends entirely on the effect Custard assigns to a call into the
   recursion it is part of.  Read pure, the left subtree is never printed. *)
let rec walk (t: tree) : ML unit =
  match t with
  | Leaf n -> FStar.IO.print_string (string_of_int n)
  | Node l r -> walk l; walk r

(* The same, between two members of a mutually recursive group: each is
   reached through a request of its own, so neither is available when the
   other's body is extracted. *)
let rec walk_l (t: tree) : ML unit =
  match t with
  | Leaf n -> FStar.IO.print_string (string_of_int n)
  | Node l r -> walk_r l; walk_r r
and walk_r (t: tree) : ML unit =
  match t with
  | Leaf n -> FStar.IO.print_string (string_of_int (n + 10))
  | Node l r -> walk_l l; walk_l r

(* And in a local [let rec], which is lambda-lifted into a group of its own. *)
let walk_local (t: tree) : ML unit =
  let rec go (t: tree) : ML unit =
    match t with
    | Leaf n -> FStar.IO.print_string (string_of_int (n * 2))
    | Node l r -> go l; go r
  in
  go t

let t : tree = Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)

let main () : ML unit =
  walk t;
  FStar.IO.print_string " ";
  walk_l t;
  FStar.IO.print_string " ";
  walk_local t;
  FStar.IO.print_string "\n"
