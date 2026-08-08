(* Type monomorphization (section 5.0).

   Under --custard_monomorphize_types every polymorphic *type* declaration is
   replaced by one declaration per instantiation, so that the output contains
   no type variable at all.  What has to hold afterwards:

     - two instantiations of one type are two declarations, and their
       constructors are distinguishable, so a value of one cannot be confused
       with a value of the other;
     - a nested instantiation (list (list int)) works, which is what needs the
       worklist rather than a single sweep;
     - a type abbreviation is not an instantiation of its own: 'pair_of_ints'
       and 'both int' have to end up as the same declaration, and so do 'nat'
       and 'int'. *)
module MonoTypes

open FStar.All
open FStar.List.Tot

type both a = { fst : a; snd : a }

type tree a =
  | Leaf
  | Node of tree a & a & tree a

let pair_of_ints = both int

let mk (#a:Type) (x:a) (y:a) : both a = { fst = x; snd = y }

let swap (#a:Type) (p:both a) : both a = { fst = p.snd; snd = p.fst }

let rec size (#a:Type) (t:tree a) : nat =
  match t with
  | Leaf -> 0
  | Node (l, _, r) -> 1 + size l + size r

let rec flatten (#a:Type) (t:tree a) : list a =
  match t with
  | Leaf -> []
  | Node (l, x, r) -> flatten l @ (x :: flatten r)

let leaves (#a:Type) (x:a) (y:a) : tree a =
  Node (Node (Leaf, x, Leaf), y, Leaf)

(* A nested instantiation: the outer list is asked for only once the inner one
   has a name. *)
let nested : list (list int) = [[1; 2]; [3]]

let rec sum_all (xss : list (list int)) : int =
  match xss with
  | [] -> 0
  | xs :: rest -> fold_left (fun a b -> a + b) 0 xs + sum_all rest

(* 'pair_of_ints' is an abbreviation, so this must reuse the declaration that
   'mk 1 2' below asks for rather than making a second one. *)
let via_abbrev (p : pair_of_ints) : int = p.fst + p.snd

(* Written out rather than calling FStar.String.concat, whose OCaml
   realization is polymorphic and would therefore freeze 'list' (section
   5.0). *)
let rec join (xs : list string) : string =
  match xs with
  | [] -> ""
  | x :: rest -> x ^ join rest

let main () : ML unit =
  let ints = swap (mk 1 2) in
  let bools = swap (mk true false) in
  FStar.IO.print_string (string_of_int ints.fst);
  FStar.IO.print_string (if bools.fst then "T" else "F");
  FStar.IO.print_string (string_of_int (via_abbrev (mk 10 20)));
  FStar.IO.print_string (string_of_int (size (leaves 1 2)));
  FStar.IO.print_string (string_of_int (size (leaves "a" "b")));
  FStar.IO.print_string (join (flatten (leaves "x" "y")));
  FStar.IO.print_string (string_of_int (sum_all nested));
  FStar.IO.print_string "\n"
