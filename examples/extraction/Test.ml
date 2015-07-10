
type nnat =
| O
| S of nnat

type 'a list =
| Nil
| Cons of 'a * 'a list

type ('a , 'b) list2 =
| Nil2
| Cons2 of 'a * 'b * ('a , 'b) list2

(*this is how the printer will print  MLTY_App (MLTY_Tuple nnat nnat) (MLTY_named list)*)
(* type hello = (nnat * nnat) list2 *)
(*OCaml rejects it*)

(*this is how the printer will print  MLTY_named [MLTY_named [] nnat, MLTY_named [] nnat] (list)*)
type hello = (nnat , nnat) list2
(*So, the special handling of application of inductive types in OCaml AST is a necessity, and not a redundancy*)