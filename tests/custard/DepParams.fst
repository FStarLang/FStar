module DepParams
open FStar.All
open FStar.IO

class printable (a:Type) = { pr : a -> string }

instance p_int : printable int = { pr = string_of_int }

(* An inductive whose parameter list is dependent: the dictionary's sort
   mentions the [a] bound just before it.  [Sig_inductive_typ] stores its
   parameters closed, so that mention is a de Bruijn index until extraction
   opens them -- and every parameter sort is inspected, to decide which
   parameters are type parameters of the emitted type. *)
noeq type labelled (a:Type) {| printable a |} = { tag: string; value: a }

let render (#a:Type) {| printable a |} (l : labelled a) : string =
  l.tag ^ "=" ^ pr l.value

let main () : ML unit =
  print_string (render ({ tag = "x"; value = 42 }) ^ "\n")
