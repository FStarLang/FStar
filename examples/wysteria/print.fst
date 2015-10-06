(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi FStar.IO --admit_fsi Prins;
    other-files:ghost.fst ordset.fsi ordmap.fsi set.fsi heap.fst st.fst all.fst io.fsti prins.fsi ast.fst
 --*)

module Print

open AST
open FStar.IO

val print_term: term -> unit
let print_term = print_any
