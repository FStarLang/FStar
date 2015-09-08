(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi FStar.IO;
    variables:LIB=../../lib;
    other-files:$LIB/ordset.fsi $LIB/ordmap.fsi $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/io.fsti ast.fst
 --*)

module Print

open AST
open FStar.IO

val print_term: term -> unit
let print_term = print_any
