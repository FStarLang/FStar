(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins;
    other-files:FStar.Ghost.fst ordset.fsi ordmap.fsi prins.fsi ast.fst
 --*)

module Prog

open AST

val program:exp
