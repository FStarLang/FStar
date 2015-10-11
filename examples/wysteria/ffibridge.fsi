(*--build-config
   options:--admit_fsi FStar.OrdSet --admit_fsi FStar.OrdMap --admit_fsi Prins;
   other-files:ordset.fsi ordmap.fsi ghost.fst prins.fsi ast.fst
--*)

module Ffibridge

open AST

val exec_ffi: nat -> 'a -> list dvalue -> 'b -> Tot dvalue

val verified_eq: x:'a -> y:'a -> Tot (r:bool{r <==> x = y})
