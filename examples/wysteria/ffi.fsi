(*--build-config
   options:--admit_fsi OrdSet --admit_fsi OrdMap;
   other-files:ordset.fsi ordmap.fsi ast.fst
--*)

module FFI

open AST

val exec_ffi: string -> list dvalue -> Tot dvalue
