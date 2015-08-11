(*--build-config
   options:--admit_fsi OrdSet --admit_fsi OrdMap;
   variables:LIB=../../lib;
   other-files:$LIB/ordset.fsi $LIB/ordmap.fsi ast.fst
--*)

module FFI

open AST

val exec_ffi: string -> list dvalue -> Tot dvalue
