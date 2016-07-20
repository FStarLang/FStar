module Ast

open FStar.UInt32
open FStar.UInt64

open Helper

let u32 = UInt32.t
let u64 = UInt64.t

type exp =
 |Reg of string
 |Constant of u64

type stmt = 
 |Store of exp * exp
 |Assign of exp * exp
 |Load of exp * exp
 |Seq of (list stmt)
 |If of exp * (list stmt) * (list stmt)
 |Jump of exp
 |Call of exp
 |Skip 
 |Assert

type program = stmt

type sgxmem = 
| Register of string
| Memory of u64

val lookup: (sgxmem->u64)->sgxmem -> u64
val extend: (sgxmem -> u64)->sgxmem->u64 ->(sgxmem->u64)
