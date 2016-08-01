module Ast

open FStar.UInt32
open FStar.UInt64

exception Halt
let u32 = UInt32.t
let u64 = UInt64.t

type exp =
 |Register of string
 |Constant of u64

type stmt = 
 |Store of u64*exp * exp
 |Assign of exp * exp
 |Load of exp * u64* exp
 |Seq of (list stmt)
 |If of exp * (list stmt) * (list stmt)
 |Jump of exp
 |Call of exp
 |Skip 
 |Assert
 |Return

type lambda = string * stmt
type program = list lambda

