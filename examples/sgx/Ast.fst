module Ast

open FStar.UInt32
let u32 = UInt32.t

type exp =
 |Reg of string
 |Constant of u32
 |Function of string

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
