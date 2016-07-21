module Ast

open FStar.UInt32
open FStar.UInt64

exception Halt
let u32 = UInt32.t
let u64 = UInt64.t

type exp =
 |Register of string
 |Constant of nat

type stmt = 
 |Store of nat*exp * exp
 |Assign of exp * exp
 |Load of exp * nat* exp
 |Seq of (list stmt)
 |If of exp * (list stmt) * (list stmt)
 |Jump of exp
 |Call of exp
 |Skip 
 |Assert

type program = stmt

