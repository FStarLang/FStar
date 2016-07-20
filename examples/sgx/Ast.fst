module Ast

open FStar.UInt32
open FStar.UInt64

open Helper

exception Halt
let u32 = UInt32.t
let u64 = UInt64.t

type exp =
 |RegExp of string
 |ConstantExp of u64

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


type lowexp =
 |LowVarExp of string
 |LowConstantExp of u64
 |LowMemExp of u64

type lowstmt = 
 |LowStore of lowexp * lowexp
 |LowAssign of lowexp * lowexp
 |LowLoad of lowexp * lowexp
 |LowSeq of (list lowstmt)
 |LowIf of lowexp * (list lowstmt) * (list lowstmt)
 |LowJump of lowexp
 |LowCall of lowexp
 |LowSkip 
 |LowAssert

type lowprogram = lowstmt

type lowsgxmem = 
| LowRegister of string
| LowMemory of u64

