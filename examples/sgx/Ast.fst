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
 |Store of u64*exp * exp
 |Assign of exp * exp
 |Load of exp * u64* exp
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
 |LowStore of u64*lowexp * lowexp
 |LowAssign of lowexp * lowexp
 |LowLoad of lowexp * u64*lowexp
 |LowSeq of (list lowstmt)
 |LowIf of lowexp * (list lowstmt) * (list lowstmt)
 |LowJump of lowexp
 |LowCall of lowexp
 |LowSkip 
 |LowAssert

type lowprogram = lowstmt

type lowsgxmem = 
| LowRegister of string
(* Commenting this. Need more granularity to reason about invariants
| LowMemory of u64 
*)
| BitMapRange of u64
| UHeapRange of u64
| UStackRange of u64
(* Should we encode callbitmap here?
| CallBitmap of u64
*)

