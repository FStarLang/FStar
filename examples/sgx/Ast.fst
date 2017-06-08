module Ast

open FStar.UInt32
open FStar.UInt64

let u32 = UInt32.t
let u64 = UInt64.t

let address = UInt64.t
let dword = UInt64.t
let word = UInt32.t
let offset = UInt64.t


type exp =
 |Register of string
 |Constant of u64

(* All stmt have their corresponding address as first argument *)
type stmt = 
 |Add of u64 * exp * exp *exp
 |Sub of u64 * exp * exp *exp
 |Cmp of u64 * exp * exp * exp
 |Div	of u64 * exp * exp * exp
 |Mod of u64 * exp * exp * exp
 |Mul of u64 * exp * exp * exp
 |Lsr of u64 * exp * exp * exp
 |Lor of u64 * exp * exp * exp
 |Store of u64 * u64*exp * exp
 |Assign of  u64 * exp * exp
 |Push of  u64 * exp 
 |Pop of u64 * exp 
 |Load of u64 *exp * u64* exp
 |Seq of u64 * (list stmt)
 |If of  u64 * exp * stmt * stmt
 |Jump of u64 * exp
 |Call of u64 * exp
 |Skip of u64
 |Assert   (* Ghost *)
 |Return of u64

type lambda = string * stmt
type program = list lambda

type accesstype =
| Public
| Private

type argument =
| Mkintarg 
| Mkstringarg
 
(* 0x1000  foo [int;int..] public iswrapper? *)
type callentry =
 | MkCallentry : address -> string -> (list argument) -> accesstype ->bool-> callentry

type calltable =
 | MkCalltable : (list callentry) -> calltable 
