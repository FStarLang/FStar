
module Interpreter

open SGXState
open FStar.Array
open FStar.UInt64
open FStar.List
open Ast

exception Halt

let u64 = UInt64.t

val defensive: (array u64) -> (array u64) ->nat-> nat-> sgxstate
let defensive regs buf base size = 
  let read' (regname:string) = 
       0uL
    in
  let write' (regname:string) (value:u64) = 
       ()
    in
  let load' (n:nat) (addr:nat) = 
       Array.index buf (addr-base) 
    in
  let store' (n:nat) (v:u64) (addr:nat) =
        Array.upd buf (addr-base) v  
    in
   Mksgxstate read' write' load' store'
	


val eval: sgxstate -> exp -> u64
let eval (env:sgxstate) = function
 | Register r -> env.read r 
 | Constant n -> 0uL

let step (env:sgxstate) = function 
  | Skip -> ()
  | Store(n, ea, ev)-> 
       let a = eval env ea in
       let v = eval env ev in 
       env.store n v 0

let steps (env:sgxstate) instr = List.iter (fun elem->step env elem ) instr  

val ustar:(array u64)->(array u64) -> nat ->unit->unit
let ustar regs buf base entry = 
  let size = 1000 in
  let mem = defensive regs buf base size in
  steps mem [(Store(1,(Register "rax"),(Register "rcx")))] 
