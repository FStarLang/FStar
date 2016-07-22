
module Interpreter

open SGXState
open FStar.Array
open FStar.UInt64
open FStar.List
open Util
open Ast

exception Halt

let u64 = UInt64.t

(*
val STX.Halt: unit -> STX 'a 
val STX.Load : unit -> buffer ... -> STX word
val STX.Store: unit -> buffer ... -> STX unit
*)

val defensive: (array u64) -> (array u64) ->nat-> nat->nat->nat->nat->nat-> sgxstate
let defensive regs buf base wbmapstart uheapstart ustackstart ucodestart size = 
  let read' (regname:string) = 
       (* What should regs structure be? *)
       0uL
    in
  let write' (regname:string) (value:u64) = 
       ()
    in
  let load' (n:nat) (addr:nat) = 
       Array.index buf (addr-base) 
    in
  let store' (n:nat) (v:u64) (addr:nat) =
     if addr > wbmapstart && addr < uheapstart then
	(* addr is in write-bitmap, get the index
	   i.e. bitmapindex represents the address whose permission
	   is being toggled 
	*)
	let bitmapindex = get_address_represented_in_bitmap base wbmapstart addr in 
	
	(* Check that bitmapindex belongs to current stack frame. Steps:
	  1. Read rbp register which contains current frame pointer
	  2. Check that 'bitmapindex' is less than [|rbp |] 
	*)
	let currentframestart = cast_to_nat (read' "rbp") in
	if (bitmapindex < currentframestart) then	
        	Array.upd buf (addr-base) v
	else
		raise Halt
    else if addr >uheapstart && addr < ustackstart then
	(* In Progress: Do necessary checks here.. *)  
	()
    in
   Mksgxstate read' write' load' store'
	
(* Should look into the call table from manifest and fetch the corresponding function
 *)
let decode insaddr = [Skip]

let get_register_name = function
 | Register r -> r
 | _ -> raise Halt

val eval: sgxstate -> exp -> u64
let eval (env:sgxstate) = function
 | Register r -> env.read r 
 | Constant n -> n

val step : sgxstate -> stmt -> unit
val steps : sgxstate -> (list stmt) -> unit

let rec step (env:sgxstate) = function 
  | Skip -> ()
  | Store(n, ea, ev)-> 
       let a = eval env ea in
       let v = eval env ev in 
       env.store (cast_to_nat n) v (cast_to_nat a)
  | Load (reg, n, ea) ->
       let a = eval env ea in
       let value = env.load (cast_to_nat n) (cast_to_nat a) in
       let regname = get_register_name reg in
       env.write regname value
  | Call e ->
       let fentry = eval env e in
	(* Convert this to sequence of instructions *)
	steps env (decode fentry)

and steps (env:sgxstate) instr = List.iter (fun elem->step env elem ) instr  

val ustar:(array u64)->(array u64)-> nat ->nat->nat->nat->nat->unit->unit
let ustar regs buf base wbmapstart uheapstart ustackstart ucodestart entry = 
  let size = 1000 in
  let mem = defensive regs buf base wbmapstart uheapstart ustackstart ucodestart size in
  steps mem [(Store(1uL,(Register "rax"),(Register "rcx")))] 
