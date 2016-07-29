
module Interpreter

open SGXState
open FStar.Buffer
open FStar.UInt64
open FStar.List
open Util
open Ast

exception Halt

let word = UInt64.t
let address = UInt64.t

(*
val STX.Halt: unit -> STX 'a 
val STX.Load : unit -> buffer ... -> STX word
val STX.Store: unit -> buffer ... -> STX unit
*)

assume val search: (buffer word)->(addr:nat)-> bool

val defensive: (buffer word) -> (buffer word)->(buffer word) ->nat-> nat->nat->nat->nat->nat-> sgxstate
let defensive regs buf calltable base wbmapstart ucodestart uheapstart ustackstart size = 
  let read' (regname:string) = 
       (* What should regs structure be? *)
       0uL
    in
  let write' (regname:string) (value:word) = 
       ()
    in
  let load' (n:nat) (addr:nat) = 
       Buffer.index buf (addr-base)
    in
  let store' (n:nat) (v:word) (addr:nat) =
     if addr > wbmapstart && addr < ucodestart then
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
        	Buffer.upd buf (addr-base) v
	else
		raise Halt
    else if addr >uheapstart && addr < ustackstart then
	(* In Progress: Address is in UHeap.. *)  
	()
    else if addr >ustackstart && addr < (read' "rbp")  then
	(* In Progress: Address belongs to older stack frames *)  
	()
    else if addr >(read' "rbp") && addr < (read' "rsp")  then
	(* In Progress: Address belongs to current stack frame. Always ok *)  
	()
    in
  let iscallableaddress' (addr:nat) =
	let iscallable = search calltable addr in
	if iscallable then
		()
	else
		raise Halt
    in	
   Mksgxstate read' write' load' store' iscallableaddress'
	
(* Should look into the call table from manifest and fetch the corresponding function
 *)
let decode instraddr = [Skip]

let get_register_name = function
 | Register r -> r
 | _ -> raise Halt

val eval: sgxstate -> exp -> word
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
	(* Raises Exception if the function is not callable *)	
       let _ = env.iscallableaddress fentry in
	(* Convert this to sequence of instructions *)
	steps env (decode fentry)
  | If (e, truli, falsli) ->
	let boolval = eval env e in
	if boolval then
		steps env truli
	else
		steps env falsli 
  |Assign (reg, e) ->
	let value = eval env e in
        let regname = get_register_name reg in
        env.write regname value

and steps (env:sgxstate) instr = List.iter (fun elem->step env elem ) instr  

(* Should the following function have a type that uses effects associated with hyperstack ? 
   Is buf supposed to be a hyperstack?
*)
val ustar:(buffer word)->(buffer word)-> (buffer word)->nat ->nat->nat->nat->nat->unit->unit
let ustar regs buf calltable base wbmapstart uheapstart ustackstart ucodestart entry = 
  let size = 1000 in
  let mem = defensive regs buf calltable base wbmapstart ucodestart uheapstart ustackstart size in
  (* For testing *)
  steps mem [(Store(1uL,(Register "rax"),(Register "rcx")))] 

(* Place holder for parsing manifest and getting the start addresses and  
  calltable
 *)
let parse_manifest = ()
