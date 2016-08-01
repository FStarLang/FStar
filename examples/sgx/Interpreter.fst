
module Interpreter

open FStar.Buffer
open FStar.ST
open FStar.UInt64
open FStar.List
open Util
open Ast
open Test
open SGXState

exception Halt

let dword = UInt64.t
let word = UInt32.t
let address = UInt64.t
let offset = UInt64.t

(*
val STX.Halt: unit -> STX 'a 
val STX.Load : unit -> buffer ... -> STX dword
val STX.Store: unit -> buffer ... -> STX unit
*)

assume val search: (buffer dword)->(addr:address)-> bool

type memaccess =
 |MkMemAccess: 
	      read: (cpuregstate -> string) -> (* Helper function to read registers, used by store *)
  	      load: (word -> address -> dword) ->
  	      store:(word -> address-> dword -> cpuregstate ->unit)->
	      decode:(program ->address->(list stmt))->memaccess

val defensive: (buffer dword)->(list dword) ->address-> address->address->address->address->memaccess
let defensive buf calltable base wbmapstart ucodestart uheapstart ustackstart = 
  let read' (regname:string) (env:cpuregstate) =
 	let rec search_reg regname = function
		  |[] -> raise Halt
		  |(MkReg regname' value)::tail -> if regname' = regname then
								value
							else
								search_reg regname tail
	in
	search_reg regname (get_reg_list env)
  in
  let load' (n:word) (addr:address) = 
       let idx = (sub addr base) in
       let wordidx = (cast_to_word idx) in
       (* Buffer.index buf wordidx *)
	()
    in
  let store' (n:word) (v:dword) (addr:address) (env:cpuregstate) =
     if (gt addr  wbmapstart) && (lt addr  ucodestart) then
	(* addr is in write-bitmap, get the index
	   i.e. bitmapindex represents the address whose permission
	   is being toggled 
	*)
	let bitmapindex = get_address_represented_in_bitmap base wbmapstart addr in 
	
	(* Check that bitmapindex belongs to current stack frame. Steps:
	  1. Read rbp register which contains current frame pointer
	  2. Check that 'bitmapindex' is less than [|rbp |] 
	*)
	let currentframestart = (read' "rbp" env) in
	if (lt bitmapindex currentframestart) then	
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
        	(* Buffer.upd buf wordidx v*)
		()
	else
		raise Halt
    else if (gt addr uheapstart) && (lt addr  ustackstart) then
	(* Address is in UHeap... Check that bitmap is set *)  
	let isbitmapset = get_bitmap_set base wbmapstart addr in
	if isbitmapset then
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
        	(* Buffer.upd buf wordidx v*)
		()
	else
		raise Halt
 
    else if (gt addr ustackstart) && (lt addr (read' "rbp" env))  then
	(* Address belongs to older stack frames *)  
	let isbitmapset = get_bitmap_set base wbmapstart addr in
	if isbitmapset then
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
        	(* Buffer.upd buf wordidx v*)
		()
	else
		raise Halt

    else if (gt addr (read' "rbp" env)) && (lt addr (read' "rsp" env))  then
	(* Address belongs to current stack frames *)  
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
        	(* Buffer.upd buf wordidx v*)
		()
    in
  let decode' myprogram instraddr = 
	let iscallable = search calltable instraddr in
	if  iscallable then
		let func_name = get_func_name calltable instraddr in
		(* Fetches instructions from start to end *)
		let stlist = get_stmt_list func_name myprogram in
			stlist
	else
		raise Halt
    in	

   MkMemAccess read' load' store' decode'
	
let get_register_name = function
 | Register r -> r
 | _ -> raise Halt

val update: string -> dword->cpuregstate->cpuregstate
let update (regname:string) (value:dword) (env:cpuregstate) =
 let rec loop pre = function
	| [] -> raise Halt
	| MkReg(regname', v)::tail -> if regname' = regname then
						(pre @ [MkReg (regname, value)] @ tail)
					  else
						loop (pre@[(MkReg (regname,v))]) tail 
	in loop [] env
						

val eval: cpuregstate -> exp -> dword
let eval (env:cpuregstate) = function
 | Register r ->  let rec search_reg regname = function
		  |[] -> raise Halt
		  |(MkReg regname' value)::tail -> if regname' = regname then
								value
							else
								search_reg regname tail
		in search_reg r (get_reg_list env)
 | Constant n -> n


val step : cpuregstate  -> program -> stmt -> ST cpuregstate
val steps : cpuregstate -> program -> (list stmt) -> ST cpuregstate
let rec step (env:cpuregstate) (defensivememop:memaccess) (myprogram:program) = function 
  | Skip -> env
  | Store(n, ea, ev)-> 
       let a = eval env ea in
       let v = eval env ev in 
       let _ = defensivememop.store (cast_to_word n) v a env in
       env
  | Load (reg, n, ea) ->
       let a = eval env ea in
       let value = defensivememop.load (cast_to_word n) a in
       let regname = get_register_name reg in
       let env' = update regname value in
       env'
  | Call e ->
       let fentry = eval env e in
	(* Returns a list of stmts in callee.
	   Raises Exception if the function is not callable 
	*)	
       let  stmtlist = defensivememop.decode myprogram fentry in
	steps env defensivememop myprogram stmtlist 
  | If (e, truli, falsli) ->
	let boolval = eval env e in
	if boolval then
		steps env defensivememop myprogram truli
	else
		steps env defensivememop myprog falsli 
  |Assign (reg, e) ->
	let value = eval env e in
        let regname = get_register_name reg in
        let env' = update regname value in
	 env'

 | Jump e -> 
	let value = eval env e in
	let env' = update "rip" value in 
	(* FIXME: what about checks for jump?? *)
	env'

 | Return -> let rsp = eval env (Register "rsp") in
	     let rsp' = rsp - 1 in
		update "rsp" rsp' 

and steps (env:cpuregstate) (defensivememop:memaccess) myprogram instrlist = List.fold_right (fun elem env' ->step env' defensivememop myprogram elem) instrlist env  

(* Should the following function have a type that uses effects associated with effect ST ?  *)
val ustar: (buffer dword)->address ->address->address->address->address->address->program->ST cpuregstate
let ustar calltable base wbmapstart uheapstart ustackstart ucodestart entry myprogram = 
  let memsize = 1000 in
  let regsize = 1000 in
  let buf = create  0uy memsize in 

  (* Modeling registers as list?? *)
  let regslist = [MkReg "rsp" 0uy; MkReg "rbp" 0uy; MkReg "rip"  0uy; MkReg "rax" 0uy] in
  let mem = defensive buf calltable base wbmapstart ucodestart uheapstart ustackstart in
  let stmtlist = mem.decode myprogram entry in
  steps (Mkcpuregstate regslist) mem  myprogram stmtlist


(* Place holder for parsing manifest and getting the start addresses and  
  calltable
 *)
let parse_manifest = ()
