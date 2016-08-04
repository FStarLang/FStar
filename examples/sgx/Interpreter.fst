
module Interpreter

open FStar.Buffer
open FStar.HST
open FStar.UInt64
open FStar.List.Tot
open Util
open Ast
open Test
open SGXState

exception Halt

(*
val STX.Halt: unit -> STX 'a 
val STX.Load : unit -> buffer ... -> STX dword
val STX.Store: unit -> buffer ... -> STX unit
*)

assume val search: (buffer dword)->(addr:address)-> bool

type memaccess =
 |MkMemAccess: 
	      read: (string->cpuregstate -> dword) -> (* Helper function to read registers, used by store *)
  	      load: (word -> address -> STL dword (requires (fun h -> true)) (ensures (fun h0 r h1 -> true))) -> 
  	      store:(word -> address-> dword -> cpuregstate ->STL unit (requires (fun h -> true)) (ensures (fun h0 r h1 -> true))) ->
	      decode:(program ->address->Tot (list stmt))->memaccess

val defensive: (buffer dword)->(buffer dword) ->address-> address->address->address->address->STL memaccess
									(requires (fun h -> true)) 
									(ensures (fun h0 r h1 -> true)) 
let defensive buf calltable base wbmapstart ucodestart uheapstart ustackstart = 
  let read' (regname:string) (env:cpuregstate) :(Tot dword)  =
 	let rec search_reg (regname:string) (reglist:list register) :(Tot dword) = match reglist with
		  |[] -> (* raise Halt *) 0uL
		  |(MkReg regname' value)::tail -> if regname' = regname then
								value
							else
								search_reg regname tail
	in
	search_reg regname (get_reg_list env)
  in
  let load'(n:word) (addr:address): STL dword
	(requires (fun h -> true))
	(ensures (fun h0 r h1 -> true))
	  =
       (let idx = (sub addr base) in
       let wordidx = (cast_to_word idx) in
       Buffer.index buf wordidx 
       )
    in
  let store' (n:word) (addr:address) (v:dword) (env:cpuregstate) =
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
        	Buffer.upd buf wordidx v
	else
		(* raise Halt *)
		()
    else if (gt addr uheapstart) && (lt addr  ustackstart) then
	(* Address is in UHeap... Check that bitmap is set *)  
	let isbitmapset = get_bitmap_set base wbmapstart addr in
	if isbitmapset then
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
        	Buffer.upd buf wordidx v
	else
		(* raise Halt *)
		()
 
    else if (gt addr ustackstart) && (lt addr (read' "rbp" env))  then
	(* Address belongs to older stack frames *)  
	let isbitmapset = get_bitmap_set base wbmapstart addr in
	if isbitmapset then
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
         	Buffer.upd buf wordidx v
	else
		(* raise Halt *)
		()

    else if (gt addr (read' "rbp" env)) && (lt addr (read' "rsp" env))  then
	(* Address belongs to current stack frames *)  
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
                Buffer.upd buf wordidx v
    in
  let decode' myprogram instraddr = 
	let iscallable = search_func calltable instraddr in
	if  iscallable then
		let func_name = get_func_name calltable instraddr in
		(* Fetches instructions from start to end *)
		let stlist = get_stmt_list func_name myprogram in
			stlist
	else
		(* raise Halt *)
			[]
    in	

   MkMemAccess read' load' store' decode'
	
let get_register_name = function
 | Register r -> r
 | _ -> (* raise Halt *) ""

val update: string -> dword->cpuregstate->Tot cpuregstate
let update (regname:string) (value:dword) (env:cpuregstate) =
 let rec loop (pre:list register) (post:list register) :(Tot cpuregstate) = match post with
	| [] -> (* raise Halt *) (Mkcpuregstate [])
	| (MkReg regname' v)::tail -> if regname' = regname then
						(Mkcpuregstate (pre@[MkReg regname value] @ tail))
					  else
						loop (pre@[(MkReg regname v)]) tail 
	in loop [] (get_reg_list env)
						

val eval: cpuregstate -> exp -> Tot dword
let eval (env:cpuregstate) = function
 | Register r ->  let rec search_reg (regname:string) (li:list register) :Tot dword = match li with
		  |[] -> (* raise Halt *) 0uL
		  |(MkReg regname' value)::tail -> if regname' = regname then
								value
							else
								search_reg regname tail
		in search_reg r (get_reg_list env)
 | Constant n -> n


val step : cpuregstate  ->memaccess-> program -> stmt -> STL cpuregstate 
			(requires (fun h -> true))
			(ensures (fun h0 r h1 -> true))
val steps : cpuregstate ->memaccess-> program -> (list stmt) -> STL cpuregstate
			(requires (fun h -> true))
			(ensures (fun h0 r h1 -> true))
assume val fold_right: ('a -> 'b -> STL 'b
			(requires (fun h -> true))
			(ensures (fun h0 r h1 -> true))) -> list 'a -> 'b -> STL 'b
								(requires (fun h -> true))
								(ensures (fun h0 r h1 -> true))
let rec step (env:cpuregstate) (defensivememop:memaccess) (myprogram:program) = function 
  | Skip -> env
  | Store(n, ea, ev)-> 
       let a = eval env ea in
       let v = eval env ev in 
       let _ = defensivememop.store (cast_to_word n) v a env in
       env
  | Load (reg, n, ea) ->
       let a = eval env ea in
       let wordn = (cast_to_word n) in
       let value = defensivememop.load wordn a in
       let regname = get_register_name reg in
       let env' = update regname value env in
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
	if not (eq boolval 0uL)  then
		steps env defensivememop myprogram truli
	else
		steps env defensivememop myprogram falsli 
  |Assign (reg, e) ->
	let value = eval env e in
        let regname = get_register_name reg in
        let env' = update regname value env in
	 env'

 | Jump e -> 
	let value = eval env e in
	let env' = update "rip" value env in 
	(* FIXME: what about checks for jump?? *)
	env'

 | Return -> let rspvalue = eval env (Register "rsp") in
	     let rspvalue' = (sub rspvalue 1uL) in
		update "rsp" rspvalue' env

and helperfunc  (defensivememop:memaccess) (myprogram:program) (elem:stmt) (env':cpuregstate): STL cpuregstate 
					(requires (fun h -> true))
					(ensures (fun h0 r h1 -> false)) =
					step env' defensivememop myprogram elem 

and steps (env:cpuregstate) (defensivememop:memaccess) myprogram instrlist = fold_right   (helperfunc defensivememop myprogram) instrlist env  

(* Should the following function have a type that uses effects associated with effect ST ?  *)
val ustar:(buffer dword)->(buffer dword)->address ->address->address->address->address->address->program->STL cpuregstate
	(requires (fun h-> True))
	(ensures (fun h0 r h1 -> True))
let ustar buf calltable base wbmapstart uheapstart ustackstart ucodestart entry myprogram = 
  (* Modeling registers as list?? *)
  let regslist = [MkReg "rsp" 0uL; MkReg "rbp" 0uL; MkReg "rip"  0uL; MkReg "rax" 0uL] in
  let mem = defensive buf calltable base wbmapstart ucodestart uheapstart ustackstart in
  let stmtlist = mem.decode myprogram entry in
  steps (Mkcpuregstate regslist) mem  myprogram stmtlist

val main:unit -> STL cpuregstate
	(requires (fun h-> True))
	(ensures (fun h0 r h1 -> True))
let main _ = 
  let base = 1000uL in
  let wbmapstart = 1100uL in
  let ucodestart = 1200uL in
  let ustackstart = 1300uL in
  let uheapstart = 1400uL in
  let entry = 1200uL in 
  let buf = Buffer.create 0uL 500ul in
  let calltable = Buffer.create 0uL 100ul in
  let myprogram = [("main", Seq [(Load ((Register "rax"), 4uL, (Register "rbx")))])] in
  ustar buf calltable base wbmapstart uheapstart ustackstart ucodestart entry myprogram 
  

(* Place holder for parsing manifest and getting the start addresses and  
  calltable
 *)
let parse_manifest = ()
