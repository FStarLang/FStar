
module Interpreter

open FStar.Buffer
open FStar.HST
open FStar.UInt64
open FStar.List.Tot
open FStar.IO
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
val fold_left: ('a -> 'b -> STL 'a
			(requires (fun h -> true))
			(ensures (fun h0 r h1 -> true))) -> 'a -> list 'b -> STL 'a
								(requires (fun h -> true))
								(ensures (fun h0 r h1 -> true))
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl					


type memaccess =
 |MkMemAccess: 
	      read: (string->cpuregstate -> dword) -> (* Helper function to read registers, used by store *)
  	      load: (word -> address -> STL dword (requires (fun h -> true)) (ensures (fun h0 r h1 -> true))) -> 
  	      store:(word -> address-> dword -> cpuregstate ->STL unit (requires (fun h -> true)) (ensures (fun h0 r h1 -> true))) ->
	      decode:(bool->program ->address->Tot (list stmt))->memaccess

val defensive: bool -> (buffer dword)->(buffer dword) ->address-> address->address->address->address->STL memaccess
									(requires (fun h -> true)) 
									(ensures (fun h0 r h1 -> true)) 
let defensive debugflag buf calltable base wbmapstart ucodestart uheapstart ustackstart = 
  let read' (regname:string) (env:cpuregstate) :(Tot dword)  =
 	let rec search_reg (regname:string) (reglist:list register) :(Tot dword) = match reglist with
		  |[] -> (* raise Halt *)
			 let _ = if debugflag then 
					let _ = debug_print_string "Register " in
					let _ = debug_print_string regname in
					debug_print_string " not found: Raise Halt\n" else true in
			 0uL
		  |(MkReg regname' value)::tail ->
				 	let _ = if debugflag then 
						let _ = debug_print_string "Register " in
						let _ = debug_print_string regname' in
						debug_print_string "\n" else true in
					if regname' = regname then
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
		let _ = if debugflag then debug_print_string "Bitmap not set: Raise Halt" else true in
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
		let _ = if debugflag then debug_print_string "Bitmap not set: Raise Halt" else true in
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
		let _ = if debugflag then debug_print_string "Decode: Raise Halt" else true in
		()

    else if (gt addr (read' "rbp" env)) && (lt addr (read' "rsp" env))  then
	(* Address belongs to current stack frames *)  
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
                Buffer.upd buf wordidx v
    in
  let decode' iscalltarget myprogram instraddr = 
	
	let iscallable = search_func calltable instraddr in
	if  iscallable && iscalltarget then
		let func_name = get_func_name calltable instraddr in
		(* Fetches instructions from start to end *)
		let stlist = get_stmt_list func_name myprogram in
			stlist
	else if (not iscallable) && iscalltarget then
		(* raise Halt *)
		let _ = if debugflag then debug_print_string "Decode: Raise Halt" else true in
			[]
	else (* jump target *)
		let stlist = get_stmt_list_in_current_function instraddr myprogram in
			stlist
    in	

   MkMemAccess read' load' store' decode'
	
let get_register_name = function
 | Register r -> r
 | _ -> (* raise Halt *) ""

val update: string -> dword->cpuregstate->Tot cpuregstate
let update (regname:string) (value:dword) (env:cpuregstate) =
 let rec loop (pre:list register) (post:list register) :(Tot cpuregstate) = match post with
	| [] -> (* raise Halt *) (Mkcpuregstate [])
	| (MkReg regname' v)::tail -> 
						let _ = debug_print_string "Register " in
						let _ = debug_print_string regname' in
						let _ = debug_print_string "\n" in
					if regname' = regname then
						(Mkcpuregstate (pre@[MkReg regname value] @ tail))
					  else
						loop (pre@[(MkReg regname' v)]) tail 
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

val step : bool -> cpuregstate  ->memaccess-> program -> stmt -> STL cpuregstate 
			(requires (fun h -> true))
			(ensures (fun h0 r h1 -> true))
val steps : bool-> cpuregstate ->memaccess-> program -> (list stmt) -> STL cpuregstate
			(requires (fun h -> true))
			(ensures (fun h0 r h1 -> true))
let rec step (debugflag:bool) (env:cpuregstate) (defensivememop:memaccess) (myprogram:program) = function 
  | Skip iaddr ->
       		let t = if debugflag then
				debug_print_string "Skip;\n"
       			else true in
		env
  | Add (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (add op1 op2) in
        let regname = get_register_name ed in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string "Add " in
		let _ = debug_print_string regname in
		debug_print_string "\n"
       		else true  in
	 env'
  | Cmp (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = if (eq op1 op2) then 1uL else 0uL in
        let regname = get_register_name ed in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string "Cmp " in
		let _ = debug_print_string regname in
		debug_print_string "\n"
       		else true  in
	 env'
  | Store(iaddr, n, ea, ev)-> 
       let a = eval env ea in
       let v = eval env ev in 
       let _ = defensivememop.store (cast_to_word n) v a env in
       let t = if debugflag then
			debug_print_string "Store;\n"
       		else true in
       env
  | Load (iaddr, reg, n, ea) ->
       let a = eval env ea in
       let wordn = (cast_to_word n) in
       let value = defensivememop.load wordn a in
       let regname = get_register_name reg in
       let env' = update regname value env in
       let t = if debugflag then
		let _ = debug_print_string "Load " in
		let _ = debug_print_string regname in
		debug_print_string "\n"
       else true  in
       env'
  | Call (iaddr, e) ->
       let fentry = eval env e in
	(* Returns a list of stmts in callee.
	   Raises Exception if the function is not callable 
	*)	
       let  stmtlist = defensivememop.decode true myprogram fentry in
       let t = if debugflag then
	debug_print_string "Call;\n"
       else true in
	steps debugflag env defensivememop myprogram stmtlist 
  | If (iaddr, e, truli, falsli) ->
	let boolval = eval env e in
        let t = if debugflag then
			debug_print_string "If-Else;\n"
       		else true in
	if not (eq boolval 1uL)  then
		steps debugflag env defensivememop myprogram (invert_stmt truli)
	else
		steps debugflag env defensivememop myprogram (invert_stmt falsli) 
  |Assign (iaddr, reg, e) ->
	let value = eval env e in
        let regname = get_register_name reg in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string "Assign " in
		let _ = debug_print_string regname in
		debug_print_string "\n"
       		else true  in
	 env'

 | Jump (iaddr, e) -> 
	(* FIXME: what about checks for jump?? *)
	let targetaddress = eval env e in
	(* not modeling "rip" explicitly *)
	(* Get the stmt list from updated "rip" *)
        let  stmtlist = defensivememop.decode false myprogram targetaddress in
	
       let t = if debugflag then
	debug_print_string "Jump;\n"
       else  true in
	steps debugflag env defensivememop myprogram stmtlist 

 | Return iaddr -> 
	     let rspvalue = eval env (Register "rsp") in
	     let rspvalue' = (sub rspvalue 1uL) in
	      let t =  if debugflag then
		debug_print_string "Return;\n"
	       else true in
	     update "rsp" rspvalue' env

and helperfunc  (debugflag:bool) (defensivememop:memaccess) (myprogram:program) (env':cpuregstate) (elem:stmt): STL cpuregstate 
					(requires (fun h -> true))
					(ensures (fun h0 r h1 -> false)) =
					step debugflag env' defensivememop myprogram elem 

and steps (debugflag:bool) (env:cpuregstate) (defensivememop:memaccess) myprogram instrlist = fold_left (helperfunc debugflag defensivememop myprogram) env  instrlist 

(* Should the following function have a type that uses effects associated with effect ST ?  *)
val ustar:bool->(buffer dword)->(buffer dword)->address ->address->address->address->address->address->program->STL cpuregstate
	(requires (fun h-> True))
	(ensures (fun h0 r h1 -> True))
let ustar debugflag buf calltable base wbmapstart uheapstart ustackstart ucodestart entry myprogram = 
  (* Modeling registers as list?? *)
  let regslist = [MkReg "rsp" 0uL; MkReg "rbp" 0uL; MkReg "rax"  0uL; MkReg "rbx" 0uL; MkReg "rcx" 0uL] in
  let mem = defensive debugflag buf calltable base wbmapstart ucodestart uheapstart ustackstart in
  let stmtlist = mem.decode true  myprogram entry in
  let _ = if debugflag then debug_print_string "Stepping into main\n" else true in
  steps debugflag (Mkcpuregstate regslist) mem  myprogram stmtlist

val main:bool -> STL cpuregstate
	(requires (fun h-> True))
	(ensures (fun h0 r h1 -> True))
let main debugflag = 
  let base = 1000uL in
  let wbmapstart = 1100uL in
  let ucodestart = 1200uL in
  let ustackstart = 1300uL in
  let uheapstart = 1400uL in
  let entry = 1200uL in 
  let buf = Buffer.create 0uL 500ul in
  let calltable = Buffer.create 0uL 100ul in
  let myprogram = testprogram in 
  let _ = if debugflag then debug_print_string "Printing Whole Program\n" else true in
  let _ = if debugflag then print_prog myprogram else true in
  let _ = if debugflag then debug_print_string "=======================\n" else true in
  ustar debugflag buf calltable base wbmapstart uheapstart ustackstart ucodestart entry myprogram 
  

(* Place holder for parsing manifest and getting the start addresses and  
  calltable
 *)
let parse_manifest = ()
