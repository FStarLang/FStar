
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


noeq type memaccess =
 |MkMemAccess: 
	      read: (string->cpuregstate -> dword) -> (* Helper function to read registers, used by store *)
  	      load: (word -> address -> STL dword (requires (fun h -> true)) (ensures (fun h0 r h1 -> true))) -> 
  	      store:(word -> address-> dword -> cpuregstate ->STL bool (requires (fun h -> true)) (ensures (fun h0 r h1 -> true))) ->
 	      get_bitmap_set:(address->STL bool (requires (fun h -> true)) (ensures (fun h0 r h1 -> true)) )  ->
	      decode:(bool->program ->address-> cpuregstate->Tot (list stmt))->memaccess

val defensive: bool -> (buffer dword)->calltable ->address-> address->address->address->address->address->STL memaccess
									(requires (fun h -> true)) 
									(ensures (fun h0 r h1 -> true)) 
let defensive debugflag buf calltab base wbmapstart ucodestart uheapstart uheapsize ustackstart = 
  let read' (regname:string) (env:cpuregstate) :(Tot dword)  =
 	let rec search_reg (regname:string) (reglist:list register) :(Tot dword) = match reglist with
		  |[] -> (* raise Halt *)
			 let _ = if debugflag then 
					let _ = debug_print_string "Register " in
					let _ = debug_print_string regname in
					debug_print_string " not found: Raise Halt\n" else true in
			 0uL
		  |(MkReg regname' value)::tail ->
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
	(*
	 Given an address, this function returns if it is read/writable 
	 In Progress
	*)
   let get_bitmap_set addr = 
		let bitmapoffset = get_bitmap_offset uheapstart wbmapstart addr in 
		let value = load' 1ul bitmapoffset in
		let index = get_bitmap_index uheapstart addr in
		let mask = shift_left 1uL (cast_to_word index) (* prepare mask *) in
		if (eq (UInt64.logand value  mask) 1uL) then true else false
    in
  let store' (n:word) (addr:address) (v:dword) (env:cpuregstate): STL bool
	(requires (fun h -> true))
	(ensures (fun h0 r h1 -> true)) =
     if (gte addr  wbmapstart) && (lt addr  uheapstart) then
	(* addr is in write-bitmap, get the index
	   i.e. bitmapindex represents the address whose permission
	   is being toggled 
	*)
	let address_toggled = get_address_represented_in_bitmap uheapstart wbmapstart addr in 
	
	(* Check that bitmapindex belongs to current stack frame. Steps:
	  1. Read rbp register which contains current frame pointer
	  2. Check that 'bitmapindex' is less than [|rbp |] 
	*)
	let currentframestart = (read' "rbp" env) in

	if (lte address_toggled currentframestart) then
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
	       let _ = if debugflag then 
				let _ =  debug_print_string "Current frame start: " in
				let _ = debug_print_string (to_string currentframestart) in
				let _ =  debug_print_string "\n Toggling bitmap for address: " in
				let _ = debug_print_string (to_string address_toggled) in
				debug_print_string "\n"
			 else true in
        	let _ = Buffer.upd buf wordidx v in
		true
	else
		(* raise Halt *)
		let _ = if debugflag then 
					let _ = debug_print_string "Unauthorized bitmap update: Raise Halt\n" in
					let _ =  debug_print_string "Address being written to: " in
					let _ = debug_print_string (to_string addr) in
					let _ = debug_print_string "\n" in
					let _ =  debug_print_string "Frame Pointer: " in
					let _ = debug_print_string (to_string (read' "rbp" env)) in
					let _ = debug_print_string "\n" in
					let _ =  debug_print_string "Stack Pointer: " in
					let _ = debug_print_string (to_string (read' "rsp" env)) in
					let _ = debug_print_string "\n" in
					let _ =  debug_print_string "Bitmap Start: " in
					let _ = debug_print_string (to_string wbmapstart) in
					let _ = debug_print_string "\n" in
					let _ =  debug_print_string "Heap Start: " in
					let _ = debug_print_string (to_string uheapstart) in
					let _ = debug_print_string "\n" in
					let _ =  debug_print_string "Stack Start: " in
					let _ = debug_print_string (to_string ustackstart) in
					let _ =  debug_print_string "\nEnd-of-Dump\n" in
					debug_print_string "====================\n" 
			else true in
		false
    else if (gte addr uheapstart) && (lt addr  (add uheapstart uheapsize)) then
	(* Address is in UHeap... Check that bitmap is set *)  
	let isbitmapset = get_bitmap_set addr in
	if isbitmapset then
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
	       let _ = if debugflag then 
				let _ =  debug_print_string "Updating heap: " in
				let _ = debug_print_string (UInt32.to_string wordidx) in
				debug_print_string "\n"
			 else true in
        	let _ = Buffer.upd buf wordidx v in
		true
	else
		(* raise Halt *)
		let _ = if debugflag then debug_print_string "Bitmap not set: Raise Halt\n" else true in
		false
 
    else if  (lte addr ustackstart) && (gt addr (read' "rbp" env))  then
	(* Address belongs to older stack frames *)  
	let isbitmapset = get_bitmap_set addr in
	if isbitmapset then
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
	       let _ = if debugflag then 
				let _ =  debug_print_string "Updating older stack frame: " in
				let _ = debug_print_string (UInt32.to_string wordidx) in
				debug_print_string "\n"
			 else true in
         	let _ = Buffer.upd buf wordidx v in
		true
	else
		(* raise Halt *)
		let _ = if debugflag then debug_print_string "Bitmap not set: Raise Halt\n" else true in
		false
    else if (lte addr (read' "rbp" env)) && (gte addr (read' "rsp" env))  then
	(* Address belongs to current stack frames *)  
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
	       let _ = if debugflag then 
				let _ =  debug_print_string "Updating current stack frame: " in
				let _ = debug_print_string (UInt32.to_string wordidx) in
				debug_print_string "\n"
			 else true in
               let _ = Buffer.upd buf wordidx v in
	       true
    else
	let _ = if debugflag then 
			let _ = debug_print_string "Something went wrong. Dump as follows:\n" in
			let _ =  debug_print_string "Address being written to: " in
			let _ = debug_print_string (to_string addr) in
			let _ = debug_print_string "\n" in
			let _ =  debug_print_string "Frame Pointer: " in
			let _ = debug_print_string (to_string (read' "rbp" env)) in
			let _ = debug_print_string "\n" in
			let _ =  debug_print_string "Stack Pointer: " in
			let _ = debug_print_string (to_string (read' "rsp" env)) in
			let _ = debug_print_string "\n" in
			let _ =  debug_print_string "Base Address: " in
			let _ = debug_print_string (to_string base) in
			let _ = debug_print_string "\n" in
			let _ =  debug_print_string "Code Start: " in
			let _ = debug_print_string (to_string ucodestart) in
			let _ = debug_print_string "\n" in
			let _ =  debug_print_string "Bitmap Start: " in
			let _ = debug_print_string (to_string wbmapstart) in
			let _ = debug_print_string "\n" in
			let _ =  debug_print_string "Heap Start: " in
			let _ = debug_print_string (to_string uheapstart) in
			let _ = debug_print_string "\n" in
			let _ =  debug_print_string "Stack Start: " in
			let _ = debug_print_string (to_string ustackstart) in
			let _ =  debug_print_string "\nEnd-of-Dump\n" in
			debug_print_string "====================\n" 
		else true in
        false	
    in
  let decode' iscalltarget myprogram instraddr env = 
	
	let iscallable = search_func calltab instraddr in
	if  iscallable && iscalltarget then
		let func_name = get_func_name calltab instraddr in
		let func_attr = get_func_attributes calltab func_name in
		
		let ispublic = begin match func_attr with
				| Public -> true
				| _ -> false
				end in
		if ispublic then
			(* If number of arguments is more than 4, 
			  check that stack is atleast the size of remaining arguments
			 *)	
			let numberargs = get_arguments_number calltab func_name in 
			if (numberargs > 4 ) then
				let framestart = read' "rbp" env in
				let stacktop  = read' "rsp" env in
				let framesize = (sub framestart stacktop) in
				if  ((cast_to_nat framesize) <  (numberargs - 4)) then
					(* raise Halt *)
					let _ = if debugflag then debug_print_string "Bitmap not set: Raise Halt\n" else true in
					[]
				else
					(* Fetches instructions from start to end *)
					let stlist = get_stmt_list func_name myprogram in
						stlist
			else
				
					(* Fetches instructions from start to end *)
					let stlist = get_stmt_list func_name myprogram in
						stlist
		(* private functions. We ignore the calling convention *)
		else
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

   MkMemAccess read' load' store' get_bitmap_set decode'
	
let get_register_name = function
 | Register r -> r
 | _ -> (* raise Halt *) ""

val update: string -> dword->cpuregstate->Tot cpuregstate
let update (regname:string) (value:dword) (env:cpuregstate) =
 let rec loop (pre:list register) (post:list register) :(Tot cpuregstate) = match post with
	| [] -> (* raise Halt *) (Mkcpuregstate [])
	| (MkReg regname' v)::tail -> 
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

val invariant: cpuregstate -> Tot bool
let invariant env = 
	let reglist = get_reg_list env in
	let rec search_reg (li:list register) :(Tot bool) = begin match li with
		|[] -> false
		|(MkReg regname' value)::tail -> if regname' = "rsp" then false else
						search_reg tail
		end
	in
	search_reg reglist   

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
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Add " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op1) in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op2) in
		debug_print_string ";\n"
       		else true  in
	 env'
  | Sub (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (sub op1 op2) in
        let regname = get_register_name ed in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Sub " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op1) in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op2) in
		debug_print_string ";\n"
       		else true  in
	 env'
  | Cmp (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = if (eq op1 op2) then 1uL else 0uL in
        let regname = get_register_name ed in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Cmp " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op1) in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op2) in
		debug_print_string ";\n"
       		else true  in
	 env'
  | Mul (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (mul op1 op2) in
        let regname = get_register_name ed in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Mul " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op1) in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op2) in
		debug_print_string ";\n"
       		else true  in
	 env'
  | Div (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (div op1 op2) in
        let regname = get_register_name ed in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Div " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op1) in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op2) in
		debug_print_string ";\n"
       		else true  in
	 env'
  | Mod (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (rem op1 op2) in
        let regname = get_register_name ed in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Mod " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op1) in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op2) in
		debug_print_string ";\n"
       		else true  in
	 env'
  | Lsr (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (shift_left op1 (cast_to_word op2)) in
        let regname = get_register_name ed in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Lsr " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op1) in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op2) in
		debug_print_string ";\n"
       		else true  in
	 env'
  | Lor (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (logor op1 op2) in
        let regname = get_register_name ed in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Lor " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op1) in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string op2) in
		debug_print_string ";\n"
       		else true  in
	 env'
  | Store(iaddr, n, ea, ev)-> 
       let addr = eval env ea in
       let v = eval env ev in 
       let _ = defensivememop.store (cast_to_word n)  addr v env in
       let _ = if debugflag then
			let _ = debug_print_string (to_string iaddr) in
			let _ = debug_print_string ":" in
			let _ = debug_print_string "Store " in
			let _ = debug_print_string " " in
			let _ = debug_print_string (to_string addr) in
			let _ = debug_print_string " " in
			let _ = debug_print_string (to_string v) in
			debug_print_string ";\n"
       		else true in
       env
  | Load (iaddr, reg, n, ea) ->
       let addr = eval env ea in
       let wordn = (cast_to_word n) in
       let value = defensivememop.load wordn addr in
       let regname = get_register_name reg in
       let env' = update regname value env in
       let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Load " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string value) in
		debug_print_string ";\n"
       else true  in
       env'
  | Push(iaddr, reg)-> 
       let addr = eval env (Register "rsp") in
       let v = eval env reg in 
       let _ = if debugflag then
			let _ = debug_print_string (to_string iaddr) in
			let _ = debug_print_string ":" in
			let _ = debug_print_string "Push " in
			let _ = debug_print_string (to_string addr) in
			let _ = debug_print_string " " in
			let _ = debug_print_string (to_string v) in
			debug_print_string ";\n"
       		else true in
       let _ = defensivememop.store 1ul  addr v env in
       let env' = update "rsp" (sub addr 1uL) env in
       env'
  | Pop (iaddr, reg) ->
       let addr = eval env (Register "rsp")  in
       let env' = update "rsp" (add addr 1uL) env in
       let rspvalue' = eval env' (Register "rsp") in
       let value = defensivememop.load 1ul rspvalue' in
       let regname = get_register_name reg in
       let env'' = update regname value env' in
       let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Pop " in
		let _ = debug_print_string (to_string rspvalue') in
		let _ = debug_print_string " " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string value) in
		debug_print_string ";\n"
       else true  in
       env''
  | Call (iaddr, e) ->
       let fentry = eval env e in
	let  addr = eval env (Register "rsp") in
	(* Returns a list of stmts in callee.
	   Raises Exception if the function is not callable 
	*)	
       let  stmtlist = defensivememop.decode true myprogram fentry env in
	(* push the return address if stmtlist is not null *)
	let isnull = if (List.Tot.length stmtlist) = 0 then
				true 
			else false in
	let env' = if not isnull then
			 (* push the next address to return to *)
			 (* Note that the slot pointed to by stackpointer is empty, 
				use that slot and then decrement the stackpointer
			  *)
			let retaddr = (add iaddr 1uL) in
			let _ =	defensivememop.store 1ul addr retaddr env in
			update "rsp" (sub addr 1uL) env 
		   else env 
		in
       let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Call  " in
		let _ = debug_print_string (to_string fentry) in
		let _ = debug_print_string " " in
		let _ = debug_print_string "Return address pushed: " in
		let _ = debug_print_string (to_string (add iaddr 1uL)) in
		let _ = debug_print_string "Current rsp: " in
		let _ = debug_print_string (to_string (eval env' (Register "rsp"))) in
		debug_print_string "}\n"
	       else true in
	steps debugflag env' defensivememop myprogram stmtlist 

  | If (iaddr, e, truli, falsli) ->
	let boolval = eval env e in
        let t = if debugflag then
			let _ = debug_print_string (to_string iaddr) in
			let _ = debug_print_string ":" in
			let _ = debug_print_string "If-Else " in
			let _ = debug_print_string (to_string boolval) in
			debug_print_string " ;\n"
       		else true in
	if (eq boolval 1uL)  then
		steps debugflag env defensivememop myprogram (invert_stmt truli)
	else
		steps debugflag env defensivememop myprogram (invert_stmt falsli) 
  |Assign (iaddr, reg, e) ->
	let value = eval env e in
        let regname = get_register_name reg in
        let env' = update regname value env in
        let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		let _ = debug_print_string "Assign " in
		let _ = debug_print_string regname in
		let _ = debug_print_string " " in
		let _ = debug_print_string (to_string value) in
		debug_print_string "\n"
       		else true  in
	 env'

 | Jump (iaddr, e) -> 
	(* FIXME: what about checks for jump?? *)
	let targetaddress = eval env e in
	(* not modeling "rip" explicitly *)
	(* Get the stmt list from updated "rip" *)
        let  stmtlist = defensivememop.decode false myprogram targetaddress env in
	
       let t = if debugflag then
		let _ = debug_print_string (to_string iaddr) in
		let _ = debug_print_string ":" in
		debug_print_string "Jump;\n"
       else  true in
	steps debugflag env defensivememop myprogram stmtlist 

 | Return iaddr -> 
	     let rspvalue = eval env (Register "rsp") in
	     let rspvalue' = (add rspvalue 1uL) in
	     let env' = update "rsp" rspvalue' env in
	     (* get return address *)
	     let retaddr = defensivememop.load (cast_to_word 1uL) rspvalue' in 
	     (* get the instructions from return address *)
             let  stmtlist = defensivememop.decode false myprogram retaddr env' in
	     (* pop the return address *)
	     let t =  if debugflag then
			let _ = debug_print_string (to_string iaddr) in
			let _ = debug_print_string ":" in
			let _ = debug_print_string "Return " in
			let _ = debug_print_string (to_string retaddr) in
			let _ = debug_print_string " " in
			let _ = debug_print_string "Stack Pointer:" in
			let _ = debug_print_string (to_string rspvalue') in
			debug_print_string "\n"
		       else true in
	     steps debugflag env' defensivememop myprogram stmtlist 
		

and helperfunc  (debugflag:bool) (defensivememop:memaccess) (myprogram:program) (env':cpuregstate) (elem:stmt): STL cpuregstate 
					(requires (fun h -> true))
					(ensures (fun h0 r h1 -> false)) =
					step debugflag env' defensivememop myprogram elem 

and steps (debugflag:bool) (env:cpuregstate) (defensivememop:memaccess) myprogram instrlist = fold_left (helperfunc debugflag defensivememop myprogram) env  instrlist 

val ustar:bool->(buffer dword)->calltable->address ->address->address->address->address->address->address->program->STL cpuregstate
	(requires (fun h-> True))
	(ensures (fun h0 r h1 -> True))
let ustar debugflag buf calltab base wbmapstart uheapstart uheapsize ustackstart ucodestart entry myprogram = 
  (* Modeling registers as list?? *)
  let regslist = [MkReg "rsp" ustackstart; MkReg "rbp" 0uL; MkReg "rax"  0uL; MkReg "rbx" 0uL; MkReg "rcx" 0uL;MkReg "rdx" 0uL;MkReg "r8" 0uL;MkReg "r9" 0uL;MkReg "flag" 0uL;] in
  let env = (Mkcpuregstate regslist) in
  let mem = defensive debugflag buf calltab base wbmapstart ucodestart uheapstart uheapsize ustackstart in
  let stmtlist = mem.decode true  myprogram entry env in
  let _ = if debugflag then debug_print_string "Stepping into main\n" else true in
  steps debugflag env mem myprogram stmtlist

val main:bool -> STL cpuregstate
	(requires (fun h-> True))
	(ensures (fun h0 r h1 -> True))
let main debugflag = 
  let base = 1000uL in
  let ucodestart = 1100uL in
  let wbmapstart = 1200uL in
  let uheapstart = 1300uL in
  let uheapsize = 400uL in
  let ustacksize = 400uL in
  let ustackstart = (add (add uheapstart uheapsize) ustacksize) in
  let entry = 1200uL in 
  let bufsize = add (sub ustackstart base) 2uL in 
  let buf = Buffer.create 0uL (cast_to_word bufsize) in
  let calltab = parse_manifest () in
  let myprogram = testprogram in 
  let _ = if debugflag then debug_print_string "Printing Whole Program\n" else true in
  let _ = if debugflag then print_prog myprogram else true in
  let _ = if debugflag then debug_print_string "=======================\n" else true in
  let _ = if debugflag then 
				let _ = debug_print_string "Buffer Size: " in
				debug_print_string (to_string bufsize)
			    else true in
  let _ = if debugflag then debug_print_string "\n=======================\n" else true in
  ustar debugflag buf calltab base wbmapstart uheapstart uheapsize ustackstart ucodestart entry myprogram 
  

