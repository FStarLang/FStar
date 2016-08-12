
(*--build-config
    options:--z3timeout 60 --max_fuel 60;
 --*)
module VerInterpreter

open FStar.Int
open FStar.Heap
open FStar.Buffer
open FStar.HST
open FStar.UInt64
open FStar.List.Tot
open FStar.IO
open VerUtil
open Ast
open Test
open VerSGXState

exception Halt

(*
val STX.Halt: unit -> STX 'a 
val STX.Load : unit -> buffer ... -> STX dword
val STX.Store: unit -> buffer ... -> STX unit
*)

val fold_left: ('a -> 'b -> STL 'a
			(requires (fun h -> true))
			(ensures (fun h0 r h1 -> true))) -> 'a -> list 'b -> STL 'a
								(requires (fun h -> true))
								(ensures (fun h0 r h1 -> true))
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl					


assume val debugflag:bool

(* pre-condition: idx fits the size of UInt32
   		  idx is less than length of the buffer
 *)
let load (n:word) (addr:address) (buf: buffer dword) (base:address): STL dword
	(requires (fun h -> (gte addr base) /\ (let idx =(sub addr base) in (Int.size (UInt64.v idx) UInt32.n))
				/\ (let idx = (sub addr base) in ((UInt64.v idx) < (Buffer.length buf)))
				/\ live h buf)
				)
	(ensures (fun h0 r h1 -> live h0 buf /\ h1 == h0))
	  =
       let idx = (sub addr base) in
       let wordidx = (cast_to_word idx) in
      		 Buffer.index buf wordidx 


let get_bitmap_set (addr:address) (buf:buffer dword) (base:address)  (wbmapstart:address) (uheapstart:address) (ustackstart:address): STL bool 
	(requires (fun h -> (gte addr base) 
				/\ (gte uheapstart wbmapstart) 
				/\ (gte wbmapstart base)
				/\ (gte addr uheapstart)
				/\ (gte ustackstart addr)
				/\ (let idx =(sub addr base) in (Int.size (UInt64.v idx) UInt32.n))
				/\ (let size = (sub ustackstart base) in ((UInt64.v size) < (Buffer.length buf)))
				/\ live h buf)
	)
	(ensures (fun h0 r h1 -> live h0 buf /\ h1 == h0)) =
		let bitmapoffset = get_bitmap_offset addr base wbmapstart uheapstart ustackstart in 
		let value = load 1ul bitmapoffset buf base in
		let index = get_bitmap_index addr base wbmapstart uheapstart ustackstart in 
		let wordidx = cast_to_word index  in
		let mask = shift_left 1uL wordidx (* prepare mask *) in
		(eq (UInt64.logand value  mask) 1uL)

let heap_or_active_stack (addr:address)  (uheapstart:address) (ustackstart:address) : Ghost bool
	(requires ((gte ustackstart uheapstart) /\
		   (gte ustackstart addr))
	)
	(ensures  (fun r -> if r then 
				((gte addr uheapstart) /\ (gte ustackstart addr))
			    else
				True
		)) =
    if (gte addr uheapstart) && (lte addr ustackstart)  then true
    else false
   

let get_bitmap_set_pure (h:HyperStack.mem) (addr:address) (buf:buffer dword{live h buf}) (base:address)  (wbmapstart:address) (uheapstart:address) (ustackstart:address): Ghost bool 
	(requires ((gte addr base) 
				/\ (gte uheapstart wbmapstart) 
				/\ (gte wbmapstart base)
				/\ (gte addr uheapstart)
				/\ (gte ustackstart addr)
				/\ (let idx =(sub addr base) in (Int.size (UInt64.v idx) UInt32.n))
				/\ (let size = (sub ustackstart base) in ((UInt64.v size) < (Buffer.length buf)))
				)
	)
	(ensures (fun r -> True)) =
		let bitmapoffset = get_bitmap_offset addr base wbmapstart uheapstart ustackstart in 
		let bufindex = sub bitmapoffset base in
		let value = Buffer.get h buf (UInt64.v bufindex) in
		let index = get_bitmap_index addr base wbmapstart uheapstart ustackstart in 
		let wordidx = cast_to_word index  in
		let mask = shift_left 1uL wordidx (* prepare mask *) in
		(eq (UInt64.logand value  mask) 1uL)
		
#set-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2"

  let store (n:word) (addr:address) (v:dword) (env:cpuregstate)  (base:address)  (wbmapstart:address) (wbmapsize:word) (ucodestart:address) (ucodesize:address) (uheapstart:address) (uheapsize:address) (ustackstart:address) (ustacksize:address) (buf:buffer dword): STL bool 
	(requires (fun h -> (gte addr base) 
				/\ (gte ustackstart addr)
				(* buffer layout *)
				/\ (gte ucodestart base)
				/\ (gte wbmapstart ucodestart)
				/\ (gte uheapstart wbmapstart) 
				/\ (gte ustackstart uheapstart)
				(* bitmapsize (16bits), heapstart,heapsize, stackstart, stacksize fits in 32 bits...
				   just to make life easier for satisfying mul pre-conditions *)
			 	/\ (UInt.fits (UInt32.v wbmapsize) UInt16.n)
				/\ (Int.size (UInt64.v uheapstart) UInt32.n)  
				/\ (Int.size (UInt64.v uheapsize) UInt32.n)  
				/\ (Int.size (UInt64.v ustackstart) UInt32.n)  
				/\ (Int.size (UInt64.v ustacksize) UInt32.n)  
				  (* buffer size fits in 32bit *)
			 	/\ (UInt.size (UInt64.v (UInt64.sub ustackstart base)) UInt32.n)
				    (* bitmapsize *)
				/\ (UInt32.v wbmapsize) < (UInt64.v (div (UInt64.sub ustackstart uheapstart) 64uL))
				  (* requires that last address represented by bitmap is less than stackstart *)
				/\ (let lastaddr = lastaddr_less_than_stackaddress wbmapsize uheapstart ustackstart in
					(lte lastaddr ustackstart) 
				    )
				(*  size between base and ustackstart is less than actual buffer size *)
				/\ (let size = (sub ustackstart base) in ((UInt64.v size) < (Buffer.length buf)))
				/\ (let idx =(sub addr base) in (Int.size (UInt64.v idx) UInt32.n))

				(* rbp and rsp are always in stack ranges *)
				/\ ( let stackend = (add ustackstart  ustacksize) in
					(gte env.rbp stackend) && (lte env.rbp ustackstart) && (gte env.rsp stackend) && (lte env.rsp ustackstart) 
				   )
				 (* rbp >= rsp *)
				/\ ((gte env.rbp env.rsp) == true)
				/\ live h buf)
	)
	(ensures (fun h0 r h1 ->live h0 buf /\ live h1 buf /\ modifies_1 buf h0 h1 
				/\ (gte addr base) 
				/\ (gte ucodestart base)
				/\ (gte wbmapstart ucodestart)
				/\ (gte ustackstart uheapstart)
				/\ (gte uheapstart wbmapstart) 
				/\ (gte ustackstart addr)
				/\ (let idx =(sub addr base) in (Int.size (UInt64.v idx) UInt32.n))
				/\ ((UInt64.v (sub ustackstart base)) < (Buffer.length buf)) 
				(*
				(* if address is stack or heap and the store is successful, then it should be writable *)
				/\ (if (heap_or_active_stack addr uheapstart ustackstart ) && r then 
					((get_bitmap_set_pure h0 addr buf base wbmapstart uheapstart ustackstart) == true)
				   else True
				   )
				*)
				/\ (if (gte addr ucodestart) && (lte addr wbmapstart) then
						(r==false)
				    else True
				   )
				(* rbp and rsp are always in stack ranges *)
				/\ (Int.size (UInt64.v ustackstart) UInt32.n)  
				/\ (Int.size (UInt64.v ustacksize) UInt32.n)  
				/\ ( let stackend = (add ustackstart  ustacksize) in
					(gte env.rbp stackend) && (lte env.rbp ustackstart) && (gte env.rsp stackend) && (lte env.rsp ustackstart) 
				   )
				 (* rbp >= rsp *)
				/\ ((gte env.rbp env.rsp) == true)
		 )
	) =
	
      (* Code section is not writable *)
     if	(gte addr ucodestart) && (lte addr wbmapstart) then
	false
     else if (gte addr  wbmapstart) && (lt addr  uheapstart)&& (lte (UInt64.sub addr wbmapstart) (Int.Cast.uint32_to_uint64 wbmapsize)) then
	(* addr is in write-bitmap, get the index
	   i.e. bitmapindex represents the address whose permission
	   is being toggled 
	*)
	let address_toggled = get_address_represented_in_bitmap addr base uheapstart wbmapstart wbmapsize ustackstart in
	(* Check that bitmapindex belongs to current stack frame. Steps:
	  1. Read rbp register which contains current frame pointer
	  2. Check that 'bitmapindex' is less than [|rbp |] 
	*)
	let currentframestart = (read "rbp" env) in
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
					let _ = debug_print_string (to_string (read "rbp" env)) in
					let _ = debug_print_string "\n" in
					let _ =  debug_print_string "Stack Pointer: " in
					let _ = debug_print_string (to_string (read "rsp" env)) in
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
	let isbitmapset = get_bitmap_set addr buf base  wbmapstart uheapstart ustackstart in
	if isbitmapset then
	       let idx = (sub addr base) in
	       let wordidx = (cast_to_word idx) in
	       let r = if debugflag then 
				let _ =  debug_print_string "Updating heap: " in
				let _ = debug_print_string (UInt32.to_string wordidx) in
				debug_print_string "\n"
			 else true in
        	let t = Buffer.upd buf wordidx v in
		true
	else
		(* raise Halt *)
		let _ = if debugflag then 
				debug_print_string "Bitmap not set: Raise Halt\n" 
			else true in
		false
 
    else if  (lte addr ustackstart) && (gt addr (read "rbp" env))  then
	(* Address belongs to older stack frames *)  
	let isbitmapset = get_bitmap_set addr buf base  wbmapstart uheapstart ustackstart in
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
    else if (lte addr (read "rbp" env)) && (gte addr (read "rsp" env))  then
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
			let _ = debug_print_string (to_string (read "rbp" env)) in
			let _ = debug_print_string "\n" in
			let _ =  debug_print_string "Stack Pointer: " in
			let _ = debug_print_string (to_string (read "rsp" env)) in
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

 (* post-condition:
	A call is successfull only if it is present in calltable
	A jump is successfull only if it belongs to current function
 *)
  let decode (iscalltarget:bool) (myprogram:program) (currentaddr:address) (targetaddr:address) (env:cpuregstate) (calltab:calltable): Pure (bool * (list stmt)) 
		(requires ((gte env.rbp env.rsp) == true) )
		(ensures (fun r -> if (iscalltarget && (fst r)) then 
					((search_func calltab targetaddr) == true)
				  else if ((not iscalltarget)&& (fst r)) then
					let funcname = get_function_given_address currentaddr myprogram in
					let funcname' = get_function_given_address currentaddr myprogram in
					(funcname = funcname')
				  else  True
			 )
	        ) = 
	let iscallable = search_func calltab targetaddr in
	if  iscallable && iscalltarget then
		let func_name = get_func_name calltab targetaddr in
		let func_attr = get_func_attributes calltab func_name in
		
		let ispublic = begin match func_attr with
				| Public -> true
				| Private -> false
				end in
		if ispublic then
			(* If number of arguments is more than 4, 
			  check that stack is atleast the size of remaining arguments
			 *)	
			let numberargs = get_arguments_number calltab func_name in 
			if (numberargs > 4 ) then
				let framestart = read "rbp" env in
				let stacktop  = read "rsp" env in
				let framesize = (sub framestart stacktop) in
				if  ((cast_to_nat framesize) <  (numberargs - 4)) then
					(* raise Halt *)
					let _ = if debugflag then debug_print_string "Insufficient arguments: Raise Halt\n" else true in
					(false, [])
				else
					(* Fetches instructions from start to end *)
					let stlist = get_stmt_list func_name myprogram in
						(true, stlist)
			else
				
					(* Fetches instructions from start to end *)
					let stlist = get_stmt_list func_name myprogram in
						(true, stlist)
		(* private functions. We ignore the calling convention *)
		else
		(* Fetches instructions from start to end *)
		let stlist = get_stmt_list func_name myprogram in
			(true, stlist)
	else if (not iscallable) && iscalltarget then
		(* raise Halt *)
		let _ = if debugflag then debug_print_string "Illegal Call: Raise Halt" else true in
			(false, [])
	else (* jump target *)
		let funcname = get_function_given_address currentaddr myprogram in
		let funcname' = get_function_given_address currentaddr myprogram in
		if (funcname = funcname') then
			let stlist = get_stmt_list_in_current_function targetaddr myprogram in
			(true, stlist)
		else
			(* raise Halt *)
			let _ = if debugflag then debug_print_string "invalid jump target: Raise Halt\n" else true in
			(false, [])
			
