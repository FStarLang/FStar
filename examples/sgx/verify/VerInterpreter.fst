module VerInterpreter

open FStar.Int
open FStar.Heap
open FStar.HyperStack
open FStar.Buffer
open FStar.UInt64
open FStar.List.Tot
open FStar.IO
open VerUtil
open VerAst
open VerTest
open VerSGXState

exception Halt

module HS = FStar.HyperStack

type u64 = UInt64.t
type u32 = UInt32.t

(*
val STX.Halt: unit -> STX 'a 
val STX.Load : unit -> buffer ... -> STX dword
val STX.Store: unit -> buffer ... -> STX unit
*)

assume val debugflag:bool

#set-options "--z3rlimit 50"
noeq type mmem =
  | C: base:address
       -> ucodestart:address
       -> wbmapstart:address
       -> uheapstart:address{UInt.fits (UInt64.v uheapstart) UInt32.n}
       -> ustackstart:address{UInt.fits (UInt64.v ustackstart) UInt32.n}
       -> ucodesize:u64
       -> wbmapsize:u32{UInt.fits (UInt32.v wbmapsize) UInt16.n}
       -> uheapsize:u64{UInt.fits (UInt64.v uheapsize) UInt32.n}
       -> ustacksize:u64{UInt.fits (UInt64.v ustacksize) UInt32.n}
       -> buf:buffer dword{ucodestart >=^ base        /\
                          wbmapstart >=^ ucodestart  /\
                          uheapstart >=^ wbmapstart  /\
                          ustackstart >=^ uheapstart /\
			  UInt.fits (UInt64.v (ustackstart -^ base)) UInt32.n                 /\
                          UInt64.v (ustackstart -^ base) < Buffer.length buf                  /\
			  UInt32.v wbmapsize < UInt64.v ((ustackstart -^ uheapstart) /^ 64uL) /\
			  lastaddr_less_than_stackaddress wbmapsize uheapstart ustackstart <=^ ustackstart /\
			  ustackstart >=^ ustacksize /\
			  ustackstart -^ ustacksize >=^ uheapstart +^ uheapsize}
       -> mmem
#reset-options

let addr_in_range (addr:address) (m:mmem) =
  gte addr m.base /\
  (let idx = addr -^ m.base in
   Int.size (UInt64.v idx) UInt32.n /\
   UInt64.v idx < Buffer.length m.buf)

(* pre-condition: idx fits the size of UInt32
   		  idx is less than length of the buffer
 *)
let load (n:word) (addr:address) (m:mmem)
  :STL dword
       (requires (fun h -> addr_in_range addr m /\
			live h m.buf))
       (ensures (fun h0 r h1 -> h1 == h0             /\
                             addr_in_range addr m /\
                             live h0 m.buf        /\ 
                             r == Buffer.get h0 m.buf (UInt32.v (cast_to_word (addr -^ m.base)))))
  = let idx = addr -^ m.base in
    let wordidx = cast_to_word idx in
    Buffer.index m.buf wordidx

#reset-options "--z3rlimit 100"
let get_bitmap_set_pre (h:HS.mem) (addr:address) (m:mmem)
  =  addr_in_range addr m   /\
     addr >=^ m.uheapstart  /\
     m.ustackstart >=^ addr /\
     live h m.buf

let get_bitmap_set_pure (h:HS.mem) (addr:address) (m:mmem{get_bitmap_set_pre h addr m})
  :GTot bool =
  let bitmapoffset = get_bitmap_offset addr m.base m.wbmapstart m.uheapstart m.ustackstart in 
  let bufindex = bitmapoffset -^ m.base in
  let value = Buffer.get h m.buf (UInt64.v bufindex) in
  let index = get_bitmap_index addr m.base m.wbmapstart m.uheapstart m.ustackstart in 
  let wordidx = cast_to_word index  in
  let mask = 1uL <<^ wordidx (* prepare mask *) in
  UInt64.logand value mask =^ 1uL

let get_bitmap_set (addr:address) (m:mmem)
  :STL bool
      (requires (fun h0 -> get_bitmap_set_pre h0 addr m))
      (ensures (fun h0 r h1 -> h1 == h0                     /\
                            get_bitmap_set_pre h0 addr m /\
                            r = get_bitmap_set_pure h0 addr m))
  = let bitmapoffset = get_bitmap_offset addr m.base m.wbmapstart m.uheapstart m.ustackstart in 
    let value = load 1ul bitmapoffset m in

    let h = ST.get () in
    let index = get_bitmap_index addr m.base m.wbmapstart m.uheapstart m.ustackstart in 
    let wordidx = cast_to_word index  in
    let mask = 1uL <<^ wordidx (* prepare mask *) in
    UInt64.logand value mask =^ 1uL
#reset-options

let heap_or_active_stack (addr:address) (m:mmem) :Tot bool =
  addr >=^ m.uheapstart && addr <=^ m.ustackstart

//#set-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2"
#set-options "--z3rlimit 100"
let store (n:word) (addr:address) (v:dword) (env:cpuregstate) (m:mmem)
  : STL bool 
	(requires (fun h -> addr_in_range addr m /\
			 m.ustackstart >=^ addr /\
		         (* rbp and rsp are always in stack ranges *)
			 (let stackend = m.ustackstart -^ m.ustacksize in
			  env.rbp >=^ stackend && env.rbp <=^ m.ustackstart &&
			  env.rsp >=^ stackend && env.rsp <=^ m.ustackstart) /\
		         env.rbp >=^ env.rsp /\
			 live h m.buf))
	(ensures (fun h0 r h1 -> live h0 m.buf /\ live h1 m.buf /\ modifies_1 m.buf h0 h1 /\
	                      addr_in_range addr m /\
  			      m.ustackstart >=^ addr /\
			      (let stackend = m.ustackstart -^ m.ustacksize in
			       env.rbp >=^ stackend && env.rbp <=^ m.ustackstart &&
			       env.rsp >=^ stackend && env.rsp <=^ m.ustackstart) /\
		               env.rbp >=^ env.rsp /\
			       ((heap_or_active_stack addr m /\ r) ==>
			        get_bitmap_set_pure h0 addr m))) =
	(*                       addr_in_range addr m /\ *)
	(* 			/\ (gte addr base)  *)
	(* 			/\ (gte ucodestart base) *)
	(* 			/\ (gte wbmapstart ucodestart) *)
	(* 			/\ (gte ustackstart uheapstart) *)
	(* 			/\ (gte uheapstart wbmapstart)  *)
	(* 			/\ (gte ustackstart addr) *)
	(* 			/\ (let idx =(sub addr base) in (Int.size (UInt64.v idx) UInt32.n)) *)
	(* 			/\ ((UInt64.v (sub ustackstart base)) < (Buffer.length buf))  *)
	(* 			(\* *)
	(* 			(\* if address is stack or heap and the store is successful, then it should be writable *\) *)
	(* 			/\ (if (heap_or_active_stack addr uheapstart ustackstart ) && r then  *)
	(* 				((get_bitmap_set_pure h0 addr buf base wbmapstart uheapstart ustackstart) == true) *)
	(* 			   else True *)
	(* 			   ) *)
	(* 			*\) *)
	(* 			/\ (if (gte addr ucodestart) && (lte addr wbmapstart) then *)
	(* 					(r==false) *)
	(* 			    else True *)
	(* 			   ) *)
	(* 			(\* rbp and rsp are always in stack ranges *\) *)
	(* 			/\ (Int.size (UInt64.v ustackstart) UInt32.n)   *)
	(* 			/\ (Int.size (UInt64.v ustacksize) UInt32.n)   *)
	(* 			/\ ( let stackend = (add ustackstart  ustacksize) in *)
	(* 				(gte env.rbp stackend) && (lte env.rbp ustackstart) && (gte env.rsp stackend) && (lte env.rsp ustackstart)  *)
	(* 			   ) *)
	(* 			 (\* rbp >= rsp *\) *)
	(* 			/\ ((gte env.rbp env.rsp) == true) *)
	(* 	 ) *)
	(* ) = *)
	
      (* Code section is not writable *)
     let C base ucodestart wbmapstart uheapstart ustackstart ucodesize wbmapsize uheapsize ustacksize buf = m in
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
	let isbitmapset = get_bitmap_set addr m in
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
    else admit ()




    (* else if  (lte addr ustackstart) && (gt addr (read "rbp" env))  then *)
    (* 	(\* Address belongs to older stack frames *\)   *)
    (* 	let isbitmapset = get_bitmap_set addr buf base  wbmapstart uheapstart ustackstart in *)
    (* 	if isbitmapset then *)
    (* 	       let idx = (sub addr base) in *)
    (* 	       let wordidx = (cast_to_word idx) in *)
    (* 	       let _ = if debugflag then  *)
    (* 				let _ =  debug_print_string "Updating older stack frame: " in *)
    (* 				let _ = debug_print_string (UInt32.to_string wordidx) in *)
    (* 				debug_print_string "\n" *)
    (* 			 else true in *)
    (*      	let _ = Buffer.upd buf wordidx v in *)
    (* 		true *)
    (* 	else *)
    (* 		(\* raise Halt *\) *)
    (* 		let _ = if debugflag then debug_print_string "Bitmap not set: Raise Halt\n" else true in *)
    (* 		false *)
    (* else if (lte addr (read "rbp" env)) && (gte addr (read "rsp" env))  then *)
    (* 	(\* Address belongs to current stack frames *\)   *)
    (* 	       let idx = (sub addr base) in *)
    (* 	       let wordidx = (cast_to_word idx) in *)
    (* 	       let _ = if debugflag then  *)
    (* 				let _ =  debug_print_string "Updating current stack frame: " in *)
    (* 				let _ = debug_print_string (UInt32.to_string wordidx) in *)
    (* 				debug_print_string "\n" *)
    (* 			 else true in *)
    (*            let _ = Buffer.upd buf wordidx v in *)
    (* 	       true *)
    (* else *)
    (* 	let _ = if debugflag then  *)
    (* 			let _ = debug_print_string "Something went wrong. Dump as follows:\n" in *)
    (* 			let _ =  debug_print_string "Address being written to: " in *)
    (* 			let _ = debug_print_string (to_string addr) in *)
    (* 			let _ = debug_print_string "\n" in *)
    (* 			let _ =  debug_print_string "Frame Pointer: " in *)
    (* 			let _ = debug_print_string (to_string (read "rbp" env)) in *)
    (* 			let _ = debug_print_string "\n" in *)
    (* 			let _ =  debug_print_string "Stack Pointer: " in *)
    (* 			let _ = debug_print_string (to_string (read "rsp" env)) in *)
    (* 			let _ = debug_print_string "\n" in *)
    (* 			let _ =  debug_print_string "Base Address: " in *)
    (* 			let _ = debug_print_string (to_string base) in *)
    (* 			let _ = debug_print_string "\n" in *)
    (* 			let _ =  debug_print_string "Code Start: " in *)
    (* 			let _ = debug_print_string (to_string ucodestart) in *)
    (* 			let _ = debug_print_string "\n" in *)
    (* 			let _ =  debug_print_string "Bitmap Start: " in *)
    (* 			let _ = debug_print_string (to_string wbmapstart) in *)
    (* 			let _ = debug_print_string "\n" in *)
    (* 			let _ =  debug_print_string "Heap Start: " in *)
    (* 			let _ = debug_print_string (to_string uheapstart) in *)
    (* 			let _ = debug_print_string "\n" in *)
    (* 			let _ =  debug_print_string "Stack Start: " in *)
    (* 			let _ = debug_print_string (to_string ustackstart) in *)
    (* 			let _ =  debug_print_string "\nEnd-of-Dump\n" in *)
    (* 			debug_print_string "====================\n"  *)
    (* 		else true in *)
    (*     false	 *)

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
			
let get_register_name = function
 | Register r -> r
 | _ -> (* raise Halt *) ""


val eval: cpuregstate -> exp -> Tot dword
let eval (env:cpuregstate) = function
 | Register r ->  read r env
 | Constant n -> n

 let base = 1000uL 
 let ucodestart = 1100uL 
 let ucodesize =  99uL 
 let wbmapstart = 1200uL
 let wbmapsize = 99ul 
 let uheapstart = 1300uL 
 let uheapsize = 400uL 
 let ustacksize = 400uL 
 let ustackstart = (add (add uheapstart uheapsize) ustacksize) 
 let entry = 1200uL 
 let bufsize = add (sub ustackstart base) 2uL 
 let buf = push_frame (); Buffer.create 0uL (cast_to_word bufsize) 
 let calltab = parse_manifest () 
 let env = { rsp = ustackstart;
	     rbp = ustackstart;
	     rax = 0uL;
	     rbx = 0uL;
	     rcx = 0uL;
	     rdx = 0uL;
	     r8 = 0uL;
	     r9 = 0uL;
	  }
	

let rec step (debugflag:bool) (state:(bool*cpuregstate))  (myprogram:program) (instr:stmt) : STL (bool*cpuregstate)
					(requires (fun h ->	
							(* rbp and rsp take stack range *)
							( let stackend = (add ustackstart  ustacksize) in
								(gte env.rbp stackend) && (lte env.rbp ustackstart) && (gte env.rsp stackend) && (lte env.rsp ustackstart) 
				   			) 
							 (* rbp >= rsp *)
							/\ (gte env.rbp env.rsp) 
						  )
					)
					(ensures (fun h0 r h1 -> (if (not (fst state)) then
						 			((fst r)== false) /\ (((snd r) = (snd state)) == true) 
								  else
									True
								  ) 
								 /\ (gte env.rbp env.rsp)
						 )
					 ) 
	 = let env = (snd state) in 
	   let status = (fst state) in
	   if status = false then (false, env) else
match instr with 
  | Skip iaddr ->
       		let t = if debugflag then
				debug_print_string "Skip;\n"
       			else true in
		(true, env)
  | Add (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (add_underspec op1 op2) in
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
	 (true, env')
  | Sub (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (sub_underspec op1 op2) in
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
	 (true, env')
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
	 (true, env')
  | Mul (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
	let value = (mul_underspec op1 op2) in
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
	 (true, env')
  | Div (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
        if (UInt64.v op2 <> 0) then
	   	let value = (div_underspec op1 op2) in
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
	 		(true, env')
	else
		(false, env)
  | Mod (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
        if (UInt64.v op2 <> 0) then
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
		 (true, env')
	else
		(false, env)
  | Lsr (iaddr, ed, ea, eb) -> 
        let op1 = eval env ea in
        let op2 = eval env eb in 
        if (UInt.fits (UInt64.v op2) 32) then
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
	        (true, env')
	else
	 (false, env)
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
	 (true, env')
(*
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
  *)
  | Store(iaddr, n, ea, ev)-> 
       let addr = eval env ea in
       let v = eval env ev in 
       if (gte addr base) && (gte ustackstart addr) then
 (*

  | C: base:address
       -> ucodestart:address
       -> wbmapstart:address
       -> uheapstart:address{UInt.fits (UInt64.v uheapstart) UInt32.n}
       -> ustackstart:address{UInt.fits (UInt64.v ustackstart) UInt32.n}
       -> ucodesize:u64
       -> wbmapsize:u32{UInt.fits (UInt32.v wbmapsize) UInt16.n}
       -> uheapsize:u64{UInt.fits (UInt64.v uheapsize) UInt32.n}
       -> ustacksize:u64{UInt.fits (UInt64.v ustacksize) UInt32.n}
       -> buf:buffer dword{ucodestart >=^ base        /\

*)
		let sm = C base ucodestart wbmapstart uheapstart ustackstart ucodesize wbmapsize uheapsize ustacksize buf in
	       let status' = store n  addr v env sm  in
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
	       (status', env)
	else
		(false, env)
 | _ -> (status, env)
(*
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
		

*)
and helperfunc  (debugflag:bool)  (myprogram:program) (state:(bool*cpuregstate)) (elem:stmt): STL (bool*cpuregstate) 
					(requires (fun h ->	
							(* rbp and rsp take stack range *)
							( let stackend = (add ustackstart  ustacksize) in
								(gte env.rbp stackend) && (lte env.rbp ustackstart) && (gte env.rsp stackend) && (lte env.rsp ustackstart) 
				   			) 
							 (* rbp >= rsp *)
							/\ (gte env.rbp env.rsp) 
						  )
					)
					(ensures (fun h0 r h1 -> (if (not (fst state)) then
						 			((fst r)== false) /\ (((snd r) = (snd state)) == true) 
								  else
									True
								  ) 
								 /\ (gte env.rbp env.rsp)
						 )
					 ) 
					= step debugflag state myprogram elem 


and steps (debugflag:bool) (state:(bool*cpuregstate))  (myprogram:program) (instrlist:list stmt): STL (bool*cpuregstate)
					(requires (fun h ->	
							(* rbp and rsp take stack range *)
							( let stackend = (add ustackstart  ustacksize) in
								(gte env.rbp stackend) && (lte env.rbp ustackstart) && (gte env.rsp stackend) && (lte env.rsp ustackstart) 
				   			) 
							 (* rbp >= rsp *)
							/\ (gte env.rbp env.rsp) 
						  )
					)
					(ensures (fun h0 r h1 -> (if (not (fst state)) then
						 			((fst r)== false) /\ (((snd r) = (snd state)) == true) 
								  else
									True
								  ) 
								 /\ (gte env.rbp env.rsp)
						 )
					 ) 
					 = match instrlist with
|[] -> state
| xs::tail -> steps  debugflag  (helperfunc debugflag myprogram state xs) myprogram  tail 

