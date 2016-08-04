
module Util
open FStar.UInt64
open FStar.IO
open FStar.Buffer
open Ast


val cast_to_word: address -> Tot word
let cast_to_word  _ = 0ul
(*
   Bitmap layout
  ==============
	         ____________________
		| 8-bytes /64-bits   |
		+____________________+
bitmapstart->	|bbbbbbb.......bbbbb |
		+____________________+
bitmapoffset->	|bbbbbbb.......bbbbb |
		|  |    	     |
		|  idx    	     |
		+____________________+

 Each entry is a 8 bytes long and each bit represents if the corresponding 64-bytes at an 
 address(computed by the formula below) is writable.
Each offset represents the bit array for 64 64-bit addresses.
 
 To obtain address represented index 'idx' at 'bitmapoffset' is given as:
	address = ((bitmapoffset * 64) + idx) + enclave_start_address

 To check if 'addr' is writable, compute the index 'idx' as follows:
	bitmapoffset  = (addr - enclave_start_address) / 64
	idx 	      = (addr - enclave_start_address) % 64

 Stack Layout
 ============
	 	 ____________________
		| 8-bytes /64-bits   |
		+____________________+___
framepointer->	|bbbbbbb.......bbbbb |   |
		+____________________+   |
		|bbbbbbb.......bbbbb |   |--> current stack frame
		|____________________|   | stackpointer < framepointer
		|bbbbbbb.......bbbbb |   |
stackpointer->	+____________________+___|

rbp = frame pointer
rsp = stack pointer

*)

val get_address_represented_in_bitmap:address->address->address->Tot address
let get_address_represented_in_bitmap base bitmapstart addr = 
	let bitmapoffset = (UInt64.sub addr bitmapstart) in
	let tmp = (UInt64.mul bitmapoffset 64uL) in
	(* Not including index, since a store can operate only on 8byte granularity
	  Optimize it later to get precise address
	*)
	let addroffset = (UInt64.add tmp base) in
	 addroffset

val get_bitmap_set :address->address->address->Tot bool
let get_bitmap_set base bitmapstart addr = true

val get_func_name :(buffer dword) -> address->Tot string
let get_func_name calltable instraddr = "main"

let invert_stmt s = match s with
 |Seq(_, li) -> li
 | _ -> [s]

let rec print_stmt (stli:list stmt) :Tot bool = match stli with
  | [] -> debug_print_string "end-of-stament-list\n" 
  | (Skip iaddr)::tail -> let _ = debug_print_string "skip\n" in print_stmt tail
  | (Store(iaddr, _, _, _))::tail-> let _ = debug_print_string "store\n" in print_stmt tail
  | (Load (iaddr, _, _, _))::tail-> let _ = debug_print_string "load\n" in print_stmt tail
  | (Call (iaddr, _))::tail-> let _ = debug_print_string "call\n" in print_stmt tail
  | (If (iaddr, _, _, _))::tail -> let _ = debug_print_string "if\n" in print_stmt tail
  | (Assign (iaddr, _, _))::tail-> let _ = debug_print_string "assign\n" in print_stmt tail
  | (Jump (iaddr, _))::tail -> let _ = debug_print_string "jump\n" in print_stmt tail
  | (Return iaddr)::tail -> let _ = debug_print_string "return\n" in print_stmt tail
 
let rec print_prog (myprogram:program): Tot bool = match myprogram with
 |[] -> debug_print_string "end-of-program\n" 
 |(fname, stli)::tail -> let _ = debug_print_string "FUNCTION: \n" in
			 let _ = print_stmt (invert_stmt stli) in
			 print_prog tail

val get_stmt_list : string->program->Tot (list stmt) 
let get_stmt_list funcname myprogram =
	let rec loop (fli:program): Tot (list stmt) = begin match fli with
	 |[] -> let _ = debug_print_string funcname in [] (* Ideally throw error *)
	 |(fname, stli)::tail -> if fname = funcname then (invert_stmt stli) else loop tail
	end in
	let stli = loop myprogram in
	stli


(* Returns the name of the function corresponding to this address *)
let get_function_given_address (instraddr:address) (myprogram:program) =
	let rec loop (fli:program): Tot string = begin match fli with
	 |[] -> "" (* Ideally throw error *)
	 |(fname, stli)::tail -> 
		let rec search_ins (stli:list stmt):Tot bool = begin match stli with 
			  | [] -> false
			  | (Skip iaddr)::tail 
			  | (Store(iaddr, _, _, _))::tail
			  | (Load (iaddr, _, _, _))::tail
			  | (Call (iaddr, _))::tail
			  | (If (iaddr, _, _, _))::tail 
			  | (Assign (iaddr, _, _))::tail
			  | (Jump (iaddr, _))::tail 
			  | (Return iaddr)::tail -> if (eq instraddr iaddr) then true else search_ins tail
			end
		in 
		let instrexists = search_ins (invert_stmt stli) in
		if instrexists then fname else loop tail
	end in
	loop myprogram 

(* Returns the list of stmt from the given address to end of current function *)
val get_stmt_list_in_current_function : address ->program->Tot (list stmt) 
let get_stmt_list_in_current_function instraddr myprogram =
	let funcname = get_function_given_address instraddr myprogram in
	let stli = get_stmt_list funcname myprogram in
	let rec search_ins (stli:list stmt):Tot (list stmt) = begin match stli with 
		  | [] -> []
		  | (Skip iaddr)::tail 
		  | (Store(iaddr, _, _, _))::tail
		  | (Load (iaddr, _, _, _))::tail
		  | (Call (iaddr, _))::tail
		  | (If (iaddr, _, _, _))::tail 
		  | (Assign (iaddr, _, _))::tail
		  | (Jump (iaddr, _))::tail 
		  | (Return iaddr)::tail -> if (eq instraddr iaddr) then stli else search_ins tail
		end
	in search_ins stli 

val search_func: (buffer dword) -> address -> Tot bool
let search_func calltable instraddr = true
