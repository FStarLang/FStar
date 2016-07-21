module LowInterpreter 

open Ast
open FStar.UInt64
open FStar.List
open Helper

let u64 = UInt64.t

val lowlookup: (lowsgxmem->u64)->lowsgxmem -> u64
val lowextend: (lowsgxmem -> u64)->lowsgxmem->u64 ->(lowsgxmem->u64)

(* FIXME: Map can be used instead. 
          If not fix these definitions to properly update the environment
 *)
let lowlookup lowsgxenv key =  lowsgxenv key
let lowextend lowsgxenv key value = lowsgxenv

val lowextend_helper: (lowsgxmem->u64)->u64->u64->(lowsgxmem->u64)
let lowextend_helper lowsgxenv offset value = 
	if (gt offset lowsgxmemstart) && (lt offset lowsgxbitmapoffset) then 
				let bitmapoffset = (sub offset lowsgxbitmapoffset) in 
				lowextend lowsgxenv (BitMapRange bitmapoffset) value
			else if (gt offset lowsgxbitmapoffset) && (lt offset lowsgxuheapoffset ) then 
				let uheapoffset = (sub offset lowsgxuheapoffset) in 
				lowextend lowsgxenv (UHeapRange uheapoffset) value
			else if (gt offset lowsgxuheapoffset ) && (lt offset lowsgxustackoffset) then 
				let ustackoffset = (sub offset lowsgxustackoffset) in 
				lowextend lowsgxenv (UStackRange ustackoffset) value
			else
				(* What should go here? *)
				raise Halt

let get_var_string r = 
	begin match r with
	|LowVarExp vs -> vs
	|_ -> raise Halt
	end 

(* Interprets a low* expression and returns the value. 
   Values are just u64 for now. Change this if required
 *)
let low_interpret_exp  le lowsgxenv = match le with 
 | LowVarExp v -> lowlookup lowsgxenv (LowRegister v)
 | LowMemExp offset -> if (gt offset lowsgxmemstart) && (lt offset lowsgxbitmapoffset) then 
				let bitmapoffset = (sub offset lowsgxbitmapoffset) in 
				lowlookup lowsgxenv (BitMapRange bitmapoffset)
			else if (gt offset lowsgxbitmapoffset) && (lt offset lowsgxuheapoffset ) then 
				let uheapoffset = (sub offset lowsgxuheapoffset) in 
				lowlookup lowsgxenv (UHeapRange uheapoffset)
			else if (gt offset lowsgxuheapoffset ) && (lt offset lowsgxustackoffset) then 
				let ustackoffset = (sub offset lowsgxustackoffset) in 
				lowlookup lowsgxenv (UStackRange ustackoffset)
			else
				(* What should go here? *)
				raise Halt
 | LowConstantExp n -> n

let get_lowmem_offset = function
 | LowMemExp offset -> offset
 |_ -> raise Halt

let rec low_interpret progstmt lowsgxenv = match progstmt with 
  | LowSkip -> lowsgxenv 
  | LowStore(n,lea, led)-> 

		     let offset = get_lowmem_offset lea in
		     let ved = low_interpret_exp led lowsgxenv  in
		     if islowsgxoffsetinbitmap offset then
			  let bitmapoffset = get_bitmap_offset offset in
			  let idx = 0uL in
			  let addroffset = get_address_represented_in_bitmap bitmapoffset idx  in

			  (* FIXME: check that addroffset belongs to current stack frame. How?? *)
			  let vea = low_interpret_exp lea lowsgxenv in
			  lowextend_helper lowsgxenv vea ved  
		     else if islowsgxoffsetinuheap offset then
			(* FIXME: Check for logic that bitmap is set *)
			     let vea = low_interpret_exp lea lowsgxenv in
			     lowextend_helper lowsgxenv vea ved  
		     else
				raise Halt	
			
  | LowLoad(lvar,n, lea)-> let value = low_interpret_exp lea lowsgxenv in
		    let lvs = get_var_string lvar in
		    lowextend lowsgxenv (LowRegister lvs) value  
  | LowSeq(li) -> fold_left (fun lowsgxenv elem ->low_interpret elem lowsgxenv) lowsgxenv li 
  | _   -> lowsgxenv

