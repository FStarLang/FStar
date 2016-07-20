module LowInterpreter 

open Ast
open FStar.UInt64
open FStar.Buffer 
open FStar.List

let u64 = UInt64.t

val lowlookup: (lowsgxmem->u64)->lowsgxmem -> u64
val lowextend: (lowsgxmem -> u64)->lowsgxmem->u64 ->(lowsgxmem->u64)

(* Fix these definitions *)
let lowlookup lowsgxenv key =  lowsgxenv key
let lowextend lowsgxenv key value = lowsgxenv

let get_var_string r = 
	begin match r with
	|LowVarExp vs -> vs
	|_ -> raise Halt
	end 

let rec low_interpret_exp  le lowsgxenv = match le with 
 | LowVarExp v -> lowlookup lowsgxenv (LowRegister v)
 | LowMemExp offset -> lowlookup lowsgxenv (LowMemory offset)
 | LowConstantExp n -> n

let rec low_interpret progstmt lowsgxenv = match progstmt with 
  | LowSkip -> lowsgxenv 
  | LowStore(lea, led)-> let vea = low_interpret_exp lea lowsgxenv in
		     let veb = low_interpret_exp led lowsgxenv  in
		     lowextend lowsgxenv (LowMemory vea) veb  
  | LowLoad(lv, lea)-> let vea = low_interpret_exp lea lowsgxenv in
		    let value = lowlookup lowsgxenv (LowMemory vea) in
		    let vs = get_var_string lv in
		    lowextend lowsgxenv (LowRegister vs) value  
  | LowSeq(li) -> fold_left (fun lowsgxenv elem ->low_interpret elem lowsgxenv) lowsgxenv li 
  | _   -> lowsgxenv

