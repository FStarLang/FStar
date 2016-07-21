module X86Interpreter

open FStar.UInt64
open FStar.Buffer
open FStar.List
open Ast
open LowInterpreter
open Helper
open Prims


val lookup: (sgxmem->u64)->sgxmem -> u64
val extend: (sgxmem -> u64)->sgxmem->u64 ->(sgxmem->u64)
(* Fix these definitions *)
let lookup sgxenv key =  sgxenv key
let extend sgxenv key value = sgxenv
let get_register_string r = 
	begin match r with
	|RegExp rs -> rs
	|_ -> raise Halt
	end 


(* Takes in an assembly address and converts it to low* offset *)
let translate_address sgxaddr= 
 	let tmp = (FStar.UInt64.sub sgxaddr sgxbitmapaddr) in
 	LowMemExp tmp

let translate_reg e = match e with
 | RegExp r -> LowVarExp r
 | ConstantExp n -> LowConstantExp n 

val interpret_exp: exp -> (sgxmem->u64) -> u64
let interpret_exp e (sgxenv: sgxmem->u64) = begin match e with
 | RegExp r -> lookup sgxenv (Register r)
 | ConstantExp u -> u
end

val interpret: stmt -> (sgxmem->u64) -> (lowsgxmem->u64) ->((sgxmem->u64)*(lowsgxmem->u64))
let rec interpret (progstmt:stmt) (sgxenv:sgxmem->u64) (lowsgxenv:lowsgxmem->u64) = begin match progstmt with
  | Skip -> (sgxenv, lowsgxenv)
  | Store(n, ea, ed)-> let vea = interpret_exp ea sgxenv in
		    let ved = interpret_exp ed sgxenv  in
		    let sgxenv' = extend sgxenv (Memory vea) ved  in

		    let lea = translate_address vea in
		    let led = translate_reg ed in
		    let lowsgxenv' = low_interpret (LowStore (n, lea, led)) lowsgxenv in	
		    (sgxenv', lowsgxenv')
  | Load(r, n, ea)->   let vea = interpret_exp ea sgxenv in
		    let v = lookup sgxenv (Memory vea) in
		    let rs = get_register_string r in
		    let sgxenv' = extend sgxenv (Register rs) v  in

		    let lea = translate_address vea in
		    let lr = translate_reg r in
		    let lowsgxenv' = low_interpret (LowLoad (lr, n, lea)) lowsgxenv in	
		    (sgxenv', lowsgxenv')
  | Seq(li) -> fold_left (fun envpair elem ->interpret elem (fst envpair) (snd envpair)) (sgxenv, lowsgxenv) li 
  | _   ->(sgxenv, lowsgxenv)
end

