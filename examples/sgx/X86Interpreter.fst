module X86Interpreter

open FStar.Mul
open FStar.Ghost
open FStar.HST
open FStar.Int.Cast
open FStar.UInt64
open FStar.Buffer
open Ast
open FStar.List

exception Halt

(* Fix these definitions *)
let lookup sgxenv key =  sgxenv key
let extend sgxenv key value = sgxenv
let get_register_string r = 
	begin match r with
	|Reg rs -> rs
	|_ -> raise Halt
	end 

val interpret_exp: exp -> (sgxmem->u64) -> u64
let interpret_exp e (sgxenv: sgxmem->u64) = begin match e with
 | Reg r -> lookup sgxenv (Register r)
 | Constant u -> u
end

val interpret: stmt -> (sgxmem->u64) -> (sgxmem->u64)
let rec interpret progstmt (sgxenv: sgxmem->u64) = begin match progstmt with
  | Skip -> sgxenv 
  | Store(ea, ed)-> let lea = interpret_exp ea sgxenv in
		     let leb = interpret_exp ed sgxenv  in
		     extend sgxenv (Memory lea) leb  
  | Load(r, ea)-> let lea = interpret_exp ea sgxenv in
		    let v = lookup sgxenv (Memory lea) in
		    let rs = get_register_string r in
		    extend sgxenv (Register rs) v  
  | Seq(li) -> fold_left (fun sgxenv elem ->interpret elem sgxenv) sgxenv li 
  | _   -> sgxenv
end

