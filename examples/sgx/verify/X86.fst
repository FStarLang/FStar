
(*--build-config
    options:--z3timeout 60 --max_fuel 60;
    other-files: ../Ast.fst ../Test.fst ../SGXState.fst
*)
module X86

open FStar.Int
open FStar.Buffer
open FStar.HST
open FStar.UInt64
open FStar.List.Tot
open FStar.IO
open Helper
open Ast
open Test
open SGXState

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

let read (regname:string) (env:cpuregstate) :(Tot dword)  =
	search_reg regname (get_reg_list env)

(* pre-condition: idx fits the size of UInt32
   		  idx is less than length of the buffer
 *)
let load (n:word) (addr:address) (buf: buffer dword) (base:address): ST dword
	(requires (fun h -> (gte addr base) /\ (let idx =(sub addr base) in (Int.size (UInt64.v idx) UInt32.n))
				/\ (let idx = (sub addr base) in ((UInt64.v idx) < (Buffer.length buf)))
				/\ live h buf)
				)
	(ensures (fun h0 r h1 -> live h1 buf))
	  =
       let idx = (sub addr base) in
       let wordidx = (cast_to_word idx) in
      		 Buffer.index buf wordidx 


let get_bitmap_set (addr:address) (buf:buffer dword) (base:address)  (wbmapstart:address) (uheapstart:address): STL bool 
	(requires (fun h -> (gte addr base) 
				/\ (gte uheapstart base) 
				/\ (let idx =(sub addr base) in (Int.size (UInt64.v idx) UInt32.n))
				/\ (let idx = (sub addr base) in ((UInt64.v idx) < (Buffer.length buf)))
				/\ live h buf)
	)
	(ensures (fun h0 r h1 -> live h1 buf)) =
		let bitmapoffset = get_bitmap_offset addr base wbmapstart uheapstart in 
		let value = load 1ul bitmapoffset buf base in
		let index = get_bitmap_index uheapstart addr in
		let mask = shift_left 1uL (cast_to_word index) (* prepare mask *) in
		if (eq (UInt64.logand value  mask) 1uL) then true else false

