
module Util
open FStar.UInt64
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
let get_func_name calltable instraddr = "dummy"

val get_stmt_list : string->program->Tot (list stmt) 
let get_stmt_list funcname myprogram = []

val search_func: (buffer dword) -> address -> Tot bool
let search_func calltable instraddr = true
