
module Util
open FStar.UInt64

let u64 = UInt64.t

val cast_to_nat: u64 -> nat
let cast_to_nat  i = 0

(*
  Bitmap layout
	 	_____________________
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
*)

val get_address_represented_in_bitmap:nat->nat->nat->nat
let get_address_represented_in_bitmap base bitmapstart addr = 
	let bitmapoffset = (addr - bitmapstart) in
	let tmp = (op_Multiply bitmapoffset 64) in
	(* Not including index, since a store can operate only on 8byte granularity
	  Optimize it later to get precise address
	*)
	let addroffset = (tmp+base) in
	 addroffset
