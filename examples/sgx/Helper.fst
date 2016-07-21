module Helper
open FStar.UInt64
open FStar.Mul
open FStar.Buffer 

let int_of_string s = of_string s


let u32 = UInt32.t
let u64 = UInt64.t

(* Some random values for now, the information should actually come
 from parsing low* and assembly manifests
*)
let lowsgxmemorysize:u32 = 4096ul
let lowsgxmemory = create 0uL lowsgxmemorysize
 

let sgxbitmapaddr:u64 = 0x0uL
let sgxuheapaddr:u64 = 0x0uL 
let sgxustackaddr:u64 = 0x0uL 
let sgxucodeaddr:u64 = 0x0uL 
let sgxucodesize:u64  = 0x0uL

let lowsgxmemstart = 0x0uL
let lowsgxbitmapoffset = lowsgxmemstart 
let lowsgxuheapoffset = 0x0uL 
let lowsgxustackoffset = 0x0uL 
let lowsgxustacksize = 0x0uL 

(* Functions determining if assembly address falls in one of the regions
 *)
val issgxaddrinbitmap: u64 -> bool
let issgxaddrinbitmap sgxaddr = 
 if (lt sgxaddr sgxuheapaddr) && (gt sgxaddr sgxbitmapaddr) then
	true
 else
	false

	  
val issgxaddrinuheap: u64 -> bool
let issgxaddrinuheap sgxaddr = 
 if (lt sgxaddr sgxustackaddr) && (gt sgxaddr sgxuheapaddr) then
	true
 else
	false

val issgxaddrinustack: u64 -> bool
let issgxaddrinustack sgxaddr = 
 if (lt sgxaddr sgxucodeaddr) && (gt sgxaddr sgxustackaddr) then
	true
 else
	false

	  
val issgxaddrinucode: u64 -> bool
let issgxaddrinucode sgxaddr = 
 if (gt sgxaddr sgxucodeaddr) && (lt sgxaddr (add sgxucodeaddr sgxucodesize)) then
	true
 else
	false

(* Functions determining if low* offset falls in 
  one of the low* memory regions
 *)
val islowsgxoffsetinbitmap: u64 -> bool
let islowsgxoffsetinbitmap lowsgxoffset = 
 if (lt lowsgxoffset lowsgxuheapoffset) && (gt lowsgxoffset lowsgxbitmapoffset) then
	true
 else
	false
	  
val get_bitmap_offset:u64->u64 
let get_bitmap_offset lowsgxaddr =
	(UInt64.sub lowsgxaddr lowsgxbitmapoffset)

val islowsgxoffsetinuheap: u64 -> bool
let islowsgxoffsetinuheap lowsgxoffset = 
 if (lt lowsgxoffset lowsgxustackoffset) && (gt lowsgxoffset lowsgxuheapoffset) then
	true
 else
	false

val islowsgxoffsetinustack: u64 -> bool
let islowsgxoffsetinustack lowsgxoffset = 
 if (lt lowsgxoffset (add lowsgxustackoffset  lowsgxustacksize)) && (gt lowsgxoffset lowsgxustackoffset) then
	true
 else
	false

	  
(* Support for callbitmap? TBD *)

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
val bitmap: u64->u64

let get_address_represented_in_bitmap bitmapoffset idx  = 
	let tmp = (mul bitmapoffset  64uL) in
	let addroffsetinbitmap = (add tmp idx) in
	let addroffset = (add addroffsetinbitmap lowsgxmemstart) in
	 addroffset
