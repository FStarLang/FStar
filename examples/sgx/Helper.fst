module Helper
open FStar.UInt64
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

	  
(* Support for callbitmap *)

