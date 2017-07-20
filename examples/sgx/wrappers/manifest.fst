module Manifest

let nat64_max = 0x10000000000000000
type nat64 = i:nat{i <= nat64_max}

type argtype =
  | ANat64 : argtype
  | AChar: argtype
  | ABuffer: int->argtype
  
type calltable_entry =
  |Mkcalltable_entry : fname:string -> fstart_address : nat64 -> fsize:nat64 -> args: (list argtype) -> calltable_entry

type calltable = 
  | MkCalltable : calltable_start:nat64 -> calltable_size: nat64 -> entries: (list calltable_entry) -> calltable

type umemlayout =
 | MkUmemlayout :  base_start:nat64 -> base_size:nat64 ->
                   bitmap_address:nat64 -> bitmap_size:nat64 ->
		   ctable: calltable ->
		   code_start:nat64 -> code_size: nat64 ->
		   heap_start: nat64 -> heap_size:nat64 ->
		   stack_start:nat64 -> stack_size:nat64 -> umemlayout


val get_u_start (m:umemlayout) : (r:nat64)
let get_u_start (m:umemlayout) = m.code_start
let get_u_size (m:umemlayout) = m.code_size + m.heap_size + m.stack_size
let get_u_end (m:umemlayout) = m.stack_start

val get_bitmap_start (m:umemlayout) : (r:nat64)
let get_bitmap_start (m:umemlayout) = m.bitmap_address
let get_bitmap_size (m:umemlayout) = m.bitmap_size

let get_calltable_start (m:umemlayout) = m.ctable.calltable_start
let get_code_start (m:umemlayout) = m.code_start
let get_code_size (m:umemlayout) = m.code_size

let get_heap_start (m:umemlayout) = m.heap_start
let get_heap_size (m:umemlayout) = m.heap_size
let get_stack_start (m:umemlayout) = m.stack_start
let get_stack_size (m:umemlayout) = m.stack_size

let address_within_procedure (fname:string) (dst:nat64) (env:umemlayout) = true

val is_inside_u_region (addr:nat64) (u:umemlayout) : bool
let is_inside_u_region (addr:nat64) (u:umemlayout) = ( addr < ((get_u_start u) + (get_u_size u))) && ( addr >= (get_u_start u))  



