module Manifest

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HyperStack.ST

module HH = FStar.HyperHeap

let nat64_max = 0x10000000000000000
type nat64 = i:nat{i <= nat64_max}

type argtype =
  | ANat64 : argtype
  | AChar: argtype
  | AVoid: argtype
  | ABuffer: argtype -> argtype
  
type calltable_entry =
  |Mkcalltable_entry : fname:string -> fstart_address : nat64 -> fsize:nat64 -> args: (list argtype) -> (ret: argtype) -> calltable_entry

type calltable = 
  | MkCalltable : calltable_start:nat64 -> calltable_size: nat64 -> entries: (list calltable_entry) -> calltable

let color = 0

(* Enclave and non-Enclave regions *)
let (enclave_regn: rid{is_eternal_color (HH.color enclave_regn)}) = new_colored_region HH.root (color -1)

// Shared by enclave and non-enclave components to exchange arguments
let (host_regn:rid{is_eternal_color (HH.color host_regn)}) = new_colored_region HH.root (color - 2)

(* U component *)
let (u_mem:rid{is_eternal_color (HH.color u_mem)} )  = new_colored_region enclave_regn (color-3)

let (u_code:rid{is_eternal_color (HH.color u_code)}) = new_colored_region u_mem (color-4)
let (u_heap:rid{is_eternal_color (HH.color u_heap)}) = new_colored_region u_mem (color-5)

(* V component *)
let (v_mem:rid{is_eternal_color (HH.color v_mem)})  = new_colored_region enclave_regn (color-6) 
let (v_heap:rid{is_eternal_color (HH.color v_heap)}) = new_colored_region v_mem (color-7) 

  


