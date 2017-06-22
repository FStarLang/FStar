open Manifest

let u_start = 0
let u_size = 100
let v_start = u_start + u_size
let v_size = 100
let u_heap_start = u_start
let u_heap_size = 50
let u_stack_size = 50
let u_stack_start = u_start + u_size (* stack grows downwards*)
let v_heap_size = 50
let v_stack_size = 50
let v_heap_start = v_start
let v_stack_start = v_start + v_size (* stack grows downwards*)


(* OCalls/ non-enclave public interfaces i.e., non-enclave functions  that can be invoked by enclave code *)

assume val non_enclave_entry_1 : int -> int -> int
assume val non_enclave_entry_2 : string -> int -> int


(* call table - record the function starting address and size of the function *)
let non_enclave_entry_1_address = 1000
let non_enclave_entry_1_size = 100


let non_enclave_entry_2_address = 1100
let non_enclave_entry_2_size = 100

(* helper function to get the exit address of function *)
let get_exit_address () = 2000
