
module SdkAPI

open FStar.HyperStack
open FStar.ST
open Manifest

module HH = FStar.HyperHeap

(* Modeling enclave instructions - In progress*)
assume val eexit : emode:bool -> u_mem:HH.rid->v_mem:HH.rid -> uv_shared_buf:HH.rid -> non_enclave_regn: HH.rid-> exitaddress:(rref non_enclave_regn int) -> Heap  unit 
  (requires (fun _ -> heap_only m /\ emode = true))
  (ensures  (fun _ _ _ -> emode = false))

assume val eenter : emode:bool -> u_mem:HH.rid->v_mem:HH.rid -> uv_shared_buf:HH.rid -> non_enclave_regn: HH.rid-> exitaddress:(rref non_enclave_regn int) -> Heap  unit 
  (requires (fun _ -> heap_only m /\ emode = false))
  (ensures  (fun _ _ _ -> emode = true))

(* This is the first entry point inside an enclave. Using eenter should switch the control to this function *)
assume val generic_enclave_entry : emode:bool -> u_mem:HH.rid->v_mem:HH.rid -> uv_shared_buf:HH.rid -> non_enclave_regn: HH.rid-> exitaddress:(rref non_enclave_regn int) -> Heap  unit 
  (requires (fun _ -> heap_only m /\ emode = true ))
  (ensures  (fun _ _ _ -> True))


(* 2 Design Choices for Wrappers
	1. Copy the arguments from uv_shared_buf to v_mem and then invoke CallEnclaveHost which then is verified using Vale
	2. Copy the arguments directly to non-enclave memory and do all the CallEnclaveHost () functionality. This will reduce the number of copies involved. 
*)


type struct_for_wrapper1 =
 | Mk_struct_1 of int * int
(* 
  - modifies only non_enclave_regn and uv_shared_buf 
  - Wrapper for non_enclave_entry_point_1 : int -> int-> int
  - manifest has the function type signature. so the wrapper knows how many bytes to read/write for args/ret 
*)
val callenclavehost_wrapper_1: emode: bool-> u_mem:HH.rid->v_mem:HH.rid -> uv_shared_buf:HH.rid -> non_enclave_regn: HH.rid->arg1: (rref uv_shared_buf int)-> arg2:(rref uv_shared_buf int)->rret:(rref uv_shared_buf int)  ->Heap unit
			(requires (fun m -> heap_only m /\ emode = true ))
			(ensures (fun m0 r m1 -> modifies_transitively (Set.singleton non_enclave_regn) m0 m1 ))
let callenclavehost_wrapper_1 emode u_mem v_mem uv_shared_buf non_enclave_regn arg1 arg2 =
        (*
		- copy the arguments from uv_shared_buf to v_mem
		- which stack should wrapper use? In reality this is also responsible for switching the stack pointers between
		  U and V. But since we are not modeling U's stack, how to verify that functionality?
 	*)
	let nbytes_to_read = 8 in
	let nbytes_to_return = 4 in
	let nbytes_to_allocate = nbytes_to_read + nbytes_to_return in
	(* read from uv_shared_buf *)
	let argv1 = op_Bang uv_shared_buf arg1 in
	let argv2 = op_Bang uv_shared_buf arg2 in
	let struct_1 = Mk_struct_1 (argv1, argv2) in
	
	
	(* create a reference in non_enclave_regn and copy the arguments to non_enclave_regn *)
	let non_enclave_arg = ralloc non_enclave_regn  struct_1 in

	(* IMPORTANT: instead of using a struct, use a sequence of bytes like char [] and copy the arguments.
	  Though this opens a plethora of endianness issues, this is probably the only way to access
	  return value as callenclavehost() does not know where exactly return pointer is.
	  Also this is compliant with SGX SDK API for callenclaveHost
	*) 
	let argv1_char = convert_to_bytes argv1 in
	let argv2_char = convert_to_bytes argv1 in
	let arg_char = List.concate argv1_char argv2_char in
	let ret_char = List.concate arg_char (mklist nbytes_to_return) in
	
	let non_enclave_arg_as_char = ralloc non_enclave_regn ret_char in
	 

	(* Get the exit address from manifest *)
	let exitaddress = get_exit_address () in

	(* call eexit - should it just return? In the actual SGX implementation *)
	let _ = callenclavehost emode  u_mem v_mem uv_shared_buf non_enclave_regn exitaddress in
	let ret_upd_char = op_Bang non_enclave_regn non_enclave_arg_as_char in
	let ret_val = (nth ret_upd_char nbytes_to_read) in
	
	(* Copy the return value back to uv_shared_buf *)
	let _ = op_Colon_Equals uv_shared_buf rret ret_val in 
	()

val init_sgx_memory_model : unit -> Heap (HH.rid * HH.rid * HH.rid * HH.rid) 
  (requires (fun m -> heap_only m))
  (ensures  (fun m0 r m1 -> modifies_transitively (Set.singleton m0.tip) m0 m1 ))
let init_sgx_memory_model () =
  let m = get() in
  let color = 0 in
  HH.root_has_color_zero ();

  (* Enclave and non-Enclave regions *)
  let enclave_regn = new_colored_region HH.root (color -1) in
  // Shared by enclave and non-enclave components to exchange arguments
  let non_enclave_regn = new_colored_region HH.root (color - 2) in

  (* U component *)
  let u_mem  = new_colored_region enclave_regn (color-3)  in

  (* V component *)
  let v_mem  = new_colored_region enclave_regn (color-4)  in
  let v_heap = new_colored_region v_mem (color-5)  in

  // Shared by U and V components to exchange arguments
  // Only wrappers access this region
  let uv_shared_buf= new_colored_region enclave_regn (color-6)  in
  (u_mem, v_mem, uv_shared_buf, non_enclave_regn)
  
val enclavemain : unit -> Heap unit
		(requires (fun m -> heap_only m))
		(ensures  (fun m0 r m1 -> True))
let enclavemain () = 
	let u_mem, v_mem, uv_shared_buf, non_enclave_regn = init_sgx_memory_model () in
	()
