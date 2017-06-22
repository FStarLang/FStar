
module SdkAPI

open FStar.HyperStack
open FStar.ST
open Manifest

module HH = FStar.HyperHeap


(* 
  - modifies only non_enclave_regn and uv_shared_buf 
  - Wrapper for non_enclave_entry_point_1 : int -> int-> int
  - manifest has the function type signature. so the wrapper knows how many bytes to read/write for args/ret 
*)
val callenclavehost_wrapper_1: emode: bool-> u_mem:HH.rid->v_mem:HH.rid -> uv_shared_buf:HH.rid -> non_enclave_regn: HH.rid->arg1: (rref uv_shared_buf int)-> arg2:(rref uv_shared_buf int) ->Heap unit
			(requires (fun m -> heap_only m /\ emode = true ))
			(ensures (fun m0 r m1 -> modifies_transitively (Set.singleton non_enclave_regn) m0 m1 ))
let callenclavehost_wrapper_1 mode u_mem v_mem uv_shared_buf non_enclave_regn arg1 arg2 =
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

	
	(* create a reference in non_enclave_regn and copy the arguments to a char * array of size nbytes_to_allocate *)
	(* TODO:  Create a sequence and allocate a reference for it *)
	let non_enclave_arg = ralloc non_enclave_regn  0 in
	(* eexit *)
	()

(* Modeling an enclave exit *)
assume eexit : emode:bool -> Heap  (HH.rid * HH.rid * HH.rid * HH.rid) 
  (requires (fun _ -> heap_only m /\ emode = true))
  (ensures  (fun _ _ _ -> emode = false))

(* Modeling an enclave entry *)
assume eenter : emode:bool -> Heap  (HH.rid * HH.rid * HH.rid * HH.rid) 
  (requires (fun _ -> heap_only m /\ emode = false))
  (ensures  (fun _ _ _ -> emode = true))

(* This is the first entry point inside an enclave. Using eenter should switch the control to this function *)
assume generic_enclave_entry : emode:bool -> Heap  (HH.rid * HH.rid * HH.rid * HH.rid) 
  (requires (fun _ -> heap_only m /\ emode = true ))
  (ensures  (fun _ _ _ -> True))



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
