
module SdkAPI

open FStar.HyperStack.ST
open Manifest
open FStar.Int8
open FStar.UInt32
open FStar.List.Tot.Base
open FStar.HyperStack

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

type int8 = Int8.t
type uint32 = UInt32.t


(* Modeling enclave instructions - In progress*)
(* assume val eexit : emode:bool -> u_mem:HH.rid->v_mem:HH.rid -> uv_shared_buf:HH.rid -> host_regn: HH.rid-> exitaddress:(rref host_regn int) -> Heap  unit 
  (requires (fun _ -> heap_only m /\ emode = true))
  (ensures  (fun _ _ _ -> emode = false))
*)

(*assume val eenter : emode:bool -> u_mem:HH.rid->v_mem:HH.rid -> uv_shared_buf:HH.rid -> host_regn: HH.rid-> exitaddress:(rref host_regn int) -> Heap  unit 
  (requires (fun _ -> heap_only m /\ emode = false))
  (ensures  (fun _ _ _ -> emode = true))
*)

(* This is the first entry point inside an enclave. Using eenter should switch the control to this function *)
(* assume val generic_enclave_entry : emode:bool -> u_mem:HH.rid->v_mem:HH.rid -> uv_shared_buf:HH.rid -> host_regn: HH.rid-> exitaddress:(rref host_regn int) -> Heap  unit 
  (requires (fun _ -> heap_only m /\ emode = true ))
  (ensures  (fun _ _ _ -> True))

*)
 assume val convert_int_to_bytes: n:int-> Tot (list int8)
assume val mknatlist : n:int -> Tot (list int8) 
 

assume val callenclavehost:  uv_shared_buf:HH.rid -> host_regn:HH.rid-> exitaddress:(HS.reference int) -> Heap  unit 
			(requires (fun m -> heap_only m ))
			(ensures (fun m0 r m1 -> modifies_transitively (Set.singleton host_regn) m0 m1 
				 /\ equal_domains m0 m1))


(* Design for Wrapper
	 Copy the arguments from uv_shared_buf to host_regn and then invoke CallEnclaveHost which then is verified using Vale
*)


(* 
  - modifies only host_regn and uv_shared_buf 
  - Wrapper for non_enclave_entry_point_1 : int -> int-> int
  - manifest has the function type signature. so the wrapper knows how many bytes to read/write for args/ret 
*)
val callenclavehost_wrapper_1: (uv_shared_buf:HH.rid) ->(host_regn: HH.rid)->arg1:(HS.reference int)-> arg2:(HS.reference int)->rret:(HS.reference int)  ->ST unit
			(requires (fun m -> heap_only m 
				 /\ 	m `weak_contains` arg1
				 /\ 	m `weak_contains` arg2
				 /\ 	m `contains` rret
				 /\ 	is_eternal_region host_regn	
				 )
			)
			(ensures (fun m0 r m1 -> modifies_transitively (Set.union (Set.singleton rret.id) (Set.singleton host_regn)) m0 m1 ))
let callenclavehost_wrapper_1  (uv_shared_buf:HH.rid) (host_regn:HH.rid) arg1 arg2 rret =
        (*
		- copy the arguments from uv_shared_buf to v_mem
		- which stack should wrapper use? In reality this is also responsible for switching the stack pointers between
		  U and V. But since we are not modeling U's stack, how to verify that functionality?
 	*)
	(* read from uv_shared_buf *)
	let argv1 = op_Bang arg1 in
	let argv2 = op_Bang arg2 in

	(* create a reference in host_regn and copy the arguments to host_regn *)
	// let struct_1 = Mk_struct_1 (argv1, argv2) in
	//let non_enclave_arg = ralloc host_regn  struct_1 in

	(* IMPORTANT: instead of using a struct, use a sequence of bytes like char [] and copy the arguments.
	  Though this opens a plethora of endianness issues, this is probably the only way to access
	  return value as callenclavehost() does not know where exactly return pointer is.
	  Also this is compliant with SGX SDK API for callenclaveHost
	*) 
	let size_arg1 = 4 in
	let size_arg2 = 4 in
	let nbytes_to_read = 8 in
	let nbytes_to_return = 4 in
	let nbytes_to_allocate = 12 in
	let argv1_char = convert_int_to_bytes argv1 in
	let argv2_char = convert_int_to_bytes argv2 in
	let arg_char = append argv1_char argv2_char in

	(* list of arguments and return value *)
	let ret_char = append arg_char (mknatlist nbytes_to_return) in
	
	(* Create a reference in host_regn *)
	let non_enclave_arg_as_char = ralloc host_regn ret_char in
	 

	(* Get the exit address from manifest *)
	let exitaddress = get_exit_address host_regn in

	(* Abstraction for eexit - just return like a function call.*)
	let _ = callenclavehost uv_shared_buf host_regn exitaddress in
	let ret_upd_char = op_Bang non_enclave_arg_as_char in

	(* FIXME: for now just reading 1 byte *)
	let ret_val = (FStar.List.Tot.Base.nth ret_upd_char nbytes_to_read) in

	(* FIXME: convert from int8 values to int *)
	let ret_val_int = 0 in
	
	(* Copy the return value back to uv_shared_buf *)
	rret := ret_val_int;
	()

val init_sgx_memory_model : unit -> Heap (HH.rid * HH.rid * HH.rid * HH.rid) 
  (requires (fun m -> heap_only m))
  (ensures  (fun m0 r m1 -> True))
let init_sgx_memory_model () =
  let m = get() in
  let color = 0 in
  HH.root_has_color_zero ();

  (* Enclave and non-Enclave regions *)
  let enclave_regn = new_colored_region HH.root (color -1) in
  // Shared by enclave and non-enclave components to exchange arguments
  let host_regn = new_colored_region HH.root (color - 2) in

  (* U component *)
  let u_mem  = new_colored_region enclave_regn (color-3)  in

  (* V component *)
  let v_mem  = new_colored_region enclave_regn (color-4)  in
  let v_heap = new_colored_region v_mem (color-5)  in

  // Shared by U and V components to exchange arguments
  // Only wrappers access this region
  let uv_shared_buf= new_colored_region enclave_regn (color-6)  in
  (u_mem, v_mem, uv_shared_buf, host_regn)
  
val enclavemain : unit -> Heap unit
		(requires (fun m -> heap_only m))
		(ensures  (fun m0 r m1 -> True))
let enclavemain () = 
	let u_mem, v_mem, uv_shared_buf, host_regn = init_sgx_memory_model () in
	()
