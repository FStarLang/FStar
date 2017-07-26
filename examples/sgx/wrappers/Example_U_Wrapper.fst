module Example_U_Manifest
open Manifest


 (* Automatically generated wrappers for U
 * DO NOT MODIFY
 *)

assume val set_ref_as_mutable: (addr:stackref 'a) -> (rt:stackref 'a{rt.is_mutable = true})
assume val unset_ref_as_mutable: (addr:stackref 'a) -> (rt:stackref 'a{rt.is_mutable = false})
assume val is_ref_mutable: (addr: reference 'a) -> bool
assume val is_stack_reference: (addr: reference 'a) -> bool
assume val is_uheap_reference: (addr: reference 'a) -> bool
assume val is_vheap_reference : (addr: referece 'a) -> bool
assume val is_code_reference: (addr:reference 'a) -> bool

val get_stack_frames_below : (h:mem) -> (list rid)
(* Not quite right - IN PROGRESS *)
let get_stack_frames_below h =
    let top = h.tip
    let rec get_last_parent (f:rid) (l:list rid) =
         let p = HH.parent f in
          if p = HH.root then l else get_last_parent p::l

assume val refs_in_region: (l:list rid)->(list reference)

val get_all_refs_from_stack_frames_below : (h:mem) -> (list reference)
let get_all_refs_from_stack_frames_below h =
    let sframes = get_stack_frames_below h
    refs_in_region sframes

assume val get_bitmap_unset_references : (h:mem)->(list reference)

let clear_bitmap =
         let h = get ()
         let lr = get_all_refs_from_stack_frames_below h
         let rec clear_each_ref_mutability = function
                 [] -> ()
                |hd::tl -> let _ = unset_ref_as_mutable hd in
                                clear_each_ref_mutability tl

 (* Printing signature for U's function wrapper.
 * V's code invokes U's function ufunc using the wrapper ufunc_wrapper
 *)
val ufunc_wrapper : (x1: int )->(x2: int )->(x3:(reference (reference (reference  int ))))->(x4:(reference (reference  int )))->(xref1: stackref (reference  int ))-> Stack (rt: (reference  int ))
         (requires (fun h0 -> True  /\ (h0 `contains` x3)
        /\ (not is_code_reference x3)
        /\ (h0 `contains` (sel h0  x3))
        /\ (not is_code_reference (sel h0  x3))
        /\ (h0 `contains` (sel h0  (sel h0  x3)))
        /\ (not is_code_reference (sel h0  (sel h0  x3)))
        /\ (h0 `contains` x4)
        /\ (not is_code_reference x4)
        /\ (h0 `contains` (sel h0  x4))
        /\ (not is_code_reference (sel h0  x4))
        /\ (h0 `contains` xref1)
        /\ (not is_code_reference xref1)
        ))
         (ensures (fun h0 r h1 -> modifies Set.union Set.empty Set.union (Set.singleton (frameOf x3)) Set.union (Set.singleton (frameOf sel h  x3)) Set.union (Set.singleton (frameOf sel h  (frameOf sel h  x3))) Set.union (Set.singleton (frameOf sel h  x3)) Set.union (Set.singleton (frameOf x4)) Set.union (Set.singleton (frameOf sel h  x4)) Set.union (Set.singleton (frameOf xref1))  u_mem h0 h1
         /\ modifies_ref (frameOf x3)  (Set.singleton (as_addr x3))
         /\ modifies_ref (frameOf (sel h0  x3)) Set.singleton as_addr (frameOf sel h0  x3)
         /\ modifies_ref (frameOf (sel h0  (sel h0  x3))) Set.singleton as_addr (frameOf sel h0  as_addr (frameOf sel h0  x3))Set.union (Set.singleton (frameOf sel h  x3))
         /\ modifies_ref (frameOf x4)  (Set.singleton (as_addr x4))
         /\ modifies_ref (frameOf (sel h0  x4)) Set.singleton as_addr (frameOf sel h0  x4)
         /\ modifies_ref (frameOf xref1) (Set.singleton (as_addr xref1))
         /\ (not is_vheap_reference rt)
        ))
let ufunc_wrapper  x1 x2 x3 x4 xref1 =

        (* Clearing bitmap *)
        let _ = clear_bitmap in
        (* Setting the mutability bit of references for arguments *)
        if (is_stack_reference x3) then
                set_ref_as_mutable x3
         if (is_stack_reference (sel h0  x3)) then
                set_ref_as_mutable x3
         if (is_stack_reference (sel h0  (sel h0  x3))) then
                set_ref_as_mutable x3
         if (is_stack_reference x4) then
                set_ref_as_mutable x4
         if (is_stack_reference (sel h0  x4)) then
                set_ref_as_mutable x4
         if (is_stack_reference  xref1) then
                set_ref_as_mutable xref5
         (* invoking function *)
        let rt = ufunc x1 x2 x3 x4 xref1
         in rt

