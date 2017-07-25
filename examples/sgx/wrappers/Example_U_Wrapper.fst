module Example_U_Wrapper


 (* Automatically generated wrappers for U
 * DO NOT MODIFY
 *)

type bitmap = reference (seq int)
assume val is_writable: (addr: nat) -> bool
assume val is_uheap_reference: (addr: nat) -> bool
assume val is_vheap_reference : (addr:nat) -> bool
assume val is_code_pointer: (addr:nat) -> bool

val get_stack_frames_below : (h:mem) -> (list rid)
(* Not quite right - IN PROGRESS *)
let get_stack_frames_below h =
    let top = h.tip
    let rec get_last_parent (f:rid) (l:list rid) =
         let p = HH.parent f in
          if p = HH.root then l else get_last_parent p::l

assume val refs_in_region: (l:rid)->(list nat)

val get_all_refs_from_stack_frames_below : (h:mem) -> (Set nat)
let get_all_refs_from_stack_frames_below h =
    let sframes = get_stack_frames_below h
    let srefs = refs_in_region sframes
    as_addr_list srefs

assume val get_bitmap_unset_locations : (h:mem)->(loc: Set nat)-> (Set nat)


 (* Printing signature for U's function wrapper.
 * V's code invokes U's function ufunc using the wrapper ufunc_wrapper
 *)
val ufunc_wrapper : (x1: int )->(x2: int )->(x3:(reference (reference (reference  int ))))->(x4:(reference (reference  int )))->(xref1: stackref (reference  int ))-> Stack (rt: (reference  int ))
         (requires (fun h -> True  /\ (h `contains` x3)
        /\ (h `contains` (sel h0  x3))
        /\ (h `contains` (sel h0  (sel h0  x3)))
        /\ (h `contains` x4)
        /\ (h `contains` (sel h0  x4))
        /\ (h `contains` xref1)
        ))
         (ensures (fun h0 r h1 -> modifies Set.union Set.empty Set.union (Set.singleton (frameOf x3)) Set.union (Set.singleton (frameOf sel h  x3)) Set.union (Set.singleton (frameOf sel h  (frameOf sel h  x3))) Set.union (Set.singleton (frameOf sel h  x3)) Set.union (Set.singleton (frameOf x4)) Set.union (Set.singleton (frameOf sel h  x4)) Set.union (Set.singleton (frameOf xref1)) h0 h1
         /\ modifies_ref (frameOf x3)  (Set.singleton (as_addr x3))
         /\ modifies_ref (frameOf (sel h0  x3)) Set.singleton as_addr (frameOf sel h0  x3)
         /\ modifies_ref (frameOf (sel h0  (sel h0  x3))) Set.singleton as_addr (frameOf sel h0  as_addr (frameOf sel h0  x3))Set.union (Set.singleton (frameOf sel h  x3))
         /\ modifies_ref (frameOf x4)  (Set.singleton (as_addr x4))
         /\ modifies_ref (frameOf (sel h0  x4)) Set.singleton as_addr (frameOf sel h0  x4)
         /\ modifies_ref (frameOf xref1) (Set.singleton (as_addr xref1))
         /\ (not is_vheap_reference rt)
        /\ get_bitmap_unset_locations h0 (get_all_refs_from_stack_frames_below h0) = get_bitmap_unset_locations h1 (get_all_refs_from_stack_frames_below h1)
        ))
let ufunc_wrapper  x1 x2 x3 x4 xref1 =
        (* Check
                 1. If it is a stack (deep) reference, it is marked as writable in bitmap
                 2. If it is a heap reference then it refers to U's heap
                 3. Not a code pointer *)
          if true   and (is_writable (as_addr x3) or is_uheap_reference (as_addr x3))
                and ( not is_code_pointer x3)
                and (is_writable (as_addr  (sel h0  x3)) or is_uheap_reference (as_addr (sel h0  x3)))
                and ( not is_code_pointer (sel h0  x3))
                and (is_writable (as_addr  (sel h0  (sel h0  x3))) or is_uheap_reference (as_addr (sel h0  (sel h0  x3))))
                and ( not is_code_pointer (sel h0  (sel h0  x3)))
                and (is_writable (as_addr x4) or is_uheap_reference (as_addr x4))
                and ( not is_code_pointer x4)
                and (is_writable (as_addr  (sel h0  x4)) or is_uheap_reference (as_addr (sel h0  x4)))
                and ( not is_code_pointer (sel h0  x4))
                and (is_writable (as_addr xref1) or is_uheap_reference (as_addr xref1))
                and ( not is_code_pointer xref1)
                 then
                 (* invoking function *)
            let rt = ufunc x1 x2 x3 x4 xref1  in
                 rt
         else
                 (* raise an exception here? *)
                 raise Halt

