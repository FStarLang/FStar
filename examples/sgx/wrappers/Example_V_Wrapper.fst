module Example_Manifest

(* Automatically generated wrappers
 * DO NOT MODIFY
 *)

type bitmap = reference (seq int)
assume val is_writable: (addr: nat) -> bool
assume val is_uheap_reference: (addr: nat) -> bool
assume val is_vheap_reference : (addr:nat) -> bool
assume val is_code_pointer: (addr:nat) -> bool


 (* Printing signature for V's function wrapper.
 * U's code invokes V's function foo using the wrapper foo_wrapper
 *)
val foo_wrapper : (x1: int )->(x2: int )->(x3:(reference (reference (reference  int ))))->(x4:(reference (reference  int )))->(xref1: stackref (reference  int ))-> ST (rt: (reference  int ))
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
        ))
let foo_wrapper  x1 x2 x3 x4 xref1 =
        (* Check
                 1. If a reference is a stack (deep) references, then it is marked as writable in bitmap
                 2. If it is a heap reference then it refers to U's heap
                 3. Not a code pointer *)
          if true   and (is_writable (as_addr x3) or is_uheap_reference (as_addr x3))
                and ( not is_higher_order_ref x3)
                and (is_writable (as_addr  (sel h0  x3)) or is_uheap_reference (as_addr (sel h0  x3)))
                and ( not is_higher_order_ref (sel h0  x3))
                and (is_writable (as_addr  (sel h0  (sel h0  x3))) or is_uheap_reference (as_addr (sel h0  (sel h0  x3))))
                and ( not is_higher_order_ref (sel h0  (sel h0  x3)))
                and (is_writable (as_addr x4) or is_uheap_reference (as_addr x4))
                and ( not is_higher_order_ref x4)
                and (is_writable (as_addr  (sel h0  x4)) or is_uheap_reference (as_addr (sel h0  x4)))
                and ( not is_higher_order_ref (sel h0  x4))
                and (is_writable (as_addr xref1) or is_uheap_reference (as_addr xref1))
                and ( not is_code_pointer xref1)
                 then
                 (* invoking function *)
            let rt = foo x1 x2 x3 x4 xref1  in
                 rt
         else
                 (* raise an exception here? *)
                 raise Halt
