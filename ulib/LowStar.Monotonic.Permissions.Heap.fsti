module LowStar.Monotonic.Permissions.Heap

open FStar.Preorder

let permission = nat

val heap: Type u#1

val emp: heap

val ref (a:Type0) (rel:preorder a) : Type0

val addr_of (#a:Type0) (#rel:preorder a) (r:ref a rel) : GTot nat

val contains: #a:Type0 -> #rel:preorder a -> heap -> ref a rel -> Type0

val writeable: #a:Type0 -> #rel:preorder a -> heap -> ref a rel -> Type0

val sel_tot: #a:Type0 -> #rel:preorder a -> h:heap -> r:ref a rel{h `contains` r} -> Tot a

val upd_tot: #a:Type0 -> #rel:preorder a -> h:heap -> r:ref a rel{h `writeable` r} -> x:a -> Tot heap

val alloc: #a:Type0 -> rel:preorder a -> heap -> a -> mm:bool -> Tot (ref a rel * heap)

val distinct: #a:Type0 -> #rel:preorder a -> ref a rel -> ref a rel -> GTot bool

// Share the permissions between the given ref and a newly created ref. Both are contained, but not 
// writeable anymore if the first one initially was
// Only GTot because of H.addr_of being GTot. Could be solved with friend
val share: #a:Type -> #rel:preorder a -> h:heap -> r:ref a rel{h `contains` r} -> Ghost (heap * ref a rel * ref a rel)
 (requires True)
 // This could possibly go into an auxiliary lemma
 (ensures fun (h', r1, r2) -> h' `contains` r1 /\ h' `contains` r2 /\ addr_of r1 = addr_of r2 /\ distinct r1 r2)

// Merges permissions into r1. Does not touch to the heap otherwise
// Again, only ghost because of H.addr_of.
val merge: #a:Type -> #rel:preorder a -> h:heap -> r1:ref a rel{h `contains` r1} -> r2:ref a rel{h `contains` r2} ->
  Ghost (heap * ref a rel) 
    (requires addr_of r1 = addr_of r2 /\ distinct r1 r2) // ensures that addresses are the same, but perm ids are different
    (ensures fun (h', r') -> h' `contains` r')    
