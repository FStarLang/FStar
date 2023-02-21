type ('a, 'b) ref = 'a Steel_HigherReference.ref

let alloc (p:unit) (v:'a) = Steel_HigherReference.alloc

let read_refine (q:unit) (p:unit) (frame:unit) (r: ('a, unit) ref) =
  Steel_HigherReference.read q p r

let write (v:unit) (r:('a, unit) ref) (x:'a) =
Steel_HigherReference.write v r x

let witness (q:unit) (p:unit) (r:('a, unit) ref) (fact:unit) (v:unit) (_:unit) = ()

let recall (q:unit) (p:unit) (fact:unit) (r:('a, unit) ref) (v:unit) = ()

