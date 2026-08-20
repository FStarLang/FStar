module StrictInt
let f (x:int) : int = x

(* Same type in both fixture modules, so no filter can ever separate the
   two candidates and a use site is unconditionally ambiguous. *)
let same : int = 0
