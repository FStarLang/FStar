type 'a set = 'a BatSet.t
let empty () =  BatSet.empty
let singleton = BatSet.singleton
let union = BatSet.union
let intersect = BatSet.intersect
let complement x = BatSet.empty
let mem = BatSet.mem

(* F* should not extract below: *)
type ('A, 'B, 'C) equal = unit
