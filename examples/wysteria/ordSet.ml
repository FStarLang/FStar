type ('a, 'b) ordset = 'a BatSet.t

let empty _ = BatSet.empty
let union _ s1 s2 = BatSet.union s1 s2
let intersect _ s1 s2 = BatSet.intersect s1 s2
let mem _ x s = BatSet.mem x s					    
let choose _ s = if BatSet.is_empty s then None else Some (BatSet.choose s)
let remove _ x s = BatSet.remove x s
let size _ s = BatSet.cardinal s			       
let subset _ s1 s2 = BatSet.subset s1 s2
let singleton _ x = BatSet.singleton x
let is_singleton _ s = BatSet.cardinal s = 1
let insert _ x s = BatSet.add x s
let fold _ f s a = BatSet.fold f s a
