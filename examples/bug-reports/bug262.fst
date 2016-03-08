module Bug

open FStar.ST

//val log: ref (list int) //<-- adding this line makes it succeed
let log = ref []

val test : unit -> ST unit (requires (fun h -> Heap.contains h log))
                           (ensures (fun h0 _ h1 -> modifies !{log} h0 h1))
let test () = log := []
