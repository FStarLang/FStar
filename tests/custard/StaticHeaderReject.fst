module StaticHeaderReject

let constant : FStar.UInt32.t = 7ul

assume val seed (u:unit) : FStar.All.ML bool
let computed : bool = seed ()

let apply (x:FStar.UInt32.t) : FStar.UInt32.t = x
let main () : FStar.All.ML FStar.UInt32.t = 0ul
