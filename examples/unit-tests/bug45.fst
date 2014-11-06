
module Bug45

val xxx : unit -> Fact unit (ensures False)
let xxx _ = assert(False); admit()
