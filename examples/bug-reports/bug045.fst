module Bug045

val xxx : unit -> Lemma (ensures (False))
let xxx _ = assert(False); admit()
