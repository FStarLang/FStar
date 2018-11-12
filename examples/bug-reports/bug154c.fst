module Bug154c

val ff : unit -> Lemma (ensures False)
let ff u = ignore (false && (0 = 1))
