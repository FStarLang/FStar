module Bug154c

val ff : u:unit -> Lemma (False)
let ff u = ignore (false && 1 = 2)
