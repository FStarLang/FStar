module Bug154b

val all : b:bool ->
          Pure bool (requires True) (ensures (fun u -> b))
let all b = b && 1 = 2

val ff : u:unit -> Lemma (False)
let ff u = ignore (all false)
