module Bug154b

val all : b:bool -> n:nat ->
          Pure bool (requires True) (ensures (fun u -> b))
let all b n = b && n = 1

val ff : u:unit -> Lemma (False)
let ff u = ignore (all false 1)
