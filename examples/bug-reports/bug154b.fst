module Bug154b

val all : b:bool -> n:nat ->
          Pure bool (requires True)
            (ensures (fun u -> n = 0 \/ b))
let rec all b n = n = 0 || (b && all b (n-1))

val ff : u:unit -> Lemma (False)
let ff u = ignore (all false 42)
