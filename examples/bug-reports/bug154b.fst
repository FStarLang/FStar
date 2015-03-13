module Bug154b

val all : p:bool -> xs:list unit ->
          Pure bool (requires True)
            (ensures (fun u -> is_Nil xs \/ p))
let rec all p xs =
  if is_Nil xs then false
  else (p && all p (Cons.tl xs))

val ff : u:unit -> Lemma (False)
let ff u = ignore (all false [()])
