module Bug161

val find: f:('a -> Tot bool) -> l:list 'a ->
      Tot (res:(option 'a){Some? res ==> f (Some?.v res)})
let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl
