module Bug154b
open List

(* One more unsoundness bug *)

val all : p:bool -> xs:list unit ->
          Pure bool (requires True)
            (ensures (fun u -> is_Cons xs ==> p))
let rec all p xs =
  match xs with
  | [] -> true
  | x :: xs' -> p && all p xs'

val ff : u:unit -> Lemma (False)
let ff u = ignore (all false [()])
