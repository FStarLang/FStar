module Ex04e
//find

type option 'a =  
   | None : option 'a
   | Some : 'a -> option 'a

(* The intrinsic style is more convenient in this case *)
val find : f:('a -> Tot bool) -> list 'a -> Tot (option (x:'a{f x}))
let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

(* Extrinsically things are more verbose, since we are basically duplicating
   the structure of find in find_some. It's still not too bad. *)

val find' : #t:Type -> f:(t -> Tot bool) -> list t -> Tot (option t)
let rec find' #t f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find' f tl


val find_some : #t:Type -> f:(t -> Tot bool) -> l:list t -> x:t -> Lemma
                  (requires (find' f l == Some x))
                  (ensures (f x = true))
let rec find_some #t f l x =
  match l with
  | [] -> ()
  | hd::tl -> if f hd then () else find_some f tl x
