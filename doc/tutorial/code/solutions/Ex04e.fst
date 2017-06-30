module Ex04e
//find

type option 'a =  
   | None : option 'a
   | Some : v:'a -> option 'a

(* The intrinsic style is more convenient in this case *)
val find : f:('a -> Tot bool) -> list 'a -> Tot (option (x:'a{f x}))
let rec find f l = match l with
  | [] -> None
  | hd :: tl -> if f hd then Some hd else find f tl

(* Extrinsically things are more verbose, since we are basically duplicating
   the structure of find in find_some. It's still not too bad. *)

val find' : #t:Type -> f:(t -> Tot bool) -> list t -> Tot (option t)
let rec find' #t f l = match l with
  | [] -> None
  | hd :: tl -> if f hd then Some hd else find' f tl

val find_some : f:('a -> Tot bool) -> xs:(list 'a) ->
    Lemma (None? (find' f xs) || f (Some?.v (find' f xs)))
let rec find_some f xs =
    match xs with
    | [] -> ()
    | x :: xs' -> find_some f xs'

(* [Some?.v] and [None?] are convenient ways to manipulate options.  They are
   described later in the tutorial.  Here's a more verbose way to achieve the
   same thing: *)

val find_some' : f:('a -> Tot bool) -> xs:(list 'a) ->
    Lemma (match find f xs with
           | None -> true
           | Some v -> f v)
let rec find_some' f xs =
    match xs with
    | [] -> ()
    | x :: xs' -> find_some' f xs'
