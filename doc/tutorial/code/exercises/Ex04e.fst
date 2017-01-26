module Ex04e
//find

type option 'a =  
   | None : option 'a
   | Some : v:'a -> option 'a

let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

(*
Prove that if `find` returns `Some x` then `f x = true`. 
Is it better to do this intrinsically or extrinsically? Do it both ways.
*)



