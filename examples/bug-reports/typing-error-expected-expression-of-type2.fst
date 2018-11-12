module EEOT2

val app : list 'a -> list 'a -> Tot (list 'a)
let rec app l1 l2 =
  match l1 with
  | []   -> l2
  | h::t -> app h l2

(*
Expected expression of type "[Before:(list ('U537 'a))][After:(list ('U537 'a))]";
got expression "h" of type
"[Before:((fun 'a:Type => ((fun 'a:Type => 'a) 'a)) 'a)]
[After:'a]"
*)
