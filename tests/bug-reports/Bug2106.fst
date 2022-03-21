module Bug2106

val loop : (#a:Type u#a) -> x:a -> Dv a
let rec loop #a x = loop x

val last : (#a:Type u#a) -> l:(list a){Cons? l} -> Tot a
let rec last l =
  match l with
  | [hd] -> hd
  | _::tl -> last tl

let rec loop2 #a (x:a) : Dv a = loop2 x
