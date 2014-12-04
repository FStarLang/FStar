module Unif

val comp : 'a:Type -> 'b:Type ->
           'a -> ('a -> 'a) -> ('a -> 'b -> 'a) -> 'a -> 'a
let comp j f g x =
  let ff a z = f (g z (f (f (g x z)))) in
  let gg = g (f x) in
  ff j (gg j)

(* Error message before and after normalization:

Expected expression of type "[Before:'b][After:'b]";
got expression "z" of type
"[Before:((fun 'a:Type 'b:Type => 'a) 'a 'b)][After:'a]"
*)
