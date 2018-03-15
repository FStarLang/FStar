module FStar.Tactics.Util

open FStar.Tactics.Effect

(* Tac list functions, since there's no effect polymorphism *)
val map: ('a -> Tac 'b) -> list 'a -> Tac (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

val iter : ('a -> Tac unit) -> list 'a -> Tac unit
let iter f x =
    let _ = map f x in ()

val fold_left: ('a -> 'b -> Tac 'a) -> 'a -> l:list 'b -> Tac 'a
let rec fold_left f x l = match l with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

val fold_right: ('a -> 'b -> Tac 'b) -> list 'a -> 'b -> Tac 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(* There's no unconditionally total zip like this in Tot.Base, why? Anyway use this *)
val zip : (#a:Type) -> (#b:Type) -> list a -> list b -> Tac (list (a * b))
let rec zip #a #b l1 l2 = match l1, l2 with
    | x::xs, y::ys -> (x,y) :: (zip xs ys)
    | _ -> []
