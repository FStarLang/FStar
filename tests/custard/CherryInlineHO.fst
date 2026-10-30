module CherryInlineHO
module U32 = FStar.UInt32
open FStar.All

(* Combinators marked [@@custard_inline] are inlined, so a lambda given to
   them meets its call and is no closure (cherry.md, "Functions"). *)
[@@FStar.Attributes.custard_inline]
let apply_plus_one (f: int -> ML int) (x: int) : ML int = f x + 1

let rec existsb (f: int -> ML bool) (l: list int) : ML bool =
  match l with
  | [] -> false
  | x :: xs -> if f x then true else existsb f xs

(* Eta-reduced to [some f = existsb f] before inlining: the call's second
   argument completes the application of [existsb]. *)
[@@FStar.Attributes.custard_inline]
let some (f: int -> ML bool) (l: list int) : ML bool = existsb f l

(* A class whose [bind] is marked, used through an alias that F* extracts as
   the partial application [bind m]: inlining the alias completes the call to
   [bind], which is then inlined in turn, and the continuation is no
   closure. *)
class monad (m: Type0 -> Type0) = {
  [@@@FStar.Attributes.custard_inline]
  bind : #a:Type0 -> #b:Type0 -> m a -> (a -> ML (m b)) -> ML (m b)
}

instance monad_option : monad option = {
  bind = (fun #a #b (o: option a) (f: a -> ML (option b)) ->
           match o with None -> None | Some v -> f v)
}

[@@FStar.Attributes.custard_inline]
let ( let! ) : #m:(Type -> Type) -> {| monad m |} -> #a:Type0 -> #b:Type0 -> m a -> (a -> ML (m b)) -> ML (m b) = bind

let sum (x y: option int) : ML (option int) =
  let! a = x in
  let! b = y in
  Some (a + b)

let add (k: int) (x: int) : ML int = apply_plus_one (fun y -> y + k) x

let has_above (k: int) (l: list int) : ML bool = some (fun y -> y > k) (0 :: l)

let main () : ML U32.t =
  if add 3 1 = 5 && has_above 2 [1; 2; 3] && not (has_above 5 [1])
     && sum (Some 1) (Some 2) = Some 3 && None? (sum (Some 1) None)
  then 0ul else 1ul
