open Prims
type 'a raise0 =
  | Ret of 'a 
let uu___is_Ret : 'a . 'a raise0 -> Prims.bool = fun projectee -> true
let __proj__Ret__item___0 : 'a . 'a raise0 -> 'a =
  fun projectee -> match projectee with | Ret _0 -> _0
type 'a raise_t = 'a raise0
let raise_val : 'a . 'a -> 'a raise_t = fun x -> Ret x
let downgrade_val : 'a . 'a raise_t -> 'a =
  fun x -> match x with | Ret x0 -> x0
let lift_dom : 'a 'b . ('a -> 'b) -> 'a raise_t -> 'b =
  fun q -> fun v -> q (downgrade_val v)
let lift_codom : 'a 'b . ('a -> 'b) -> 'a -> 'b raise_t =
  fun q -> fun v -> raise_val (q v)