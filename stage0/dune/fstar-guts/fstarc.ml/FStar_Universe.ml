open Prims
type 'a raise0 =
  | Ret of 'a 
let uu___is_Ret (projectee : 'a raise0) : Prims.bool= true
let __proj__Ret__item___0 (projectee : 'a raise0) : 'a=
  match projectee with | Ret _0 -> _0
type 'a raise_t = 'a raise0
let raise_val (x : 'a) : 'a raise_t= Ret x
let downgrade_val (x : 'a raise_t) : 'a= match x with | Ret x0 -> x0
let lift_dom (q : 'a -> 'b) (v : 'a raise_t) : 'b= q (downgrade_val v)
let lift_codom (q : 'a -> 'b) (v : 'a) : 'b raise_t= raise_val (q v)
