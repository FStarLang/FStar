open Fstarcompiler
open Prims
let o (g : 'b -> 'c) (f : 'a -> 'b) (x : 'a) : 'c= g (f x)
type ('a, 'b) op_Equals_Tilde = unit











type ('a, 'b) cbij = {
  bij: unit ;
  cright: 'a -> 'b ;
  cleft: 'b -> 'a }

let __proj__Mkcbij__item__cright (projectee : ('a, 'b) cbij) : 'a -> 'b=
  match projectee with | { bij; cright; cleft;_} -> cright
let __proj__Mkcbij__item__cleft (projectee : ('a, 'b) cbij) : 'b -> 'a=
  match projectee with | { bij; cright; cleft;_} -> cleft
let mk_cbij (right : 'a -> 'b) (left : 'b -> 'a) (right_left : unit)
  (left_right : unit) : ('a, 'b) cbij=
  { bij = (); cright = right; cleft = left }
type ('a, 'b) op_Equals_Equals_Tilde = ('a, 'b) cbij

