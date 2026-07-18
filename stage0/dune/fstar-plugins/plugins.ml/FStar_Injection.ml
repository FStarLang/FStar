open Fstarcompiler
open Prims
let o (g : 'b -> 'c) (f : 'a -> 'b) (x : 'a) : 'c= g (f x)
type ('a, 'b) op_At_Tilde_Greater = unit
type ('a, 'b, 'i) image_of = ('a, 'b, Obj.t) FStar_Functions.image_of
type ('a, 'b) op_At_Tilde_Greater_Greater = Obj.t
