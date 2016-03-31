module Unit1.Projectors1
open FStar.BaseTypes

type t = 
  | T : x:int -> y:nat -> t

val f : t:t -> Tot int
let f t = t.x

type s = 
  | S : x:bool -> y:nat -> s

let g s : bool = s.x

type u = {x:char; y:int} 
let h u : char = u.x

type v = 
  | V : field1:int -> field2:nat -> v
