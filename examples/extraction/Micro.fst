module Micro

let f1 (x:int) : Lemma (x == x) = ()
let g1 (x:int) = f1 x; x + 1

let h2 #post ($f: (x:int -> Lemma (post x))) = f 0
let i2 (x:int) = h2 f1; x + 1

let h3 #post ($f: (x:int -> Lemma (post x))) x = f 0; x + 1
let i3 (x:int) = h3 f1 x

let weird0 (a:Type) : Pure a (requires (a == unit)) (ensures fun _ -> True) =
  f1 0

let weird1 (a:Type) (f: (int -> unit)) : Pure a (requires (a == unit)) (ensures fun _ -> True) =
  f1 0

#set-options "--lax"
let weird2 (a:Type) (f: int -> unit) : Pure a (requires (a == (int -> unit))) (ensures fun _ -> True) =
  f1
#reset-options

assume
val f4 : nat -> GTot nat
let h4 (#a:Type) (x:nat) : GTot nat = f4 x

assume
val f5 : nat -> Dv bool
#set-options "--lax"
let h5 (x:nat) = f5 x && f5 x
#reset-options

assume
val f6 : string -> Dv string
let h6 (s:string) c = c (f6 s)

assume
val f7: string -> Dv unit
let h7:unit = f7 "hello"

let g8 (f:int -> 'b) (x:int) : Dv 'b = f x
let ignore (x:int) : unit = ()
let h8 (x:int) = g8 ignore x; x + 1

let h9 (x:int) (y:bool) =
  let id (#a:Type) (x:a) = x in
  id x, id y
