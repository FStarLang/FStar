module Micro

let f (x:int) : Lemma (x == x) = ()
let g (x:int) = f x; x + 1

let h #post ($f: (x:int -> Lemma (post x))) = f 0
let i (x:int) = h f; x + 1

let h' #post ($f: (x:int -> Lemma (post x))) x = f 0; x + 1
let i' (x:int) = h' f x


let inversion (a:Type) = True
let allow_inversion (a:Type) : Pure unit (requires True) (ensures (fun x -> inversion a)) = ()
let invertOption (a:Type) = allow_inversion (list a)

let weird0 (a:Type) : Pure a (requires (a == unit)) (ensures fun _ -> True) =
  f 0

let weird1 (a:Type) (f: (int -> unit)) : Pure a (requires (a == unit)) (ensures fun _ -> True) =
  f 0

let weird2 (a:Type) (f: int -> unit) : Pure a (requires (a == (int -> unit))) (ensures fun _ -> True) =
  f

assume type t : Type -> Type
assume val  f : nat -> GTot nat
let ghost1 (#a:Type) (b:t a) (x:nat) : GTot nat = f x

let only (#a:Type0) (#rel:preorder a) (x:mref a rel) :GTot (set nat) = S.singleton (addr_of x)

assume val f : nat -> Dv bool
let test (x:nat) = f x && f x
