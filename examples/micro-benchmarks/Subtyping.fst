module Subtyping

assume val p : int -> Type0
assume val q : int -> Type0
assume val n : n:int{q n}

let f : int -> b:int{q b} = fun (_:int) -> n
let g : a:int{p a} -> int = f
let h : a:int{p a} -> int = fun (_:int) -> n // this used to fail before fab0d820c8e342f16e83c5e1b4734876e5a59106
let i : a:int{p a} -> b:int{p b} = fun n -> n
