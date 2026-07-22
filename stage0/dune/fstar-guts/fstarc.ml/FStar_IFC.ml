open Prims
type semilattice =
  | SemiLattice of unit * Obj.t * (Obj.t -> Obj.t -> Obj.t) 
let uu___is_SemiLattice (projectee : semilattice) : Prims.bool= true
let __proj__SemiLattice__item__top (projectee : semilattice) : Obj.t=
  match projectee with | SemiLattice (carrier, top, lub) -> top
let __proj__SemiLattice__item__lub (projectee : semilattice) :
  Obj.t -> Obj.t -> Obj.t=
  match projectee with | SemiLattice (carrier, top, lub) -> lub
type sl = unit
type 'sl1 lattice_element = unit

type ('sl1, 'l, 'b) protected = 'b
let hide (sl1 : unit) (l : unit) (b : unit) (x : Obj.t) : Obj.t= x
let return (sl1 : unit) (a : unit) (l : unit) (x : Obj.t) : Obj.t=
  hide () () () x
let map (sl1 : unit) (l : unit) (x : (Obj.t, Obj.t, 'a) protected)
  (f : 'a -> 'b) : (Obj.t, Obj.t, 'b) protected= f x
let join (sl1 : unit) (l1 : unit) (l2 : unit) (a : unit) (x : Obj.t) : 
  Obj.t= x
let op_let_Greater_Greater (sl1 : unit) (l1 : unit) (a : unit) (x : Obj.t)
  (l2 : unit) (b : unit) (f : Obj.t -> Obj.t) : Obj.t=
  join () () () () (map () () x f)
