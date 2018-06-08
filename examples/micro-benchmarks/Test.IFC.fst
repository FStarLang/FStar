module Test.IFC
////////////////////////////////////////////////////////////////////////////////
//A basic test of monadic information flow control provided in FStar.IFC
////////////////////////////////////////////////////////////////////////////////
open FStar.IFC

let two_point_lattice =
  SemiLattice true (fun x y -> x || y)

let high : lattice_element two_point_lattice = true
let low  : lattice_element two_point_lattice = false

let ret #a (x:a) = return low x

let test1 (#l1:lattice_element two_point_lattice)
          (px:protected l1 int)
   : z:protected l1 int{reveal z = reveal px + 1}
   = map px (fun x -> x + 1)

let test2 (#l1:lattice_element two_point_lattice)
          (#l2:lattice_element two_point_lattice)
          (px:protected l1 int)
          (py:protected l2 int)
   : z:protected (l1 `lub` l2) int{reveal z = reveal px + reveal py}
   = let f (x:int) : (z:protected l2 int{reveal z = x + reveal py}) =
         map py (fun y -> x + y)
     in
     let g :  (z:protected l1 (protected l2 int){reveal (reveal z) = reveal px + reveal py}) =
         map px f
     in
     join g

let test3 (#l1:lattice_element two_point_lattice)
          (#l2:lattice_element two_point_lattice)
          (px:protected l1 int)
          (py:protected l2 int)
   : z:protected (l1 `lub` l2) int{reveal z = reveal px + reveal py}
   = x <-- px ;
     y <-- py ;
     ret (x + y)
