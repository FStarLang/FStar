module Test.ConstantTimeIntegers

open FStar.Integers
open FStar.IFC
open FStar.ConstantTime.Integers

private irreducible
let test (x:int) (y:int) = x + y
private
let two_point_lattice = Ghost.hide (SemiLattice true ( || ))
private
let lo : lattice_element two_point_lattice = Ghost.hide false
private
let hi : lattice_element two_point_lattice = Ghost.hide true
private irreducible
let test2 (x:t (Secret lo (Unsigned W32))) (y:t (Secret lo (Unsigned W32))) = x +% y
private irreducible
let test3 (x:t (Secret hi (Unsigned W32))) (y:t (Secret lo (Unsigned W32))) = x +% promote y hi
private irreducible
let test4 (x:t (Secret lo (Unsigned W32))) (y:t (Secret hi (Unsigned W32)) { ok ( + ) (i x) (i y) }) = promote x hi + y

private
let hacl_lattice = Ghost.hide (SemiLattice () (fun _ _ -> ()))
private
let hacl_label : lattice_element hacl_lattice = Ghost.hide ()
private
let s_uint32 = t (Secret hacl_label (Unsigned W32))
private irreducible
let test5 (x:s_uint32) (y:s_uint32) = x +% y
private irreducible
let test6 (x:s_uint32) (y:s_uint32{ok (+) (i x) (i y)}) = x + y

