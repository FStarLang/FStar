module AnotType

(* If this is not first, we explode weirdly *)
(* AnotType.fst(3,19-3,20): (Error 22) Top-level declaration AnotType.uu___is_A for a name that is already used in this module; top-level declarations must be unique in their module *)
(* Huh???????? *)
(* [@(expect_failure [309])] *)
(* type tc : int = | C *)

type ta : Type = | A

type tb : Type u#42 = | B

(* Fails, Type0 != Type42 *)
[@(expect_failure [189])]
let _ = ta == tb

type td : eqtype = | D

type te : int -> eqtype = | Ea : te 1
                          | Eb : te 1
                          | Ec : te 8
                          | Ed : te 99


(* This has to work without SMT, since `td` was annotated as an eqtype.
 * We need not unfold and see the relevant `hasEq`. *)
#set-options "--no_smt"
let f (x y : td) = x = y

let _ = Ea = Eb
