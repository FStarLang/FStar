module AnotType

type ta : Type = | A

type tb : Type u#42 = | B

(* We get two errors with this, probably should only report one *)
(* AnotType.fst(8,0-8,19): (Error 234) The type of AnotType.tc is Prims.int, but since this is the result type of a constructor its type should be Type *)
(* AnotType.fst(8,0-8,19): (Error 12) Expected type "Type u#_"; got type "Prims.int" *)
[@(fail [309])]
type tc : int = | C

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
