module IfaceCopiedLet

(* Note: no [let twice] here; the interface's definition is used as is. *)

let quad (x:int) : int = twice (twice x)

let describe (#a:Type) {| showable a |} (x:a) : string = show_ x

let _ = assert (quad 1 == 4)
let _ = assert (describe 0 == "int")
