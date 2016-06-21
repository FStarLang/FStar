
open Prims

type 'Aa erased =
'Aa


let reveal = (Obj.magic ((fun x -> (Obj.magic (())))))


let hide = (fun x -> x)


let lemma_hide_reveal = (Obj.magic ((fun x -> ())))


let as_ghost = (fun f -> (f ()))


let elift1 = (Obj.magic ((fun f ga -> (f (Obj.magic ((Obj.magic (()))))))))


let elift2 = (Obj.magic ((fun f ga gc -> (f (Obj.magic ((Obj.magic (())))) (Obj.magic ((Obj.magic (()))))))))


let elift3 = (Obj.magic ((fun f ga gc gd -> (f (Obj.magic ((Obj.magic (())))) (Obj.magic ((Obj.magic (())))) (Obj.magic ((Obj.magic (()))))))))


let elift1_p = (Obj.magic ((fun f ga -> (f (Obj.magic ((Obj.magic (()))))))))


let elift2_p = (Obj.magic ((fun f ga gc -> (f (Obj.magic ((Obj.magic (())))) (Obj.magic ((Obj.magic (()))))))))


let gcut = ()


let gassume = (fun uu____234 -> ())




