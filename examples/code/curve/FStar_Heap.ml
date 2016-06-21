
open Prims

type heap =
Prims.unit

type 'Aa ref =
| MkRef of 'Aa


let ___MkRef____0 = (fun projectee -> (match ((Obj.magic (projectee))) with
| MkRef (_0) -> begin
_0
end))

type aref =
| Ref of Prims.unit * Obj.t ref


type 'Aprojectee a =
Obj.t


let ___Ref___r : aref  ->  Prims.unit FStar_Heap_Ref.a ref = (fun projectee -> (Obj.magic ((match ((Obj.magic (projectee))) with
| Ref (a, r) -> begin
r
end))))


let sel = (Obj.magic ((fun __51 __52 -> ())))


let upd = (Obj.magic ((fun __73 __74 __75 -> ())))


let emp : heap = (Obj.magic (()))


let contains = (Obj.magic ((fun __91 __92 -> ())))


let equal : heap  ->  heap  ->  Prims.bool = (Obj.magic ((fun __100 __101 -> ())))


let restrict : heap  ->  aref FStar_Set.set  ->  heap = (Obj.magic ((fun __109 __110 -> ())))


let concat : heap  ->  heap  ->  heap = (Obj.magic ((fun __118 __119 -> ())))


let domain : heap  ->  aref FStar_Set.set = (Obj.magic ((fun __124 -> ())))


type ('Ar, 'Ap, 'Ah) on =
'Ap


type ('Arefs, 'Ah0, 'Ah1) fresh =
Prims.unit


type ('Amods, 'Ah, 'Ah') modifies =
(Prims.unit Prims.b2t, Prims.unit Prims.b2t) Prims.l_and


let lemma_modifies_trans : heap  ->  heap  ->  heap  ->  aref FStar_Set.set  ->  aref FStar_Set.set  ->  Prims.unit = (fun m1 m2 m3 s1 s2 -> ())


let only = (fun x -> (FStar_Set.singleton (Ref ((), (Obj.magic (x))))))


let op_Hat_Plus_Plus = (fun r s -> (FStar_Set.union (FStar_Set.singleton (Ref ((), (Obj.magic (r))))) s))


let op_Plus_Plus_Hat = (fun s r -> (FStar_Set.union s (FStar_Set.singleton (Ref ((), (Obj.magic (r)))))))


let op_Hat_Plus_Hat = (fun r1 r2 -> (FStar_Set.union (FStar_Set.singleton (Ref ((), (Obj.magic (r1))))) (FStar_Set.singleton (Ref ((), (Obj.magic (r2)))))))




