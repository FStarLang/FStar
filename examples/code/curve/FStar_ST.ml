
open Prims

type 'Aa ref =
'Aa FStar_Heap.ref


type ('Amods, 'Ah, 'Ah') modifies =
Prims.unit Prims.b2t


type st_pre =
FStar_Heap.heap Prims.st_pre_h


type 'Aa st_post =
(FStar_Heap.heap, 'Aa) Prims.st_post_h


type 'Aa st_wp =
(FStar_Heap.heap, 'Aa) Prims.st_wp_h


type ('Aa, 'Awp, 'Ap, 'Ah) lift_div_state =
'Awp


let recall = (fun r -> ())


let alloc = (Obj.magic ((fun init -> ())))


let read = (Obj.magic ((fun r -> ())))


let write = (fun r v -> ())


let op_Colon_Equals = (fun r v -> ())


let get : Prims.unit  ->  FStar_Heap.heap = (Obj.magic ((fun __122 -> ())))




