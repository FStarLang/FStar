
open Prims

type all_pre =
FStar_Heap.heap Prims.all_pre_h


type 'Aa all_post =
(FStar_Heap.heap, 'Aa) Prims.all_post_h


type 'Aa all_wp =
(FStar_Heap.heap, 'Aa) Prims.all_wp_h


type ('Aa, 'Awp, 'Ap) lift_state_all =
'Awp


type ('Aa, 'Awp, 'Ap, 'Ah) lift_exn_all =
'Awp


let pipe_right = (Obj.magic ((fun __39 __40 -> ())))


let pipe_left = (Obj.magic ((fun __62 __63 -> ())))


let failwith = (Obj.magic ((fun __78 -> ())))


let exit = (Obj.magic ((fun __87 -> ())))


let try_with = (Obj.magic ((fun __107 __108 -> ())))




