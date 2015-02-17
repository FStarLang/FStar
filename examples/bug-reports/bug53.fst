module Test

type mlist =
| N
| C: mhd:nat -> mtl:mlist -> mlist

val zero_list: l:mlist -> Tot bool
let rec zero_list l = match l with
| N -> true
| C n l' -> n = 0 && zero_list l'

(* some formulas *)
opaque logic type first_case (l:mlist) = C.mhd l = 0 /\
C.mhd (C.mtl l) = 0

opaque logic type second_case (l:mlist) = C.mhd l = 0 /\
C.mhd (C.mtl l) = 1

opaque logic type third_case (l:mlist) = C.mhd l = 1 /\
C.mhd (C.mtl l) = 0

opaque logic type fourth_case (l:mlist) = C.mhd l = 1 /\
C.mhd (C.mtl l) = 1

opaque logic type pre_1 (l:mlist) = b2t (zero_list (C.mtl (C.mtl l)))

opaque logic type pre (l:mlist) =
(first_case l ==> pre_1 l) /\
(second_case l ==> pre_1 l) /\
(third_case l ==> pre_1 l) /\
(fourth_case l ==> pre_1 l) /\
( (~(first_case l \/ second_case l \/ third_case l \/ fourth_case l)) ==> zero_list l)

val do_zero: l:mlist -> Pure mlist (requires (pre l)) (ensures (fun l -> zero_list l))
let do_zero l = match l with
| C 0 (C 0 l') -> C 0 (C 0 l')
| C 0 (C 1 l') -> C 0 (C 0 l')
| C 1 (C 0 l') -> C 0 (C 0 l')
| C 1 (C 1 l') -> C 0 (C 0 l')

| _ -> l
