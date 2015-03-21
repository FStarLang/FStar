module MergeSort
open List

assume val sorted: list int -> Tot bool
assume val split: l:list int -> Tot ((list int * list int))
assume val merge: l1:list int -> Tot (r:list int{(sorted l1)})

val mergesort: l:list int -> list int
let rec mergesort l =
    let (l1, l2) = split l in
    let sl1 = mergesort l in
    merge sl1
