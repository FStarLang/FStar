module LListWithTail.Cell
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference

val cell (a:Type0) : Type0
let cellptr (a: Type0) : Type0 = ref (option (cell a))
val next (c:cell 'a) : cellptr 'a
val data (c:cell 'a) : 'a
val mk_cell (n: cellptr 'a) (d:'a)
  : Pure (cell 'a)
    (requires True)
    (ensures fun c ->
      next c == n /\
      data c == d)
