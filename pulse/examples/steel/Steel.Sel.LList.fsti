module Steel.Sel.LList

open Steel.Memory
open Steel.SelEffect


val cell (a:Type0) : Type0
let t (a:Type0) = ref (cell a)

val next (c:cell 'a) : t 'a
val data (c:cell 'a) : 'a
val mk_cell (n: t 'a) (d:'a)
  : Pure (cell 'a)
    (requires True)
    (ensures fun c ->
      next c == n /\
      data c == d)



val llist_sl (#a:Type0) (r:t a) : slprop u#1
val llist_sel (#a:Type0) (r:t a) : selector (list a) (llist_sl r)

[@@__steel_reduce__]
let llist' #a r : vprop' =
  {hp = llist_sl r;
   t = list a;
   sel = llist_sel r}
unfold
let llist (#a:Type0) (r:t a) = VUnit (llist' r)
