module LListWithTail.Cell

#push-options "--__no_positivity"
noeq
type cell (a: Type0) = {
  next: ref (option (cell a));
  data: a;
}
#pop-options


let next c = c.next
let data c = c.data
let mk_cell n d = {
  next = n;
  data = d
}
