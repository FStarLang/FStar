(*
   A simple heap model for use in layered effect examples.
*)
module FStar.SimpleHeap

module S = FStar.Set
module F = FStar.FunctionalExtensionality

(** Internal cell type: stores a typed value *)
private noeq type cell = | Cell : a:Type0 -> v:a -> cell

(** Internal heap record *)
private noeq type heap_rec = {
  next: pos;
  mem: F.restricted_t nat (fun _ -> option cell);
}

(** Heap invariant: addresses >= next are unused *)
let heap = h:heap_rec{forall (n:nat). n >= h.next ==> None? (h.mem n)}

(** Reference: just a positive nat address *)
let ref a = pos

let ref_equal #a #b r1 r2 = r1 = r2

let addr_of #a r = r

let addr_of_injective #a r1 r2 = ()

let ref_equal_addr #a #b r1 r2 = ()

let contains #a h r =
  r > 0 /\
  Some? (h.mem r) /\
  (let Some (Cell a' _) = h.mem r in a == a')

let addr_unused_in n h = None? (h.mem n)

let unused_in #a r h = addr_unused_in (addr_of r) h

let sel #a h r =
  let Some (Cell _ v) = h.mem r in
  v

let upd #a h r x =
  { h with mem = F.on_dom nat (fun n -> if n = r then Some (Cell a x) else h.mem n) }

let alloc #a h x =
  let r : ref a = h.next in
  let h' : heap = {
    next = h.next + 1;
    mem = F.on_dom nat (fun n -> if n = r then Some (Cell a x) else h.mem n);
  } in
  (r, h')

let next_addr h = h.next

let contains_upd #a #b h r x r' =
  ()

let sel_upd_same #a h r x =
  ()

let sel_upd_other #a #b h r1 x r2 =
  ()

let alloc_fresh #a h x =
  ()

let alloc_contains #a #b h x r =
  ()

let unused_not_contains #a h r =
  ()

let contains_not_unused #a h r =
  ()
