module SL.Actions

open SL.Heap
open SL.Effect

let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (m:memory) = wp (fun a -> p a m)
sub_effect DIV ~> STATE = lift_div_st


let read_wp (#a:Type) (r:ref a) : st_wp a =
    (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post x m0)

assume val ( ! ) (#a:Type) (r:ref a) : ST a (read_wp r) [ii r]


let write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
  (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () (r |> v))

assume val ( := ) (#a:Type) (r:ref a) (v:a) :ST unit (write_wp r v) [ii r]


let alloc_wp (#a:Type) (v:a) : st_wp (ref a) =
  (fun post m0 -> forall (r:ref a). m0 == emp  /\ post r (r |> v))

assume val alloc (#a:Type) (v:a) : ST (ref a) (alloc_wp v) []


let free_wp (#a:Type) (r:ref a) : st_wp unit =
  (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () emp)

assume val free (#a:Type) (r:ref a) : ST unit (free_wp r) [ii r]
