module ExampleALL

open SimpleHeap

new_effect ExALL = ALL_h SimpleHeap.heap

unfold let lift_div_exall (a:Type) (wp:pure_wp a) (p:all_post_h heap a) (h:heap) = wp (fun a -> p (V a) h)
sub_effect DIV ~> ExALL = lift_div_exall

open ExampleST

unfold let lift_exst_exall (a:Type) (wp:st_wp_h heap a) (p:all_post_h heap a) (h:heap) = wp (fun a -> p (V a)) h
sub_effect ExST ~> ExALL = lift_exst_exall

assume val get : unit -> ExALL heap (fun p h -> p (V h) h)
assume val put : h:heap -> ExALL unit (fun p _ -> p (V ()) h)
assume val raise_ : #a:Type -> e:exn -> ExALL a (fun p h -> p (E e) h)

assume val st_read_all : #a:Type0 -> r:ref a -> ExALL a (fun p h ->
  h `contains` r /\ p (V (sel h r)) h)

assume val st_write_all : #a:Type0 -> r:ref a -> v:a -> ExALL unit (fun p h ->
  h `contains` r /\
  (forall h1.
    modifies (only r) h h1 /\
    equal_dom h h1 /\
    h1 `contains` r /\
    sel h1 r == v
    ==> p (V ()) h1))
