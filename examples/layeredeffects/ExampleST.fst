module ExampleST

open SimpleHeap

new_effect ExST = STATE_h SimpleHeap.heap

unfold let lift_div_exst (a:Type) (wp:pure_wp a) (p:st_post_h heap a) (h:heap) = wp (fun a -> p a h)
sub_effect DIV ~> ExST = lift_div_exst

assume val get : unit -> ExST heap (fun p h -> p h h)
assume val put : h:heap -> ExST unit (fun p _ -> p () h)

assume val st_alloc : #a:Type0 -> init:a -> ExST (ref a) (fun p h ->
  forall r h1.
    fresh r h h1 /\
    sel h1 r == init /\
    (forall (b:Type0) (r':ref b). h `contains` r' ==> h1 `contains` r' /\ sel h1 r' == sel h r')
    ==> p r h1)

assume val st_read : #a:Type0 -> r:ref a -> ExST a (fun p h ->
  h `contains` r /\ p (sel h r) h)

assume val st_write : #a:Type0 -> r:ref a -> v:a -> ExST unit (fun p h ->
  h `contains` r /\
  (forall h1.
    modifies (only r) h h1 /\
    equal_dom h h1 /\
    h1 `contains` r /\
    sel h1 r == v
    ==> p () h1))
