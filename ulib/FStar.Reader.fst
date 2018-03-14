module FStar.Reader
let reader_pre_h  (heap:Type)          = heap -> GTot Type0
let reader_post_h (a:Type)             = a -> GTot Type0
let reader_wp_h   (heap:Type) (a:Type) = reader_post_h a -> Tot (reader_pre_h heap)

unfold let reader_return        (heap:Type) (a:Type)
                               (x:a) (p:reader_post_h a) (h0:heap) = p x
unfold let reader_bind_wp   (heap:Type) 
			    (r1:range) 
			    (a:Type) (b:Type)
                            (wp1:reader_wp_h heap a)
                            (wp2:(a -> GTot (reader_wp_h heap b)))
                            (p:reader_post_h b) (h0:heap) =
     labeled r1 "push" unit
     /\ wp1 (fun a ->
       labeled r1 "pop" unit
       /\ wp2 a p h0) h0
unfold let reader_if_then_else  (heap:Type) (a:Type) (p:Type)
                             (wp_then:reader_wp_h heap a) (wp_else:reader_wp_h heap a)
                             (post:reader_post_h a) (h0:heap) =
     l_ITE p
        (wp_then post h0)
	(wp_else post h0)
unfold let reader_ite_wp        (heap:Type) (a:Type)
                            (wp:reader_wp_h heap a)
                            (post:reader_post_h a) (h0:heap) =
     forall (k:reader_post_h a).
	 (forall (x:a).{:pattern (guard_free (k x))} post x ==> k x)
	 ==> wp k h0
unfold let reader_stronger  (heap:Type) (a:Type) (wp1:reader_wp_h heap a)
                        (wp2:reader_wp_h heap a) =
     (forall (p:reader_post_h a) (h:heap). wp1 p h ==> wp2 p h)

unfold let reader_close_wp      (heap:Type) (a:Type) (b:Type)
                             (wp:(b -> GTot (reader_wp_h heap a)))
                             (p:reader_post_h a) (h:heap) =
     (forall (b:b). wp b p h)
unfold let reader_assert_p      (heap:Type) (a:Type) (p:Type)
                             (wp:reader_wp_h heap a)
                             (q:reader_post_h a) (h:heap) =
     p /\ wp q h
unfold let reader_assume_p      (heap:Type) (a:Type) (p:Type)
                             (wp:reader_wp_h heap a)
                             (q:reader_post_h a) (h:heap) =
     p ==> wp q h
unfold let reader_null_wp       (heap:Type) (a:Type)
                             (p:reader_post_h a) (h:heap) =
     (forall (x:a). p x)
unfold let reader_trivial       (heap:Type) (a:Type)
                             (wp:reader_wp_h heap a) =
     (forall h0. wp (fun r -> True) h0)

new_effect {
  READER_h (heap:Type) : result:Type -> wp:reader_wp_h heap result -> Effect
  with return_wp    = reader_return heap
     ; bind_wp      = reader_bind_wp heap
     ; if_then_else = reader_if_then_else heap
     ; ite_wp       = reader_ite_wp heap
     ; stronger     = reader_stronger heap
     ; close_wp     = reader_close_wp heap
     ; assert_p     = reader_assert_p heap
     ; assume_p     = reader_assume_p heap
     ; null_wp      = reader_null_wp heap
     ; trivial      = reader_trivial heap
}
open FStar.Heap
new_effect READER = READER_h FStar.Heap.heap

effect STRead (a:Type) (pre: (heap -> Type0)) (post:heap -> a -> Type0) = 
  READER a (fun (p:reader_post_h a) h0 -> pre h0 /\ (forall (x:a). post h0 x ==> p x))

open FStar.ST
assume val read:  #a:Type -> r:ref a -> STRead a
					 (requires (fun h -> True))
					 (ensures (fun h x -> x == sel h r))

unfold let lift_reader_state (a:Type) (wp:reader_wp_h heap a) (p:st_post a) (h:heap) = wp (fun a -> p a h) h
sub_effect READER ~> STATE = lift_reader_state
unfold let lift_div_reader (a:Type) (wp:pure_wp a) (p:reader_post_h a) (h:heap) = wp p
sub_effect DIV ~> READER = lift_div_reader

(* Testing *)

let f (r:ref int) : STRead int 
  (requires (fun h -> True))
  (ensures (fun h x -> x = sel h r + 1) )
  = read r + 1


let g (r:ref int) (s:ref int) : ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> sel h1 r = (sel h0 r + 1) + (sel h0 s + 1)))
  = let x = f r in
    let y = f s in
    r := x + y
