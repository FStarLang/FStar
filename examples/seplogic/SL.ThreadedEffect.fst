module SL.ThreadedEffect

(* A variant of the separation logic state effect that has experimental support for fork and join. *)

open SL.ThreadedHeap

module OS = FStar.OrdSet

let pre = heap -> Type0
let post (a:Type) = a -> heap -> Type0
let st_wp (a:Type) = post a -> pre

let return_wp (a:Type) (x:a) :st_wp a = 
  fun post m0 -> post x m0

let frame_wp (#a:Type) (wp:st_wp a) (post:heap -> post a) (h:heap) =
  exists (m0 m1:memory). 
    defined (m0 <*> m1) /\ 
    heap_memory h == (m0 <*> m1) /\ 
    (let (h0,h1) = split_heap m0 m1 h in 
     wp (post h1) h0)

let frame_post (#a:Type) (p:post a) (h0:heap) :post a =
  fun x h1 -> 
    defined (heap_memory h1 <*> heap_memory h0) /\ p x (join h1 h0)

let bind_wp (r:range) (a:Type) (b:Type) (wp1:st_wp a) (wp2:a -> st_wp b)
  :st_wp b
  = fun post h0 -> 
      wp1 (fun x h1 -> wp2 x post h1) h0

let id_wp (a:Type) (x:a) (p:post a) (h:heap) = p x h

let st_if_then_else (a:Type) (p:Type) (wp_then:st_wp a) (wp_else:st_wp a) (post:post a) (h0:heap) =
  l_ITE p ((bind_wp range_0 a a wp_then (id_wp a)) post h0)
          ((bind_wp range_0 a a wp_else (id_wp a)) post h0)

let st_ite_wp (a:Type) (wp:st_wp a) (p:post a) (h0:heap) = wp p h0

let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
  forall (p:post a) (h:heap). wp1 p h ==> wp2 p h

let st_close_wp (a:Type) (b:Type) (wp:(b -> GTot (st_wp a))) (p:post a) (h:heap) =
  forall (b:b). wp b p h

let st_assert_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (h:heap) =
  p /\ wp q h

let st_assume_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (h:heap) =
  p ==> wp q h

let st_null_wp (a:Type) (p:post a) (h:heap) =
  forall (x:a) (h:heap). p x h

let st_trivial (a:Type) (wp:st_wp a) =
  forall h0. wp (fun _ _ -> True) h0
      
new_effect {
  STATE : result:Type -> wp:st_wp result -> Effect
  with return_wp    = return_wp
     ; bind_wp      = bind_wp
     ; if_then_else = st_if_then_else
     ; ite_wp       = st_ite_wp
     ; stronger     = st_stronger
     ; close_wp     = st_close_wp
     ; assert_p     = st_assert_p
     ; assume_p     = st_assume_p
     ; null_wp      = st_null_wp
     ; trivial      = st_trivial
}

let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (h:heap) = wp (fun a -> p a h)
sub_effect DIV ~> STATE = lift_div_st

let read_wp (#a:Type) (r:ref a) : st_wp a =
  fun post h0 -> 
    exists (x:a). heap_memory h0 == (r |> x) /\ post x h0

unfold
let frame_read_wp (#a:Type) (r:ref a) : st_wp a =
  fun post h0 -> 
    frame_wp (read_wp r) (frame_post post) h0

assume
val ( ! ) (#a:Type) (r:ref a) : STATE a (frame_read_wp r)

let write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
  fun post h0 -> 
    exists (x:a). heap_memory h0 == (r |> x) /\ post () (upd h0 r v)

unfold
let frame_write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
  fun post h0 -> 
    frame_wp (write_wp r v) (frame_post post) h0

assume
val ( := ) (#a:Type) (r:ref a) (v:a) : STATE unit (frame_write_wp r v)

let alloc_wp (#a:Type) (v:a) : st_wp (ref a) =
  fun post h0 -> 
    heap_memory h0 == emp /\ (let (r,h1) = alloc h0 v in post r h1)

unfold
let frame_alloc_wp (#a:Type) (v:a) : st_wp (ref a) =
  fun post h0 -> 
    frame_wp (alloc_wp v) (frame_post post) h0
   
assume
val alloc (#a:Type) (v:a) : STATE (ref a) (frame_alloc_wp v)

let dealloc_wp (#a:Type) (r:ref a) : st_wp unit =
  fun post h0 -> 
    exists x . heap_memory h0 == (r |> x) /\ post () (dealloc h0 r)

unfold
let frame_dealloc_wp (#a:Type) (r:ref a) : st_wp unit =
  fun post h0 -> 
    frame_wp (dealloc_wp r) (frame_post post) h0

assume
val dealloc (#a:Type) (r:ref a) : STATE unit (frame_dealloc_wp r)



(* threads *)

(*

Separation Logic triples for fork and join based on the deny-guarantee work.

(Based on "Deny-guarantee reasoning" by Dodds, Feng, Parkinson, and Vafeiadis.)

  {P} C {Q}     x not in FV(P,C,Q)
  -------------------------------- [T-fork]
  {P} x := fork C {Thread(x,Q)}

  
  ----------------------- [T-Join]
  {Thread(x,Q)} join x{Q}


For our WP-style presentation, we do not allow any sort of interference between threads, for now.

*)

let fork_wp (#a:Type0) (#r:ref a)
            (#fp:footprint) (#pre:heap -> Type0) (#post:heap -> Type0)
            (f:unit -> STATE unit (fun p h0 -> 
                                     fp_free fp (heap_memory h0) /\ pre h0 /\ 
                                     (forall h1 . (fp_free fp (heap_memory h1) /\ post h1) ==> p () h1))) 
          : st_wp (tid fp post) = 
  fun p h0 -> 
    fp_free fp (heap_memory h0) /\ pre h0 /\ 
    (let (t,h1) = alloc_tid fp post h0 in 
     p t h1)

unfold
let frame_fork_wp (#a:Type0) (#r:ref a)
                  (#fp:footprint) (#pre:heap -> Type0) (#post:heap -> Type0)
                  (f:unit -> STATE unit (fun p h0 -> 
                                           fp_free fp (heap_memory h0) /\ pre h0 /\ 
                                           (forall h1 . (fp_free fp (heap_memory h1) /\ post h1) ==> p () h1))) 
                : st_wp (tid fp post) =
  fun p h0 -> 
    frame_wp (fork_wp #a #r #fp #pre #post f) (frame_post p) h0

assume
val fork (#a:Type0) (#r:ref a)
         (#fp:footprint) (#pre:heap -> Type0) (#post:heap -> Type0)
         (f:unit -> STATE unit (fun p h0 -> 
                                  fp_free fp (heap_memory h0) /\ pre h0 /\ 
                                  (forall h1 . (fp_free fp (heap_memory h1) /\ post h1) ==> p () h1))) 
       : STATE (tid fp post) (frame_fork_wp #a #r #fp #pre #post f)

let join_wp (#a:Type0) (#r:ref a)
            (#fp:footprint) (#post:heap -> Type0)
            (t:tid fp post) : st_wp unit =
  fun p h0 -> 
    addrs_in (heap_memory h0) = fp /\ fp_locked_by t (heap_memory h0) /\ 
    (let h1 = dealloc_tid t h0 in
     post h1 ==> p () h1)

let frame_join_wp (#a:Type0) (#r:ref a)
                  (#fp:footprint) (#post:heap -> Type0)
                  (t:tid fp post) 
                : st_wp unit =
  fun p h0 -> 
    frame_wp (join_wp #a #r #fp #post t) (frame_post p) h0

assume
val join (#a:Type0) (#r:ref a)                               
         (#fp:footprint) (#post:heap -> Type0)
         (t:tid fp post)
       : STATE unit (frame_join_wp #a #r #fp #post t)
