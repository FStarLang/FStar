module SL.Effect

open SL.Heap

let pre = memory -> Type0
let post (a:Type) = a -> memory -> Type0
let st_wp (a:Type) = post a -> pre

(* unfold *) let return_wp (a:Type) (x:a) :st_wp a = 
  fun post m0 -> post x m0

(* unfold *) let frame_wp (#a:Type) (wp:st_wp a) (post:memory -> post a) (m:memory) =
  exists (m0 m1:memory). defined (m0 <*> m1) /\ m == (m0 <*> m1) /\ wp (post m1) m0

(* unfold *) let frame_post (#a:Type) (p:post a) (m0:memory) :post a =
  fun x m1 -> defined (m1 <*> m0) /\ p x (m1 <*> m0)  //m1 is the frame

(* unfold *) let bind_wp (r:range) (a:Type) (b:Type) (wp1:st_wp a) (wp2:a -> st_wp b)
  :st_wp b
  = fun post m0 -> wp1 (fun x m1 -> wp2 x post m1) m0
    // frame_wp wp1 (frame_post (fun x m1 -> frame_wp (wp2 x) (frame_post post) m1)) m0

(* unfold *) let id_wp (a:Type) (x:a) (p:post a) (m:memory) = p x emp

(* unfold *)  let st_if_then_else (a:Type) (p:Type) (wp_then:st_wp a) (wp_else:st_wp a) (post:post a) (m0:memory) =
  l_ITE p (wp_then post m0) (wp_else post m0)
  // l_ITE p ((bind_wp range_0 a a wp_then (id_wp a)) post m0)
  //         ((bind_wp range_0 a a wp_else (id_wp a)) post m0)

(* unfold *)  let st_ite_wp (a:Type) (wp:st_wp a) (p:post a) (m0:memory) = wp p m0

(* unfold *)  let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
  forall (p:post a) (m:memory). wp1 p m ==> wp2 p m

(* unfold *) let st_close_wp (a:Type) (b:Type) (wp:(b -> GTot (st_wp a))) (p:post a) (m:memory) =
  forall (b:b). wp b p m

(* unfold *)  let st_assert_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (m:memory) =
  p /\ wp q m

(* unfold *)  let st_assume_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (m:memory) =
  p ==> wp q m

(* unfold *)  let st_null_wp (a:Type) (p:post a) (m:memory) =
  forall (x:a) (m:memory). p x m

(* unfold *) let st_trivial (a:Type) (wp:st_wp a) =
  forall m0. wp (fun _ _ -> True) m0
      
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

(* unfold *) let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (m:memory) = wp (fun a -> p a m)
sub_effect DIV ~> STATE = lift_div_st

let read_wp (#a:Type) (r:ref a) : st_wp a =
    (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post x m0)

unfold
let frame_read_wp (#a:Type) (r:ref a) : st_wp a =
   fun post m0 -> frame_wp (read_wp r) (frame_post post) m0

assume
val ( ! ) (#a:Type) (r:ref a)
  :STATE a (frame_read_wp r)

let write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
  (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () (r |> v))

unfold
let frame_write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
   fun post m0 -> frame_wp (write_wp r v) (frame_post post) m0

assume
val ( := ) (#a:Type) (r:ref a) (v:a)
  :STATE unit (frame_write_wp r v)
