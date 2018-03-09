module SL.Effect
open SepLogic.Heap

let pre = heap -> Type0
let post (a:Type) = a -> heap -> Type0
let st_wp (a:Type) = post a -> pre

unfold let return_wp (a:Type) (x:a) :st_wp a = 
  fun post h0 -> h0 == emp /\ post x h0

unfold let frame_wp (#a:Type) (wp:st_wp a) (post:heap -> post a) (h:heap) =
  exists (h0 h1:heap). h == (h0 <*> h1) /\ wp (post h1) h0

unfold let frame_post (#a:Type) (p:post a) (h:heap) :post a =
  fun x h1 -> p x (h1 <*> h)  //h1 is the frame

unfold let bind_wp (r:range) (a:Type) (b:Type) (wp1:st_wp a) (wp2:a -> st_wp b)
  :st_wp b
  = fun post h ->
    frame_wp wp1 (frame_post (fun x h1 -> frame_wp (wp2 x) (frame_post post) h1)) h

unfold  let st_if_then_else (a:Type) (p:Type) (wp_then:st_wp a) (wp_else:st_wp a) (post:post a) (h0:heap) =
  l_ITE p (wp_then post h0) (wp_else post h0)

unfold  let st_ite_wp (a:Type) (wp:st_wp a) (p:post a) (h0:heap) =
  forall (k:post a).
    (forall (x:a) (h:heap).{:pattern (guard_free (k x h))} k x h <==> p x h)
    ==> wp k h0

unfold  let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
  forall (p:post a) (h:heap). wp1 p h ==> wp2 p h

unfold let st_close_wp (a:Type) (b:Type) (wp:(b -> GTot (st_wp a))) (p:post a) (h:heap) =
  forall (b:b). wp b p h

unfold  let st_assert_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (h:heap) =
  p /\ wp q h

unfold  let st_assume_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (h:heap) =
  p ==> wp q h

unfold  let st_null_wp (a:Type) (p:post a) (h:heap) =
  forall (x:a) (h:heap). p x h

unfold let st_trivial (a:Type) (wp:st_wp a) =
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

unfold let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (h:heap) = wp (fun a -> p a emp)
sub_effect DIV ~> STATE = lift_div_st

assume
val ( ! ) (#a:Type) (r:ref a)
  :STATE a (fun post h0 -> exists (x:a). h0 == (r |> x) /\ post x h0)

assume
val ( := ) (#a:Type) (r:ref a) (v:a)
  :STATE unit (fun post h0 -> exists (x:a). h0 == (r |> x) /\ post () (r |> v))

// open SL.Tactics
// open FStar.Tactics.Builtins
// open FStar.Tactics.Logic

// #set-options "--print_full_names"
// //sequential composition
// let swap (r:ref int) (s:ref int) =
//   (let x = !r in
//    let y = !s in
//    r := y;
//    s := x)
//   <: STATE unit (fun post h0 -> exists x y. h0 == join_tot (points_to r x) (points_to s y)
//                                   /\ post () (join_tot (points_to r y) (points_to s x)))
//   by (fun () -> dump "A"; 
//              let post = FStar.Tactics.forall_intro () in
//              let h0 = FStar.Tactics.forall_intro () in             
//              let pre = implies_intro () in
//              dump "B"; 
//              FStar.Tactics.Derived.admit1(); //NS: not sure how the existing SL.Tactics.solve is supposed to tackle this
//              qed())

// //branching
// let conditional_swap (r:ref int) (s:ref int) =
//   let x = !r in
//   if x = 0 then
//    let y = !s in
//    r := y

// //recursion
// let rec decr_n (n:nat) (r:ref int) : STATE unit (fun post h -> False) = 
//   if n <> 0 then ()
//   else (r := !r - 1; decr_n (n - 1) r)

