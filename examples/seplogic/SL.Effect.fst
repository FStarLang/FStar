module SL.Effect

open SepLogic.Heap

unfold let memory = m:memory{defined m}

let pre = memory -> Type0
let post (a:Type) = a -> memory -> Type0
let st_wp (a:Type) = post a -> pre

unfold let return_wp (a:Type) (x:a) :st_wp a = 
  fun post m0 -> m0 == emp /\ post x m0

unfold let frame_wp (#a:Type) (wp:st_wp a) (post:memory -> post a) (m:memory) =
  exists (m0 m1:memory). defined m /\ m == (m0 <*> m1) /\ wp (post m1) m0

unfold let frame_post (#a:Type) (p:post a) (m0:memory) :post a =
  fun x m1 -> defined (m1 <*> m0) /\ p x (m1 <*> m0)  //m1 is the frame

unfold let bind_wp (r:range) (a:Type) (b:Type) (wp1:st_wp a) (wp2:a -> st_wp b)
  :st_wp b
  = fun post m0 ->
    frame_wp wp1 (frame_post (fun x m1 -> frame_wp (wp2 x) (frame_post post) m1)) m0

unfold  let st_if_then_else (a:Type) (p:Type) (wp_then:st_wp a) (wp_else:st_wp a) (post:post a) (m0:memory) =
  l_ITE p (wp_then post m0) (wp_else post m0)

unfold  let st_ite_wp (a:Type) (wp:st_wp a) (p:post a) (m0:memory) =
  forall (k:post a).
    (forall (x:a) (m:memory).{:pattern (guard_free (k x m))} k x m <==> p x m)
    ==> wp k m0

unfold  let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
  forall (p:post a) (m:memory). wp1 p m ==> wp2 p m

unfold let st_close_wp (a:Type) (b:Type) (wp:(b -> GTot (st_wp a))) (p:post a) (m:memory) =
  forall (b:b). wp b p m

unfold  let st_assert_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (m:memory) =
  p /\ wp q m

unfold  let st_assume_p (a:Type) (p:Type) (wp:st_wp a) (q:post a) (m:memory) =
  p ==> wp q m

unfold  let st_null_wp (a:Type) (p:post a) (m:memory) =
  forall (x:a) (m:memory). p x m

unfold let st_trivial (a:Type) (wp:st_wp a) =
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

unfold let lift_div_st (a:Type) (wp:pure_wp a) (p:post a) (m:memory) = emp_defined(); wp (fun a -> p a emp)
sub_effect DIV ~> STATE = lift_div_st

assume
val ( ! ) (#a:Type) (r:ref a)
  :STATE a (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post x m0)

assume
val ( := ) (#a:Type) (r:ref a) (v:a)
  :STATE unit (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post () (r |> v))




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

