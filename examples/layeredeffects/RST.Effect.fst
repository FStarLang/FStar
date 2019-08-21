module RST.Effect

open FStar.HyperStack.ST

open Steel.Resource
open Steel.RST

module HS = FStar.HyperStack

type rst_pre (r:resource) = rprop r  //rprop is rmem r -> Type0
type rst_post (a:Type) (r:a -> resource) = x:a -> rprop (r x)

type rst_wp' (a:Type) (r_in:resource) (r_out:a -> resource) = rst_post a r_out -> rst_pre r_in

let rst_wp_monotonic (a:Type) (r_in:resource) (r_out:a -> resource) (wp:rst_wp' a r_in r_out) =
  forall (p q:rst_post a r_out).
    (forall x h. p x h ==> q x h) ==>
    (forall h. wp p h ==> wp q h)

type rst_wp (a:Type) (r_in:resource) (r_out:a -> resource) = wp:rst_wp' a r_in r_out{rst_wp_monotonic a r_in r_out wp}

type repr (a:Type) (r_in:resource) (r_out:a -> resource) (wp:rst_wp a r_in r_out) =
  unit -> 
  STATE a (fun p h0 ->
    inv r_in h0 /\ rst_inv r_in h0 /\
    wp
      (fun (x:a) (h_r_out:rmem (r_out x)) ->
        forall h1. (mk_rmem (r_out x) h1 == h_r_out /\
               inv (r_out x) h1 /\
               rst_inv (r_out x) h1 /\
               modifies r_in (r_out x) h0 h1) ==> p x h1)
      (mk_rmem r_in h0))

unfold let emp = empty_resource

let return (a:Type) (x:a)
: repr a emp (fun _ -> emp) (fun p rm -> p x rm)
= fun _ -> x

let bind (a:Type) (b:Type)
  (r_in_f:resource) (r_out_f:a -> resource) (wp_f:rst_wp a r_in_f r_out_f)
  (r_out_g:b -> resource) (wp_g:(x:a -> rst_wp b (r_out_f x) r_out_g))
  (f:repr a r_in_f r_out_f wp_f)
  (g:(x:a -> repr b (r_out_f x) r_out_g (wp_g x)))
: repr b r_in_f r_out_g (fun p rm0 -> wp_f (fun x rm1 -> (wp_g x) p rm1) rm0)
= fun _ ->
  let x = f () in
  g x ()

let stronger (a:Type)
  (r_in_f:resource) (r_out_f:a -> resource) (wp_f:rst_wp a r_in_f r_out_f)
  (r_in_g:resource) (r_out_g:a -> resource) (wp_g:rst_wp a r_in_g r_out_g)
  (f:repr a r_in_f r_out_f wp_f)
: Pure (repr a r_in_g r_out_g wp_g)
  (requires
    r_in_f == r_in_g /\ r_out_f == r_out_g /\
    (forall p h. wp_g p h ==> wp_f p h))
  (ensures fun _ -> True)
= f

let conjunction = unit

layered_effect {
  RSTATE : a:Type -> r_in:resource -> r_out:(a -> resource) -> wp:rst_wp a r_in r_out -> Effect
  with repr        = repr;
       return      = return;
       bind        = bind;
       stronger    = stronger;
       conjunction = conjunction
}

assume Pure_wp_monotonicity:
  forall (a:Type) (wp:pure_wp a).
    (forall (p q:pure_post a).
       (forall (x:a). p x ==> q x) ==>
       (wp p ==> wp q))

let lift_pure_rstate (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
: repr a emp (fun _ -> emp) (fun p h -> wp (fun x -> p x h))
= fun _ -> f ()

sub_effect PURE ~> RSTATE = lift_pure_rstate


effect RST (a:Type)
  (r_in:resource) (r_out:a -> resource)
  (pre:rprop r_in) (post:rmem r_in -> (x:a) -> rprop (r_out x))
= RSTATE a r_in r_out
  (fun (p:rst_post a r_out) (h0:rmem r_in) -> pre h0 /\ (forall (x:a) (h1:rmem (r_out x)). post h0 x h1 ==> p x h1))

#set-options "--log_queries --z3refresh"
let test ()
: RST int emp (fun _ -> emp) (fun _ -> True) (fun _ r _ -> r > 1)
= 2


// type pre_t (r:resource) = rprop r
// type post_t (a:Type) (r_in:resource) (r_out:a -> resource) =
//   rmem r_in -> x:a -> rprop (r_out x)

// type repr (a:Type)
//   (r_in:resource) (r_out:a -> resource)
//   (pre:pre_t r_in) (post:post_t a r_in r_out)
// = unit ->
//   ST a
//   (fun h ->
//     inv r_in h /\
//     rst_inv r_in h /\
//     pre (mk_rmem r_in h))
//   (fun h0 x h1 ->
//     inv (r_out x) h1 /\
//     rst_inv (r_out x) h1 /\
//     modifies r_in (r_out x) h0 h1 /\
//     post (mk_rmem r_in h0) x (mk_rmem (r_out x) h1))

// unfold let emp = empty_resource

// let return (a:Type) (x:a)
// : repr a emp (fun _ -> emp)
//   (fun (_:rmem emp) -> True)
//   (fun (_:rmem emp) (y:a) (_:rmem emp) -> y == x)
// = fun _ -> x

// let bind (a:Type) (b:Type)
//   (r_in_f:resource) (r_out_f:a -> resource)
//   (pre_f:pre_t r_in_f) (post_f:post_t a r_in_f r_out_f)
//   (r_out_g:b -> resource)
//   (pre_g:(x:a -> pre_t (r_out_f x))) (post_g:(x:a -> post_t b (r_out_f x) r_out_g))
//   (f:repr a r_in_f r_out_f pre_f post_f)
//   (g:(x:a -> repr b (r_out_f x) r_out_g (pre_g x) (post_g x)))
// : repr b r_in_f r_out_g
//   (fun (h:rmem r_in_f) ->
//     pre_f h /\
//     (forall (x:a) (h1:rmem (r_out_f x)).
//        post_f h x h1 ==> pre_g x h1))    
//   (fun (h0:rmem r_in_f) (x:b) (h1:rmem (r_out_g x)) ->
//     exists (y:a) (h:rmem (r_out_f y)).
//       post_f h0 y h /\ (post_g y) h x h1)
// = fun _ ->
//   let r = f () in
//   (g r) ()

// let stronger (a:Type)
//   (r_in_f:resource) (r_out_f:a -> resource)
//   (pre_f:pre_t r_in_f) (post_f:post_t a r_in_f r_out_f)
//   (r_in_g:resource) (r_out_g:a -> resource)
//   (pre_g:pre_t r_in_g) (post_g:post_t a r_in_g r_out_g)
//   (f:repr a r_in_f r_out_f pre_f post_f)
// : Pure (repr a r_in_g r_out_g pre_g post_g)
//   (requires
//     r_in_f == r_in_g /\ r_out_f == r_out_g /\
//     (forall (h:rmem r_in_f). pre_g h ==> pre_f h) /\
//     (forall (h0:rmem r_in_f) (x:a) (h1:rmem (r_out_f x)). post_f h0 x h1 ==> post_g h0 x h1))
//   (ensures fun _ -> True)
// = f

// let conjunction = unit

