module HoareST2

open FStar.Heap
open FStar.ST

#set-options "--max_fuel 0 --max_ifuel 0"

type pre_t = heap -> Type0
type post_t (a:Type) = a -> heap -> Type0

type repr (a:Type) (pre:pre_t) (post:post_t a) : Type =
  unit -> STATE a (fun p h -> pre h /\ (forall (x:a) (h1:heap). post x h1 ==> p x h1))

let return (a:Type) (x:a)
: repr a (fun _ -> True) (fun r _ -> r == x)
= fun _ -> x

let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (post_g:post_t b)
  (f:repr a pre_f post_f) (g:(x:a -> repr b (post_f x) post_g))
: repr b pre_f post_g
= fun _ ->
  let x = f () in
  g x ()

let stronger (a:Type)
  (pre_f:pre_t) (post_f:post_t a)
  (pre_g:pre_t) (post_g:post_t a)
  (f:repr a pre_f post_f)
: Pure (repr a pre_g post_g)
  (requires
    (forall (h:heap). pre_g h ==> pre_f h) /\
    (forall (x:a) (h:heap). post_f x h ==> post_g x h))
  (ensures fun _ -> True)
= f

let conjunction = unit

layered_effect {
  HoareST2 : a:Type -> pre:pre_t -> post:post_t a -> Effect
  with repr        = repr;
       return      = return;
       bind        = bind;
       stronger    = stronger;
       conjunction = conjunction
}

assume val wp_monotonic_pure (_:unit)
  : Lemma
    (forall (a:Type) (wp:pure_wp a).
       (forall (p q:pure_post a).
          (forall (x:a). p x ==> q x) ==>
          (wp p ==> wp q)))

assume val wp_monotonic_st (_:unit)
  : Lemma
    (forall (a:Type) (wp:st_wp a).
       (forall (p q:st_post a).
          (forall (x:a) (h:heap). p x h ==> q x h) ==>
          (forall (h:heap). wp p h ==> wp q h)))

let lift_pure_hoarest2 (a:Type) (wp:pure_wp a) (post:post_t a) (f:unit -> PURE a wp)
: repr a (fun h -> wp (fun x -> post x h)) post
= wp_monotonic_st ();
  wp_monotonic_pure ();
  fun _ ->
  f ()

sub_effect PURE ~> HoareST2 = lift_pure_hoarest2
