module LowStar.STExn

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.HyperStack.ST

(***** STEXN effect for Low* *****)

#set-options "--max_fuel 0 --max_ifuel 1 --initial_ifuel 1"

noeq
type result (a:Type) =
  | V: a -> result a
  | E: exn -> result a

let stexn_pre = HS.mem -> Type
let stexn_post_with_pre (a:Type) (pre:Type) = result a -> (_:HS.mem{pre}) -> Type
let stexn_post (a:Type) = stexn_post_with_pre a True
let stexn_wp (a:Type) = stexn_post a -> stexn_pre

unfold
let stexn_ite (a:Type) (wp:stexn_wp a) (post:stexn_post a) (h0:HS.mem) =
  forall (k:stexn_post a).
    (forall (r:result a) (h1:HS.mem).{:pattern (guard_free (k r h1))} post r h1 ==> k r h1)
    ==> wp k h0

unfold
let stexn_return (a:Type) (x:a) (post:stexn_post a) = post (V x)

unfold
let stexn_bind (_:range)
  (a:Type) (b:Type)
  (wp_a:stexn_wp a) (wp_b:a -> stexn_wp b)
  (post:stexn_post b) (h0:HS.mem)
  = wp_a
      (fun ra h1 ->
       match ra with
       | V x     -> wp_b x post h1
       | E e     -> post (E e) h1) h0

unfold
let stexn_if_then_else
  (a:Type) (p:Type)
  (wp_then wp_else:stexn_wp a)
  (post:stexn_post a) (h0:HS.mem)
  = l_ITE p (wp_then post h0) (wp_else post h0)

unfold
let stexn_stronger (a:Type) (wp1 wp2:stexn_wp a) =
  forall (p:stexn_post a) (h:HS.mem). wp1 p h ==> wp2 p h

unfold
let stexn_close
  (a:Type) (b:Type)
  (wp:b -> stexn_wp a) (post:stexn_post a) (h:HS.mem)
  = forall (x:b). wp x post h

unfold
let stexn_assert
  (a:Type) (p:Type)
  (wp:stexn_wp a) (post:stexn_post a) (h:HS.mem)
  = p /\ wp post h

unfold
let stexn_assume
  (a:Type) (p:Type)
  (wp:stexn_wp a) (post:stexn_post a) (h:HS.mem)
  = p ==> wp post h

unfold
let stexn_null (a:Type) (post:stexn_post a) (h:HS.mem) =
  forall (r:result a). post r h

unfold
let stexn_trivial (a:Type) (wp:stexn_wp a) =
  forall (h0:HS.mem). wp (fun r h1 -> True) h0

new_effect {
  STEXN : a:Type -> wp:stexn_wp a -> Effect
  with
    return_wp    = stexn_return;
    bind_wp      = stexn_bind;
    if_then_else = stexn_if_then_else;
    ite_wp       = stexn_ite;
    stronger     = stexn_stronger;
    close_wp     = stexn_close;
    assert_p     = stexn_assert;
    assume_p     = stexn_assume;
    null_wp      = stexn_null;
    trivial      = stexn_trivial
}

unfold
let lift_st_stexn (a:Type) (wp:st_wp a) (post:stexn_post a) (h0:HS.mem) =
  wp (fun x h1 -> post (V x) h1) h0

sub_effect STATE ~> STEXN = lift_st_stexn

effect STExn (a:Type)
  (req:HS.mem -> Type) (ens:(h0:HS.mem -> stexn_post_with_pre a (req h0)))
  = STEXN a
    (fun (post:stexn_post a) (h0:HS.mem) ->
     req h0 /\ (forall r h1. (req h0 /\ ens h0 r h1) ==> post r h1))

effect StExn (a:Type) = STExn a (fun _ -> True) (fun _ _ _ -> True)


(***** Repr for the STEXN effect *****)

unfold
let repr (#a:Type) (r:result a) : either a exn =
  match r with
  | V x -> Inl x
  | E e -> Inr e

unfold
let repr_wp (a:Type) (wp:stexn_wp a) : st_wp (either a exn) =
  fun (post:st_post (either a exn)) (h0:HS.mem) ->
  wp (fun r h1 -> post (repr r) h1) h0

let repr_comp (a:Type) (wp:stexn_wp a) =
  unit -> STATE (either a exn) (repr_wp a wp)

assume val wp_monotonic_stexn (_:unit)
  : Lemma 
    (forall (a:Type) (wp:stexn_wp a).
       (forall (p q:stexn_post a).
          (forall (x:result a) (h:HS.mem). p x h ==> q x h) ==>
          (forall (h:HS.mem). wp p h ==> wp q h)))

let bind_repr (r:range)
  (a:Type) (wp_f:stexn_wp a) (f:repr_comp a wp_f)
  (b:Type) (wp_g:a -> stexn_wp b) (g:(x:a -> repr_comp b (wp_g x)))
  : repr_comp b (stexn_bind r a b wp_f wp_g)
  = wp_monotonic_stexn ();
    fun _ ->
    let r = f () in
    match r with
    | Inl x -> g x ()
    | Inr e -> Inr e

assume val wp_monotonic_st (_:unit)
  : Lemma
    (forall (a:Type) (wp:st_wp a).
       (forall (p q:st_post a).
          (forall (x:a) (h:HS.mem). p x h ==> q x h) ==>
          (forall (h:HS.mem). wp p h ==> wp q h)))

let lift_st_repr
  (a:Type) (wp_f:st_wp a) (f:unit -> STATE a wp_f)
  : repr_comp a (lift_st_stexn a wp_f)
  = wp_monotonic_st ();
    fun _ ->
    let x = f () in
    Inl x
