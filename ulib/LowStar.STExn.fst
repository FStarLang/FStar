module LowStar.STExn

open FStar.Heap
open FStar.ST

// type pre_t = Type0
// type post_t (a:Type) = Type0

// #set-options "--print_universes"

// type repr (a:Type) (pre:pre_t) (post:post_t a) : Type =
//   unit -> PURE a (fun p -> forall (x:a). p x)

// let return (a:Type) (x:a)
// : repr a True True
// = fun _ -> x

// let bind (a:Type) (b:Type)
//   (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:a -> post_t b)
//   (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) (post_g x)))
// : repr b True True
// = fun _ ->
//   let x = f () in
//   g x ()

// let stronger (a:Type)
//   (pre_g:pre_t) (post_g:post_t a)
//   (pre_f:pre_t) (post_f:post_t a)
//   (f:repr a pre_f post_f)
// : Pure (repr a pre_g post_g)
//   (requires True)
//   (ensures fun _ -> True)
// = f

// let conjunction (a:Type)
//   (pre_f:pre_t) (post_f:post_t a)
//   (pre_g:pre_t) (post_g:post_t a)
//   : Type
// = repr a True True

// // let conjunction_is_stronger_f (a:Type)
// //   (pre_f:pre_t) (post_f:post_t a)
// //   (pre_g:pre_t) (post_g:post_t a)
// //   (f:repr a pre_f post_f)
// // : Tot _
// // = stronger a (fun h -> pre_f h /\ pre_g h) (fun h0 r h1 -> post_f h0 r h1 \/ post_g h0 r h1) pre_f post_f f

// // let conjunction_is_stronger_g (a:Type)
// //   (pre_f:pre_t) (post_f:post_t a)
// //   (pre_g:pre_t) (post_g:post_t a)
// //   (f:repr a pre_g post_g)
// // : Tot _
// // = stronger a (fun h -> pre_f h /\ pre_g h) (fun h0 r h1 -> post_f h0 r h1 \/ post_g h0 r h1) pre_g post_g f

// layered_effect {
//   Useless : a:Type -> pre:pre_t -> post:post_t a -> Effect
//   with repr        = repr;
//        return      = return;
//        bind        = bind;
//        stronger    = stronger;
//        conjunction = conjunction
// }

type pre_t = heap -> Type0
type post_t (a:Type) = heap -> a -> heap -> Type0

#set-options "--print_universes"

type repr (a:Type) (pre:pre_t) (post:post_t a) : Type =
  unit -> STATE a (fun p h -> pre h /\ (forall (x:a) (h1:heap). post h x h1 ==> p x h1))

let return (a:Type) (x:a)
: repr a (fun _ -> True) (fun h0 r h1 -> r == x /\ h0 == h1)
= fun _ -> x

let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:a -> post_t b)
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) (post_g x)))
: repr b
  (fun h0 -> pre_f h0 /\ (forall (x:a) (h1:heap). post_f h0 x h1 ==> pre_g x h1))
  (fun h0 y h2 -> exists (x:a) (h1:heap). post_f h0 x h1 /\ post_g x h1 y h2)
= fun _ ->
  let x = f () in
  g x ()

let stronger (a:Type)
  (pre_g:pre_t) (post_g:post_t a)
  (pre_f:pre_t) (post_f:post_t a)
  (f:repr a pre_f post_f)
: Pure (repr a pre_g post_g)
  (requires
    (forall (h:heap). pre_g h ==> pre_f h) /\
    (forall (h0 h1:heap) (x:a). post_f h0 x h1 ==> post_g h0 x h1))
  (ensures fun _ -> True)
= f

let conjunction (a:Type)
  (pre_f:pre_t) (post_f:post_t a)
  (pre_g:pre_t) (post_g:post_t a)
  : Type
= repr a
  (fun h -> pre_f h /\ pre_g h)
  (fun h0 r h1 -> post_f h0 r h1 \/ post_g h0 r h1)

let conjunction_is_stronger_f (a:Type)
  (pre_f:pre_t) (post_f:post_t a)
  (pre_g:pre_t) (post_g:post_t a)
  (f:repr a pre_f post_f)
: Tot _
= stronger a (fun h -> pre_f h /\ pre_g h) (fun h0 r h1 -> post_f h0 r h1 \/ post_g h0 r h1) pre_f post_f f

let conjunction_is_stronger_g (a:Type)
  (pre_f:pre_t) (post_f:post_t a)
  (pre_g:pre_t) (post_g:post_t a)
  (f:repr a pre_g post_g)
: Tot _
= stronger a (fun h -> pre_f h /\ pre_g h) (fun h0 r h1 -> post_f h0 r h1 \/ post_g h0 r h1) pre_g post_g f

layered_effect {
  HoareST : a:Type -> pre:pre_t -> post:post_t a -> Effect
  with repr        = repr;
       return      = return;
       bind        = bind;
       stronger    = stronger;
       conjunction = conjunction
}

// module HS = FStar.HyperStack
// module ST = FStar.HyperStack.ST

// open FStar.HyperStack.ST

// /// Encoding hoare_st a pre post as a layered effect on top of STATE (rather than defining it in terms of STATE)


// /// Think of this definition below as repr of a layered effect hoare_st
// ///
// /// The main difference being, in layered effect, this definition only provides a model of hoare_st
// ///
// /// The typechecker would not unfold hoare_st to construct the VCs etc.

// type hoare_st (a:Type) (pre:HS.mem -> Type0) (post:HS.mem -> a -> HS.mem -> Type0) =
//   unit -> STATE a (fun p h0 -> pre h0 /\ (forall (x:a) (h1:HS.mem). post h0 x h1 ==> p x h1))


// /// For return and bind, the implementation provides the instantiation of indices of hoare_st

// let hoare_st_return (a:Type) (x:a)
//   : hoare_st a (fun _ -> True) (fun h0 y h1 -> h0 == h1 /\ y == x)
//   = fun _ -> x

// let hoare_st_bind (a:Type) (b:Type)
//   (pre1:HS.mem -> Type0) (post1:HS.mem -> a -> HS.mem -> Type0)
//   (pre2:a -> HS.mem -> Type0) (post2:a -> HS.mem -> b -> HS.mem -> Type0)
//   (f1:hoare_st a pre1 post1) (f2:(x:a -> hoare_st b (pre2 x) (post2 x)))
//   : hoare_st b
//     (fun h0 -> pre1 h0 /\ (forall (x:a) (h1:HS.mem). post1 h0 x h1 ==> pre2 x h1))
//     (fun h0 y h2 -> exists (x:a) (h1:HS.mem). post1 h0 x h1 /\ post2 x h1 y h2)
//   = fun _ ->
//     let x = f1 () in
//     f2 x ()

// unfold
// let hoare_st_stronger (a:Type)
//   (pre1:HS.mem -> Type0) (post1:HS.mem -> a -> HS.mem -> Type0)
//   (pre2:HS.mem -> Type0) (post2:HS.mem -> a -> HS.mem -> Type0)
//   = (forall (h:HS.mem). pre1 h ==> pre2 h) /\
//     (forall (h0:HS.mem) (x:a) (h1:HS.mem). post2 h0 x h1 ==> post1 h0 x h1)

// unfold
// let hoare_st_stronger_is_consistent (a:Type)
//   (pre1:HS.mem -> Type0) (post1:HS.mem -> a -> HS.mem -> Type0)
//   (pre2:HS.mem -> Type0) (post2:HS.mem -> a -> HS.mem -> Type0)
//   : Lemma (requires hoare_st_stronger a pre1 post1 pre2 post2)
//           (ensures forall (u:unit).
//             st_stronger HS.mem a (fun p h0 -> pre1 h0 /\ (forall (x:a) (h1:HS.mem). post1 h0 x h1 ==> p x h1))
//                                  (fun p h0 -> pre2 h0 /\ (forall (x:a) (h1:HS.mem). post2 h0 x h1 ==> p x h1)))
//   = ()


// // (***** STEXN effect for Low* *****)

// #set-options "--max_fuel 0 --max_ifuel 1 --initial_ifuel 1"

// noeq
// type result (a:Type) =
//   | V: a -> result a
//   | E: exn -> result a

// let stexn_pre = HS.mem -> Type
// let stexn_post_with_pre (a:Type) (pre:Type) = result a -> (_:HS.mem{pre}) -> Type
// let stexn_post (a:Type) = stexn_post_with_pre a True
// let stexn_wp (a:Type) = stexn_post a -> stexn_pre

// unfold
// let stexn_ite (a:Type) (wp:stexn_wp a) (post:stexn_post a) (h0:HS.mem) =
//   forall (k:stexn_post a).
//     (forall (r:result a) (h1:HS.mem).{:pattern (guard_free (k r h1))} post r h1 ==> k r h1)
//     ==> wp k h0

// unfold
// let stexn_return (a:Type) (x:a) (post:stexn_post a) = post (V x)

// unfold
// let stexn_bind (_:range)
//   (a:Type) (b:Type)
//   (wp_a:stexn_wp a) (wp_b:a -> stexn_wp b)
//   : stexn_wp b
//   = fun (post:stexn_post b) (h0:HS.mem) ->
//     wp_a
//       (fun ra h1 ->
//        match ra with
//        | V x     -> wp_b x post h1
//        | E e     -> post (E e) h1) h0

// unfold
// let stexn_if_then_else
//   (a:Type) (p:Type)
//   (wp_then wp_else:stexn_wp a)
//   : stexn_wp a
//   = fun (post:stexn_post a) (h0:HS.mem) ->
//     l_ITE p (wp_then post h0) (wp_else post h0)

// unfold
// let stexn_stronger (a:Type) (wp1 wp2:stexn_wp a) =
//   forall (p:stexn_post a) (h:HS.mem). wp1 p h ==> wp2 p h

// unfold
// let stexn_close
//   (a:Type) (b:Type)
//   (wp:b -> stexn_wp a)
//   : stexn_wp a
//   = fun (post:stexn_post a) (h:HS.mem) ->
//     forall (x:b). wp x post h

// unfold
// let stexn_assert
//   (a:Type) (p:Type)
//   (wp:stexn_wp a)
//   : stexn_wp a
//   = fun (post:stexn_post a) (h:HS.mem) ->
//     p /\ wp post h

// unfold
// let stexn_assume
//   (a:Type) (p:Type)
//   (wp:stexn_wp a)
//   : stexn_wp a
//   = fun (post:stexn_post a) (h:HS.mem) ->
//     p ==> wp post h

// unfold
// let stexn_null (a:Type) : stexn_wp a =
//   fun (post:stexn_post a) (h:HS.mem) ->
//     forall (r:result a). post r h

// unfold
// let stexn_trivial (a:Type) (wp:stexn_wp a) =
//   forall (h0:HS.mem). wp (fun r h1 -> True) h0

// new_effect {
//   STEXN : a:Type -> wp:stexn_wp a -> Effect
//   with
//     return_wp    = stexn_return;
//     bind_wp      = stexn_bind;
//     if_then_else = stexn_if_then_else;
//     ite_wp       = stexn_ite;
//     stronger     = stexn_stronger;
//     close_wp     = stexn_close;
//     assert_p     = stexn_assert;
//     assume_p     = stexn_assume;
//     null_wp      = stexn_null;
//     trivial      = stexn_trivial
// }

// unfold
// let raise_wp (a:Type) (e:exn) : stexn_wp a =
//   fun (post:stexn_post a) (h:HS.mem) -> post (E e) h

// assume val raise (#a:Type) (e:exn)
//   : STEXN a (raise_wp a e)

// unfold
// let trywith_wp (a:Type)
//   (try_wp:stexn_wp a) (with_wp:exn -> stexn_wp a)
//   : stexn_wp a
//   = fun (post:stexn_post a) (h0:HS.mem) ->
//     try_wp
//       (fun r h1 ->
//        match r with
//        | V x -> post (V x) h1
//        | E e -> (with_wp e) post h1) h0

// unfold
// let lift_st_stexn (a:Type) (wp:st_wp a) (post:stexn_post a) (h0:HS.mem) =
//   wp (fun x h1 -> post (V x) h1) h0

// sub_effect STATE ~> STEXN = lift_st_stexn

// effect STExn (a:Type)
//   (req:HS.mem -> Type) (ens:(h0:HS.mem -> stexn_post_with_pre a (req h0)))
//   = STEXN a
//     (fun (post:stexn_post a) (h0:HS.mem) ->
//      req h0 /\ (forall r h1. (req h0 /\ ens h0 r h1) ==> post r h1))

// effect StExn (a:Type) = STExn a (fun _ -> True) (fun _ _ _ -> True)


// (***** Repr for the STEXN effect *****)

// unfold
// let repr (#a:Type) (r:result a) : either a exn =
//   match r with
//   | V x -> Inl x
//   | E e -> Inr e

// unfold
// let repr_wp (a:Type) (wp:stexn_wp a) : st_wp (either a exn) =
//   fun (post:st_post (either a exn)) (h0:HS.mem) ->
//   wp (fun r h1 -> post (repr r) h1) h0

// let repr_comp (a:Type) (wp:stexn_wp a) =
//   unit -> STATE (either a exn) (repr_wp a wp)

// assume val wp_monotonic_stexn (_:unit)
//   : Lemma 
//     (forall (a:Type) (wp:stexn_wp a).
//        (forall (p q:stexn_post a).
//           (forall (x:result a) (h:HS.mem). p x h ==> q x h) ==>
//           (forall (h:HS.mem). wp p h ==> wp q h)))

// let bind_repr (r:range)
//   (a:Type) (wp_f:stexn_wp a) (f:repr_comp a wp_f)
//   (b:Type) (wp_g:a -> stexn_wp b) (g:(x:a -> repr_comp b (wp_g x)))
//   : repr_comp b (stexn_bind r a b wp_f wp_g)
//   = wp_monotonic_stexn ();
//     fun _ ->
//     let r = f () in
//     match r with
//     | Inl x -> g x ()
//     | Inr e -> Inr e

// assume val wp_monotonic_st (_:unit)
//   : Lemma
//     (forall (a:Type) (wp:st_wp a).
//        (forall (p q:st_post a).
//           (forall (x:a) (h:HS.mem). p x h ==> q x h) ==>
//           (forall (h:HS.mem). wp p h ==> wp q h)))

// let lift_st_repr
//   (a:Type) (wp_f:st_wp a) (f:unit -> STATE a wp_f)
//   : repr_comp a (lift_st_stexn a wp_f)
//   = wp_monotonic_st ();
//     fun _ ->
//     let x = f () in
//     Inl x

// let raise_repr (a:Type) (e:exn) : repr_comp a (raise_wp a e)
//   = fun _ -> Inr e

// let trywith_repr (a:Type)
//   (wp_try:stexn_wp a) (f:repr_comp a wp_try)
//   (wp_with:exn -> stexn_wp a) (g:(e:exn -> repr_comp a (wp_with e)))
//   : repr_comp a (trywith_wp a wp_try wp_with)
//   = wp_monotonic_stexn ();
//     fun _ ->
//     let r = f () in
//     match r with
//     | Inl x -> Inl x
//     | Inr e -> g e ()
