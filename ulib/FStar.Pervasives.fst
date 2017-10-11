module FStar.Pervasives

(* This is a file from the core library, dependencies must be explicit *)
open Prims
include FStar.Pervasives.Native

new_effect DIV = PURE
sub_effect PURE ~> DIV  = purewp_id

effect Div (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
       DIV a (fun (p:pure_post a) -> pre /\ (forall a. post a ==> p a))

effect Dv (a:Type) =
     DIV a (fun (p:pure_post a) -> (forall (x:a). p x))

(* We use the EXT effect to underspecify external system calls
   as being impure but having no observable effect on the state *)
effect EXT (a:Type) = Dv a

let st_pre_h   (heap:Type) = heap -> GTot Type0
let st_post_h' (heap:Type) (a:Type) (pre:Type) = a -> (_:heap{pre}) -> GTot Type0
let st_post_h  (heap:Type) (a:Type) = st_post_h' heap a True
let st_wp_h    (heap:Type) (a:Type) = st_post_h heap a -> Tot (st_pre_h heap)

unfold let st_return        (heap:Type) (a:Type)
                            (x:a) (p:st_post_h heap a) =
     p x
unfold let st_bind_wp       (heap:Type)
			    (r1:range)
			    (a:Type) (b:Type)
                            (wp1:st_wp_h heap a)
                            (wp2:(a -> GTot (st_wp_h heap b)))
                            (p:st_post_h heap b) (h0:heap) =
  wp1 (fun a h1 -> wp2 a p h1) h0
unfold let st_if_then_else  (heap:Type) (a:Type) (p:Type)
                             (wp_then:st_wp_h heap a) (wp_else:st_wp_h heap a)
                             (post:st_post_h heap a) (h0:heap) =
     l_ITE p
        (wp_then post h0)
	(wp_else post h0)
unfold let st_ite_wp        (heap:Type) (a:Type)
                            (wp:st_wp_h heap a)
                            (post:st_post_h heap a) (h0:heap) =
     forall (k:st_post_h heap a).
	 (forall (x:a) (h:heap).{:pattern (guard_free (k x h))} k x h <==> post x h)
	 ==> wp k h0
unfold let st_stronger  (heap:Type) (a:Type) (wp1:st_wp_h heap a)
                        (wp2:st_wp_h heap a) =
     (forall (p:st_post_h heap a) (h:heap). wp1 p h ==> wp2 p h)

unfold let st_close_wp      (heap:Type) (a:Type) (b:Type)
                             (wp:(b -> GTot (st_wp_h heap a)))
                             (p:st_post_h heap a) (h:heap) =
     (forall (b:b). wp b p h)
unfold let st_assert_p      (heap:Type) (a:Type) (p:Type)
                             (wp:st_wp_h heap a)
                             (q:st_post_h heap a) (h:heap) =
     p /\ wp q h
unfold let st_assume_p      (heap:Type) (a:Type) (p:Type)
                             (wp:st_wp_h heap a)
                             (q:st_post_h heap a) (h:heap) =
     p ==> wp q h
unfold let st_null_wp       (heap:Type) (a:Type)
                             (p:st_post_h heap a) (h:heap) =
     (forall (x:a) (h:heap). p x h)
unfold let st_trivial       (heap:Type) (a:Type)
                             (wp:st_wp_h heap a) =
     (forall h0. wp (fun r h1 -> True) h0)

new_effect {
  STATE_h (heap:Type) : result:Type -> wp:st_wp_h heap result -> Effect
  with return_wp    = st_return heap
     ; bind_wp      = st_bind_wp heap
     ; if_then_else = st_if_then_else heap
     ; ite_wp       = st_ite_wp heap
     ; stronger     = st_stronger heap
     ; close_wp     = st_close_wp heap
     ; assert_p     = st_assert_p heap
     ; assume_p     = st_assume_p heap
     ; null_wp      = st_null_wp heap
     ; trivial      = st_trivial heap
}


noeq type result (a:Type) =
  | V   : v:a -> result a
  | E   : e:exn -> result a
  | Err : msg:string -> result a

(* Effect EXCEPTION *)
let ex_pre  = Type0
let ex_post' (a:Type) (pre:Type) = (_:result a{pre}) -> GTot Type0
let ex_post  (a:Type) = ex_post' a True
let ex_wp    (a:Type) = ex_post a -> GTot ex_pre
unfold let ex_return   (a:Type) (x:a) (p:ex_post a) : GTot Type0 = p (V x)
unfold let ex_bind_wp (r1:range) (a:Type) (b:Type)
		       (wp1:ex_wp a)
		       (wp2:(a -> GTot (ex_wp b))) (p:ex_post b)
         : GTot Type0 =
  forall (k:ex_post b).
     (forall (rb:result b).{:pattern (guard_free (k rb))} k rb <==> p rb)
     ==> (wp1 (fun ra1 -> (V? ra1 ==> wp2 (V?.v ra1) k)
			/\ (E? ra1 ==> k (E (E?.e ra1)))))

unfold let ex_ite_wp (a:Type) (wp:ex_wp a) (post:ex_post a) =
  forall (k:ex_post a).
     (forall (rb:result a).{:pattern (guard_free (k rb))} k rb <==> post rb)
     ==> wp k

unfold let ex_if_then_else (a:Type) (p:Type) (wp_then:ex_wp a) (wp_else:ex_wp a) (post:ex_post a) =
   l_ITE p
       (wp_then post)
       (wp_else post)
unfold let ex_stronger (a:Type) (wp1:ex_wp a) (wp2:ex_wp a) =
        (forall (p:ex_post a). wp1 p ==> wp2 p)

unfold let ex_close_wp (a:Type) (b:Type) (wp:(b -> GTot (ex_wp a))) (p:ex_post a) = (forall (b:b). wp b p)
unfold let ex_assert_p (a:Type) (q:Type) (wp:ex_wp a) (p:ex_post a) = (q /\ wp p)
unfold let ex_assume_p (a:Type) (q:Type) (wp:ex_wp a) (p:ex_post a) = (q ==> wp p)
unfold let ex_null_wp (a:Type) (p:ex_post a) = (forall (r:result a). p r)
unfold let ex_trivial (a:Type) (wp:ex_wp a) = wp (fun r -> True)

new_effect {
  EXN : result:Type -> wp:ex_wp result -> Effect
  with
    return_wp    = ex_return
  ; bind_wp      = ex_bind_wp
  ; if_then_else = ex_if_then_else
  ; ite_wp       = ex_ite_wp
  ; stronger     = ex_stronger
  ; close_wp     = ex_close_wp
  ; assert_p     = ex_assert_p
  ; assume_p     = ex_assume_p
  ; null_wp      = ex_null_wp
  ; trivial      = ex_trivial
}
effect Exn (a:Type) (pre:ex_pre) (post:ex_post' a pre) =
       EXN a (fun (p:ex_post a) -> pre /\ (forall (r:result a). post r ==> p r))

unfold let lift_div_exn (a:Type) (wp:pure_wp a) (p:ex_post a) = wp (fun a -> p (V a))
sub_effect DIV ~> EXN = lift_div_exn
effect Ex (a:Type) = Exn a True (fun v -> True)

let all_pre_h   (h:Type)           = h -> GTot Type0
let all_post_h' (h:Type) (a:Type) (pre:Type)  = result a -> (_:h{pre}) -> GTot Type0
let all_post_h  (h:Type) (a:Type)  = all_post_h' h a True
let all_wp_h    (h:Type) (a:Type)  = all_post_h h a -> Tot (all_pre_h h)

unfold let all_ite_wp (heap:Type) (a:Type)
                      (wp:all_wp_h heap a)
                      (post:all_post_h heap a) (h0:heap) =
    forall (k:all_post_h heap a).
       (forall (x:result a) (h:heap).{:pattern (guard_free (k x h))} k x h <==> post x h)
       ==> wp k h0
unfold let all_return  (heap:Type) (a:Type) (x:a) (p:all_post_h heap a) = p (V x)
unfold let all_bind_wp (heap:Type) (r1:range) (a:Type) (b:Type)
                       (wp1:all_wp_h heap a)
                       (wp2:(a -> GTot (all_wp_h heap b)))
                       (p:all_post_h heap b) (h0:heap) : GTot Type0 =
  wp1 (fun ra h1 -> (match ra with
                  | V v     -> wp2 v p h1
		  | E e     -> p (E e) h1
		  | Err msg -> p (Err msg) h1)) h0

unfold let all_if_then_else (heap:Type) (a:Type) (p:Type)
                             (wp_then:all_wp_h heap a) (wp_else:all_wp_h heap a)
                             (post:all_post_h heap a) (h0:heap) =
   l_ITE p
       (wp_then post h0)
       (wp_else post h0)
unfold let all_stronger (heap:Type) (a:Type) (wp1:all_wp_h heap a)
                        (wp2:all_wp_h heap a) =
    (forall (p:all_post_h heap a) (h:heap). wp1 p h ==> wp2 p h)

unfold let all_close_wp (heap:Type) (a:Type) (b:Type)
                         (wp:(b -> GTot (all_wp_h heap a)))
                         (p:all_post_h heap a) (h:heap) =
    (forall (b:b). wp b p h)
unfold let all_assert_p (heap:Type) (a:Type) (p:Type)
                         (wp:all_wp_h heap a) (q:all_post_h heap a) (h:heap) =
    p /\ wp q h
unfold let all_assume_p (heap:Type) (a:Type) (p:Type)
                         (wp:all_wp_h heap a) (q:all_post_h heap a) (h:heap) =
    p ==> wp q h
unfold let all_null_wp (heap:Type) (a:Type)
                        (p:all_post_h heap a) (h0:heap) =
    (forall (a:result a) (h:heap). p a h)
unfold let all_trivial (heap:Type) (a:Type) (wp:all_wp_h heap a) =
    (forall (h0:heap). wp (fun r h1 -> True) h0)

new_effect {
  ALL_h (heap:Type) : a:Type -> wp:all_wp_h heap a -> Effect
  with
    return_wp    = all_return       heap
  ; bind_wp      = all_bind_wp      heap
  ; if_then_else = all_if_then_else heap
  ; ite_wp       = all_ite_wp       heap
  ; stronger     = all_stronger     heap
  ; close_wp     = all_close_wp     heap
  ; assert_p     = all_assert_p     heap
  ; assume_p     = all_assume_p     heap
  ; null_wp      = all_null_wp      heap
  ; trivial      = all_trivial      heap
}

(* An SMT-pattern to control unfolding inductives;
   In a proof, you can say `allow_inversion (option a)`
   to allow the SMT solver. cf. allow_inversion below
 *)
let inversion (a:Type) = True

let allow_inversion (a:Type)
  : Pure unit (requires True) (ensures (fun x -> inversion a))
  = ()

//allowing inverting option without having to globally increase the fuel just for this
val invertOption : a:Type -> Lemma
  (requires True)
  (ensures (forall (x:option a). None? x \/ Some? x))
  [SMTPat (option a)]
let invertOption a = allow_inversion (option a)

type either 'a 'b =
  | Inl : v:'a -> either 'a 'b
  | Inr : v:'b -> either 'a 'b



val dfst : #a:Type -> #b:(a -> GTot Type) -> dtuple2 a b -> Tot a
let dfst #a #b t = Mkdtuple2?._1 t

val dsnd : #a:Type -> #b:(a -> GTot Type) -> t:dtuple2 a b -> Tot (b (Mkdtuple2?._1 t))
let dsnd #a #b t = Mkdtuple2?._2 t

(* Concrete syntax (x:a & y:b x & c x y) *)
unopteq type dtuple3 (a:Type)
             (b:(a -> GTot Type))
             (c:(x:a -> b x -> GTot Type)) =
  | Mkdtuple3:_1:a
             -> _2:b _1
             -> _3:c _1 _2
             -> dtuple3 a b c

(* Concrete syntax (x:a & y:b x & z:c x y & d x y z) *)
unopteq type dtuple4 (a:Type)
             (b:(x:a -> GTot Type))
             (c:(x:a -> b x -> GTot Type))
             (d:(x:a -> y:b x -> z:c x y -> GTot Type)) =
 | Mkdtuple4:_1:a
           -> _2:b _1
           -> _3:c _1 _2
           -> _4:d _1 _2 _3
           -> dtuple4 a b c d

val ignore: #a:Type -> a -> Tot unit
let ignore #a x = ()
irreducible
let rec false_elim (#a:Type) (u:unit{false}) : Tot a = false_elim ()

(* For the compiler. Use as follows:
 *
 * [@ PpxDerivingShow ]
 * type t = A | B
 *
 * The resulting OCaml extracted type definition will have [@@ ppx_deriving show] attached to it. *)
type __internal_ocaml_attributes =
  | PpxDerivingShow
  | PpxDerivingShowConstant of string
  | CInline
  | Substitute
  | Gc
  | Comment of string
