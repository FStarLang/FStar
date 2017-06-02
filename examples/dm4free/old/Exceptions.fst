module Exceptions

let ex_pre = Type0
let ex_post (a:Type) = option a -> Type0
let ex_wp (a:Type) = unit -> ex_post a -> Type0

unfold let ex_return_wp (a:Type) (x:a) (_:unit) (post:ex_post a) =
  post (Some x)

//working around #517 by adding an explicit 'val'
unfold val ex_bind_wp : r:range -> (a:Type) -> (b:Type) -> (f:ex_wp a) -> (g:(a -> Tot (ex_wp b))) -> Tot (ex_wp b)
let ex_bind_wp r a b wp1 wp2 =
  fun (_:unit) (p:ex_post b) ->
   wp1 () (fun aopt -> match aopt with
		    | None -> p None
		    | Some x -> wp2 x () p)
		
unfold let ex_ite_wp (a:Type) (wp:ex_wp a) (_:unit) (post:ex_post a) =
  wp () post

unfold let ex_if_then_else (a:Type) (p:Type) (wp_then:ex_wp a) (wp_else:ex_wp a) (_:unit) (post:ex_post a) =
   l_ITE p
       (wp_then () post)
       (wp_else () post)

unfold let ex_stronger (a:Type) (wp1:ex_wp a) (wp2:ex_wp a) =
        (forall (p:ex_post a). wp1 () p ==> wp2 () p)

unfold let ex_close_wp (a:Type) (b:Type) (wp:(b -> GTot (ex_wp a))) (_:unit) (p:ex_post a) = (forall (b:b). wp b () p)
unfold let ex_assert_p (a:Type) (q:Type) (wp:ex_wp a) (_:unit) (p:ex_post a) = (q /\ wp () p)
unfold let ex_assume_p (a:Type) (q:Type) (wp:ex_wp a) (_:unit) (p:ex_post a) = (q ==> wp () p)
unfold let ex_null_wp (a:Type) (_:unit) (p:ex_post a) = (forall (r:option a). p r)
unfold let ex_trivial (a:Type) (wp:ex_wp a) = wp () (fun r -> True)

//new
let ex_repr (a:Type) (wp:ex_wp a) =
    unit -> PURE (option a) (wp ())

unfold val ex_bind: (a:Type) -> (b:Type) -> (wp0:ex_wp a)
		 -> (f:ex_repr a wp0)
		 -> (wp1:(a -> Tot (ex_wp b)))
		 -> (g:(x:a -> Tot (ex_repr b (wp1 x))))
		 -> Tot (ex_repr b (ex_bind_wp range_0 a b wp0 wp1))
let ex_bind a b wp0 f wp1 g
  = fun _ -> admit(); match f () with
		   | None -> None
		   | Some x -> g x ()
let ex_return (a:Type) (x:a)
  : ex_repr a (ex_return_wp a x)
  = fun _ -> Some x


reifiable reflectable new_effect {
  EXN : result:Type -> wp:ex_wp result -> Effect
  with
    return_wp    = ex_return_wp
  ; bind_wp      = ex_bind_wp
  ; if_then_else = ex_if_then_else
  ; ite_wp       = ex_ite_wp
  ; stronger     = ex_stronger
  ; close_wp     = ex_close_wp
  ; assert_p     = ex_assert_p
  ; assume_p     = ex_assume_p
  ; null_wp      = ex_null_wp
  ; trivial      = ex_trivial
  ; repr         = ex_repr
  ; bind         = ex_bind
  ; return       = ex_return
  //defining it here fails because of some type inference issue, but see raise below
  (*; raise        = raise *)
}

unfold let lift_pure_ex (a:Type) (wp:pure_wp a) (_:unit) (p:ex_post a) = wp (fun a -> p (Some a))
sub_effect PURE ~> EXN = lift_pure_ex

effect Exn (a:Type) (pre:ex_pre) (post:ex_post a) =
       EXN a
         (fun (_:unit) (p:ex_post a) -> pre /\ (forall (r:option a). (pre /\ post r) ==> p r)) (* WP *)

effect Ex (a:Type) = //(pre:ex_pre) (post:ex_post a) ...adding this mistakenly causes a crash!
       EXN a (fun _ p -> forall x. p x)

val raise_ : a:Type -> Tot (ex_repr a (fun (_:unit) (p:ex_post a) -> p None))
let raise_ a (_:unit) = None

//You can also build a new action "on the fly" using reflect
reifiable let raise (a:Type) : Exn a True (fun r -> r==None)
  = EXN.reflect (raise_ a)

val div_intrinsic : i:nat -> j:int -> Exn int
  (requires True)
  (ensures (function None -> j=0 | Some z -> j<>0 /\ z = i / j))
let div_intrinsic i j =
  if j=0 then raise int
  else i / j

reifiable let div_extrinsic (i:nat) (j:int) : Ex int =
  if j=0 then raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) :
  Lemma (match reify (div_extrinsic i j) () with
         | None -> j = 0
	 | Some z -> j <> 0 /\ z = i / j) = ()

