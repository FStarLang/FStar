module Bug2066

type unit : Type = unit

type pre_t = Type0

type post_t (a:Type) = a -> Type0

type repr (a:Type) (pre:pre_t) (post:post_t a) =
  unit -> Pure a pre post

unfold
let return_pre : pre_t = True

unfold
let return_post (#a:Type) (x:a) : post_t a = fun r -> r == x

let return (a:Type) (x:a) : repr a return_pre (return_post x)
  = fun _ -> x

unfold
let bind_pre (#a:Type)
  (pre_f:pre_t) (post_f:post_t a)
  (pre_g:a -> pre_t)
  : pre_t
  = pre_f /\ (forall (x:a). post_f x ==> pre_g x)

unfold
let bind_post (#a #b:Type)
  (post_f:post_t a)
  (pre_g:a -> pre_t) (post_g:a -> post_t b)
  : post_t b 
  = fun y -> exists (x:a). post_f x /\ post_g x y

let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a)
  (pre_g:a -> pre_t) (post_g:a -> post_t b)
  (f:repr a pre_f post_f)
  (g:(x:a -> repr b (pre_g x) (post_g x)))
  : repr b
      (bind_pre pre_f post_f pre_g)
      (bind_post post_f pre_g post_g)
  = fun _ ->
    let x = f () in
    (g x) ()

layered_effect {
  M : a:Type -> pre_t -> post_t a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind
}

unfold
let lift_Tot_M_pre : pre_t = True

unfold
let lift_Tot_M_post (#a:Type) (f:unit -> Tot a)
  : post_t a
  = fun x -> x == f ()

let lift_Tot_M (a:Type) (f:unit -> Tot a)
  : repr a lift_Tot_M_pre (lift_Tot_M_post f)
  = fun _ -> f ()

[@@expect_failure]
sub_effect PURE ~> M = lift_Tot_M
