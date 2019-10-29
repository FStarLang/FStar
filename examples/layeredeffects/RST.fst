module RST

open FStar.HyperStack.ST

module HS = FStar.HyperStack


assume type resource : Type0
assume val emp : resource


type repr (a:Type) (r_in:resource) (r_out:a -> resource) =
  unit -> STATE a (fun p h -> forall x h1. p x h1)


let return (a:Type) (x:a)
: repr a emp (fun _ -> emp)
= fun _ -> x

let bind (a:Type) (b:Type)
  (r_in_f:resource) (r_out_f:a -> resource) (r_out_g:b -> resource)
  (f:repr a r_in_f r_out_f) (g:(x:a -> repr b (r_out_f x) r_out_g))
: repr b r_in_f r_out_g
= fun _ ->
  let x = f () in
  (g x) ()

let subcomp (a:Type)
  (r_in:resource) (r_out:a -> resource)
  (f:repr a r_in r_out)
: (repr a r_in r_out)
= f

let if_then_else (a:Type)
  (r_in:resource) (r_out:a -> resource)
  (f:repr a r_in r_out) (g:repr a r_in r_out)
  (p:Type0)
: Type
= repr a r_in r_out


reifiable reflectable
layered_effect {
  RSTATE : a:Type -> resource -> (a -> resource) -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}


let lift_pure_rst (a:Type) (wp:pure_wp a) (r:resource) (f:unit -> PURE a wp)
: repr a r (fun _ -> r)
= admit (); fun _ -> f ()

sub_effect PURE ~> RSTATE = lift_pure_rst


assume val array : Type0
assume val array_resource (a:array) : resource

assume val alloc (_:unit) : RSTATE array emp array_resource

#set-options "--debug RST --debug_level Extreme --debug_level Rel --ugly"
let test ()
: RSTATE array emp array_resource
= let ptr = alloc () in
  ptr
