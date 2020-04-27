module Steel.Effects2

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
module Act = Steel.Actions

open Steel.Memory
open Steel.Semantics.Instantiate

module Ins = Steel.Semantics.Instantiate

type pre_t = hprop u#1
type post_t (a:Type) = a -> hprop u#1

type repr (a:Type) (pre:pre_t) (post:post_t a) =
  Sem.action_t #state #a pre post (fun _ -> True) (fun _ _ _ -> True)

let return (a:Type) (x:a) (p:a -> hprop) : repr a (p x) p =
  fun _ -> x

let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (post_g:post_t b)
  (f:repr a pre_f post_f) (g:(x:a -> repr b (post_f x) post_g))
: repr b pre_f post_g
= fun _ ->
  let x = f () in
  (g x) ()

let subcomp (a:Type)
  (pre_f:pre_t) (post_f:post_t a) (f:repr a pre_f post_f)
: repr a pre_f post_f
= f
  
let if_then_else (a:Type)
  (pre:pre_t) (post:post_t a)
  (f:repr a pre post) (g:repr a pre post)
  (p:Type0)
: Type
= repr a pre post

reifiable reflectable
layered_effect {
  SteelF: a:Type -> pre_t -> post_t a -> Effect
  with repr = repr;
       return = return;
       bind = bind;
       subcomp = subcomp;
       if_then_else = if_then_else
}

new_effect Steel = SteelF

assume val implies (p q:hprop u#1) : Type0

assume val implies_interp (p q:hprop u#1)
: Lemma
  (requires p `implies` q)
  (ensures forall (m:mem) (f:hprop). interp (p `star` f) m ==>  interp (q `star` f) m)

assume val implies_preserves_frame (p q:hprop u#1)
: Lemma
  (requires p `implies` q)
  (ensures
    forall (m1 m2:mem) (r:hprop).
      Sem.preserves_frame #state q r m1 m2 ==>
      Sem.preserves_frame #state p r m1 m2)

assume val implies_preserves_frame_right (p q:hprop u#1)
: Lemma
  (requires p `implies` q)
  (ensures
    forall (m1 m2:mem) (r:hprop).
      Sem.preserves_frame #state r p m1 m2 ==>
      Sem.preserves_frame #state r q m1 m2)

let frame_aux (#a:Type) (#pre:pre_t) (#post:post_t a)
  (f:repr a pre post) (frame:hprop)
: repr a (pre `star` frame) (fun x -> post x `star` frame)
= fun _ ->
  Sem.run #state #_ #_ #_ #_ #_ (Sem.Frame (Sem.Act f) frame (fun _ -> True))

let bind_steel_steel (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:post_t b)
  (frame_f:hprop) (frame_g:hprop)
  (_:squash (forall (x:a). (post_f x `star` frame_f) `implies` (pre_g x `star` frame_g)))
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) post_g))
: repr b (pre_f `star` frame_f) (fun z -> post_g z `star` frame_g)
= fun _ ->
  let x = frame_aux f frame_f () in

  implies_interp (post_f x `star` frame_f) (pre_g x `star` frame_g);
  implies_preserves_frame (post_f x `star` frame_f) (pre_g x `star` frame_g);
  
  frame_aux (g x) frame_g ()

polymonadic_bind (Steel, Steel) |> SteelF = bind_steel_steel


let bind_steel_steelf (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:post_t b)
  (frame_f:hprop)
  (_:squash (forall x. (post_f x `star` frame_f) `implies` pre_g x))
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) post_g))
: repr b (pre_f `star` frame_f) post_g
= fun _ ->
  let x = frame_aux f frame_f () in

  implies_interp (post_f x `star` frame_f) (pre_g x);
  implies_preserves_frame (post_f x `star` frame_f) (pre_g x);

  (g x) ()

polymonadic_bind (Steel, SteelF) |> SteelF = bind_steel_steelf


let bind_steelf_steel (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:post_t b)
  (frame_g:hprop)
  (_:squash (forall x. post_f x `implies` (pre_g x `star` frame_g)))
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) post_g))
: repr b pre_f (fun z -> post_g z `star` frame_g)
= fun _ ->
  let x = f () in

  implies_interp (post_f x) (pre_g x `star` frame_g);
  implies_preserves_frame (post_f x) (pre_g x `star` frame_g);

  frame_aux (g x) frame_g ()

polymonadic_bind (SteelF, Steel) |> SteelF = bind_steelf_steel


let bind_steelf_steelf (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:post_t b)
  (_:squash (forall x. post_f x `implies` pre_g x))
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) post_g))
: repr b pre_f post_g
= fun _ ->
  let x = f () in

  implies_interp (post_f x) (pre_g x);
  implies_preserves_frame (post_f x) (pre_g x);

  (g x) ()

polymonadic_bind (SteelF, SteelF) |> SteelF = bind_steelf_steelf

assume WP_monotonic :
  forall (a:Type) (wp:pure_wp a).
    (forall p q. (forall x. p x ==>  q x) ==>  (wp p ==>  wp q))


(*
 * TODO: implementation of this combinator requires substitution of f and g
 *       in the comp type
 *)
let bind_pure_steel_ (a:Type) (b:Type)
  (wp:pure_wp a) (pre_g:a -> pre_t) (post_g:a -> post_t b)
  (_:squash (wp (fun _ -> True)))
  (f:unit -> PURE a wp) (g:(x:a -> repr b (pre_g x) (post_g x)))
: repr b (pre_g (f ())) (post_g (f ()))
= fun _ ->
  let x = f () in
  (g x) ()

polymonadic_bind (PURE, SteelF) |> SteelF = bind_pure_steel_

polymonadic_bind (PURE, Steel) |> Steel = bind_pure_steel_

let bind_pure_steel (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (wp:a -> pure_wp b)
  (frame_f:hprop) (post_g:post_t b)
  (_:squash (forall x. wp x (fun _ -> True)))
  (f:repr a pre_f post_f) (g:(x:a -> unit -> PURE b (wp x)))
  (_:squash (forall x. (post_f x `star` frame_f) `implies` (post_g (g x ()))))
: repr b (pre_f `star` frame_f) post_g
= fun _ ->
  let m0 = NMST.get () in

  let x = f () in

  let m1 = NMST.get () in

  let y = (g x) () in

  let m2 = NMST.get () in

  implies_interp (post_f x `star` frame_f) (post_g y);

  //from executing f
  assert (Sem.preserves_frame pre_f (post_f x) m0 m1);

  //add frame_f
  Sem.preserves_frame_star #state pre_f (post_f x) m0 m1 frame_f;
  assert (Sem.preserves_frame (pre_f `star` frame_f) (post_f x `star` frame_f) m0 m1);

  //g is pure, extends preserves_frame to m2
  assert (m1 == m2);  
  assert (Sem.preserves_frame (pre_f `star` frame_f) (post_f x `star` frame_f) m0 m2);

  //from last hypothesis in the signature
  assert (post_f x `star` frame_f `implies` post_g y);
  
  implies_preserves_frame_right (post_f x `star` frame_f) (post_g y);
  assert (Sem.preserves_frame (pre_f `star` frame_f) (post_g y) m0 m2);

  y

// TODO:
// polymonadic_bind (Steel, PURE) |> SteelF = bind_pure_steel


let bind_pure_steelf (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (wp:a -> pure_wp b)
  (post_g:post_t b)
  (_:squash (forall x. wp x (fun _ -> True)))
  (f:repr a pre_f post_f) (g:(x:a -> unit -> PURE b (wp x)))
  (_:squash (forall x. post_f x `implies` (post_g (g x ()))))
: repr b pre_f post_g
= fun _ ->
  let x = f () in
  let y = (g x) () in

  implies_interp (post_f x) (post_g y);
  implies_preserves_frame_right (post_f x) (post_g y);
  
  y

// TODO:
// polymonadic_bind (SteelF, PURE) |> SteelF = bind_pure_steelf


