module Steel.Effects2

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory
module Act = Steel.Actions

open Steel.Memory
open Steel.Semantics.Instantiate

module Ins = Steel.Semantics.Instantiate

let join_preserves_interp (hp:hprop) (m0:hmem hp) (m1:mem{disjoint m0 m1})
: Lemma
  (interp hp (join m0 m1))
  [SMTPat (interp hp (join m0 m1))]
= intro_emp m1;
  intro_star hp emp m0 m1;
  affine_star hp emp (join m0 m1)

let ens_depends_only_on (#a:Type) (pre:hprop) (post:a -> hprop)
  (q:(hmem pre -> x:a -> hmem (post x) -> prop))

= //can join any disjoint mem to the pre-mem and q is still valid
  (forall x (m_pre:hmem pre) m_post (m:mem{disjoint m_pre m}).
     q m_pre x m_post <==> q (join m_pre m) x m_post) /\  //at this point we need to know interp pre (join m_pre m) -- use join_preserves_interp for that

  //can join any disjoint mem to the post-mem and q is still valid
  (forall x m_pre (m_post:hmem (post x)) (m:mem{disjoint m_post m}).
     q m_pre x m_post <==> q m_pre x (join m_post m))

type pre_t = hprop u#1
type post_t (a:Type) = a -> hprop u#1
type req_t (pre:pre_t) = q:(hmem pre -> prop){  //inlining depends only on
  forall (m0:hmem pre) (m1:mem{disjoint m0 m1}). q m0 <==> q (join m0 m1)
}
type ens_t (pre:pre_t) (a:Type u#a) (post:post_t u#a a) : Type u#(max 2 a) =
  q:(hmem pre -> x:a -> hmem (post x) -> prop){
    ens_depends_only_on pre post q
  }

#push-options "--warn_error -271"
let interp_depends_only_on_post (#a:Type) (hp:a -> hprop)
: Lemma
  (forall (x:a).
     (forall (m0:hmem (hp x)) (m1:mem{disjoint m0 m1}). interp (hp x) m0 <==> interp (hp x) (join m0 m1)))
= let aux (x:a)
    : Lemma
      (forall (m0:hmem (hp x)) (m1:mem{disjoint m0 m1}). interp (hp x) m0 <==> interp (hp x) (join m0 m1))
      [SMTPat ()]
    = interp_depends_only_on (hp x) in
  ()
#pop-options

let req_to_act_req (#pre:pre_t) (req:req_t pre) : Sem.l_pre #state pre =
  interp_depends_only_on pre;
  fun m -> interp pre m /\ req m

let ens_to_act_ens (#pre:pre_t) (#a:Type) (#post:post_t a) (ens:ens_t pre a post)
: Sem.l_post #state #a pre post
= interp_depends_only_on pre;
  interp_depends_only_on_post post;
  fun m0 x m1 -> interp pre m0 /\ interp (post x) m1 /\ ens m0 x m1

type repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a pre post (req_to_act_req req) (ens_to_act_ens ens)

assume val sl_implies (p q:hprop u#1) : Type0

assume val sl_implies_interp (p q:hprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures forall (m:mem) (f:hprop). interp (p `star` f) m ==>  interp (q `star` f) m)

assume val sl_implies_interp_emp (p q:hprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures forall (m:mem). interp p m ==>  interp q m)

assume val sl_implies_preserves_frame (p q:hprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures
    forall (m1 m2:mem) (r:hprop).
      Sem.preserves_frame #state q r m1 m2 ==>
      Sem.preserves_frame #state p r m1 m2)

assume val sl_implies_preserves_frame_right (p q:hprop u#1)
: Lemma
  (requires p `sl_implies` q)
  (ensures
    forall (m1 m2:mem) (r:hprop).
      Sem.preserves_frame #state r p m1 m2 ==>
      Sem.preserves_frame #state r q m1 m2)


unfold
let return_req (p:hprop u#1) : req_t p = fun _ -> True

unfold
let return_ens (#a:Type) (x:a) (p:a -> hprop u#1) : ens_t (p x) a p = fun _ r _ -> r == x

(*
 * Return is parametric in post
 * We rarely (never?) use M.return, but we will use it to define a ret
 *   function in the effect, that will be used to get around the scoping issues
 *   (cf. return-scoping.txt)
 *)
let return (a:Type) (x:a) (p:a -> hprop)
: repr a (p x) p (return_req (p x)) (return_ens x p)
= fun _ -> x

unfold
let bind_req (#a:Type) (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (req_g:(x:a -> req_t (post_f x)))
: req_t pre_f
= fun m0 -> req_f m0 /\ (forall (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 ==> (req_g x) m1)

unfold
let bind_ens (#a:Type) (#b:Type)
  (#pre_f:pre_t) (#post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#post_g:post_t b) (ens_g:(x:a -> ens_t (post_f x) b post_g))
: ens_t pre_f b post_g
= fun m0 y m2 ->
  req_f m0 /\ (exists (x:a) (m1:hmem (post_f x)). ens_f m0 x m1 /\ (ens_g x) m1 y m2)

(*
 * This bind is a simple bind that enforces f post to be
 *   definitionally equal to g pre
 * This is just for effect definition
 * Later we define polymonadic binds that relax this and provide framing support
 *)
let bind (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (post_g:post_t b) (req_g:(x:a -> req_t (post_f x))) (ens_g:(x:a -> ens_t (post_f x) b (post_g)))
  (f:repr a pre_f post_f req_f ens_f) (g:(x:a -> repr b (post_f x) post_g (req_g x) (ens_g x)))
: repr b pre_f post_g (bind_req req_f ens_f req_g) (bind_ens req_f ens_f ens_g)
= fun _ ->
  let x = f () in
  (g x) ()


(*
 * TODO: don't use polymonadic binds for lift anymore
 *)


(*
 * f <: g
 *)
unfold
let subcomp_pre (#a:Type) (#pre_f:pre_t) (#post_f:post_t a)
  (req_f:req_t pre_f) (ens_f:ens_t pre_f a post_f)
  (#pre_g:pre_t) (#post_g:post_t a)
  (req_g:req_t pre_g) (ens_g:ens_t pre_g a post_g)
  (_:squash (pre_g `sl_implies` pre_f))
  (_:squash (forall (x:a). post_f x `sl_implies` post_g x))
: pure_pre
= (forall (m0:hmem pre_g). req_g m0 ==> req_f m0)



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

let frame_aux (#a:Type) (#pre:pre_t) (#post:post_t a)
  (f:repr a pre post) (frame:hprop)
: repr a (pre `star` frame) (fun x -> post x `star` frame)
= fun _ ->
  Sem.run #state #_ #_ #_ #_ #_ (Sem.Frame (Sem.Act f) frame (fun _ -> True))

let bind_steel_steel (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:post_t b)
  (frame_f:hprop) (frame_g:hprop)
  (_:squash (forall (x:a). (post_f x `star` frame_f) `sl_implies` (pre_g x `star` frame_g)))
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) post_g))
: repr b (pre_f `star` frame_f) (fun z -> post_g z `star` frame_g)
= fun _ ->
  let x = frame_aux f frame_f () in

  sl_implies_interp (post_f x `star` frame_f) (pre_g x `star` frame_g);
  sl_implies_preserves_frame (post_f x `star` frame_f) (pre_g x `star` frame_g);
  
  frame_aux (g x) frame_g ()

polymonadic_bind (Steel, Steel) |> SteelF = bind_steel_steel


let bind_steel_steelf (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:post_t b)
  (frame_f:hprop)
  (_:squash (forall x. (post_f x `star` frame_f) `sl_implies` pre_g x))
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) post_g))
: repr b (pre_f `star` frame_f) post_g
= fun _ ->
  let x = frame_aux f frame_f () in

  sl_implies_interp (post_f x `star` frame_f) (pre_g x);
  sl_implies_preserves_frame (post_f x `star` frame_f) (pre_g x);

  (g x) ()

polymonadic_bind (Steel, SteelF) |> SteelF = bind_steel_steelf


let bind_steelf_steel (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:post_t b)
  (frame_g:hprop)
  (_:squash (forall x. post_f x `sl_implies` (pre_g x `star` frame_g)))
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) post_g))
: repr b pre_f (fun z -> post_g z `star` frame_g)
= fun _ ->
  let x = f () in

  sl_implies_interp (post_f x) (pre_g x `star` frame_g);
  sl_implies_preserves_frame (post_f x) (pre_g x `star` frame_g);

  frame_aux (g x) frame_g ()

polymonadic_bind (SteelF, Steel) |> SteelF = bind_steelf_steel


let bind_steelf_steelf (a:Type) (b:Type)
  (pre_f:pre_t) (post_f:post_t a) (pre_g:a -> pre_t) (post_g:post_t b)
  (_:squash (forall x. post_f x `sl_implies` pre_g x))
  (f:repr a pre_f post_f) (g:(x:a -> repr b (pre_g x) post_g))
: repr b pre_f post_g
= fun _ ->
  let x = f () in

  sl_implies_interp (post_f x) (pre_g x);
  sl_implies_preserves_frame (post_f x) (pre_g x);

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

// let bind_pure_steel (a:Type) (b:Type)
//   (pre_f:pre_t) (post_f:post_t a) (wp:a -> pure_wp b)
//   (frame_f:hprop) (post_g:post_t b)
//   (_:squash (forall x. wp x (fun _ -> True)))
//   (f:repr a pre_f post_f) (g:(x:a -> unit -> PURE b (wp x)))
//   (_:squash (forall x. (post_f x `star` frame_f) `sl_implies` (post_g (g x ()))))
// : repr b (pre_f `star` frame_f) post_g
// = fun _ ->
//   let x = (frame_aux f frame_f) () in
//   let y = (g x) () in

//   sl_implies_interp (post_f x `star` frame_f) (post_g y);
//   sl_implies_preserves_frame_right (post_f x `star` frame_f) (post_g y);

//   y

// // TODO:
// // polymonadic_bind (Steel, PURE) |> SteelF = bind_pure_steel


// let bind_pure_steelf (a:Type) (b:Type)
//   (pre_f:pre_t) (post_f:post_t a) (wp:a -> pure_wp b)
//   (post_g:post_t b)
//   (_:squash (forall x. wp x (fun _ -> True)))
//   (f:repr a pre_f post_f) (g:(x:a -> unit -> PURE b (wp x)))
//   (_:squash (forall x. post_f x `sl_implies` (post_g (g x ()))))
// : repr b pre_f post_g
// = fun _ ->
//   let x = f () in
//   let y = (g x) () in

//   sl_implies_interp (post_f x) (post_g y);
//   sl_implies_preserves_frame_right (post_f x) (post_g y);
  
//   y

// // TODO:
// // polymonadic_bind (SteelF, PURE) |> SteelF = bind_pure_steelf
