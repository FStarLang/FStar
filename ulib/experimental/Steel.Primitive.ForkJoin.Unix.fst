module Steel.Primitive.ForkJoin.Unix

(* This module shows that it's possible to layer continuations on top
of SteelT to get a direct style (or Unix style) fork/join. Very much a
prototype for now. *)

open FStar.Ghost
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.Primitive.ForkJoin

module U = FStar.Universe

#set-options "--warn_error -330"  //turn off the experimental feature warning

// (* Some helpers *)
let change_slprop_equiv (p q : slprop)
              (proof : squash (p `equiv` q))
   : SteelT unit p (fun _ -> q)
   = change_slprop p q (fun _ -> proof; equiv_sl_implies p q)

(* Continuations into unit, but parametrized by the final heap
 * proposition and with an implicit framing. I think ideally these would
 * also be parametric in the final type (instead of being hardcoded to
 * unit) but that means fork needs to be extended to be polymorphic in
 * at least one of the branches. *)
type steelK (t:Type u#aa) (framed:bool) (pre : slprop u#1) (post:t->slprop u#1) =
  #frame:slprop -> #postf:slprop ->
  f:(x:t -> SteelT unit (frame `star` post x) (fun _ -> postf)) ->
  SteelT unit (frame `star` pre) (fun _ -> postf)

(* The classic continuation monad *)
let return_ a (x:a) (#[@@@ framing_implicit] p: a -> slprop) : steelK a true (return_pre (p x)) p =
  fun k -> k x

private
let rearrange3 (p q r:slprop) : Lemma
  (((p `star` q) `star` r) `equiv` (p `star` (r `star` q)))
  = assert   (((p `star` q) `star` r) `equiv` (p `star` (r `star` q))) by canon' false (`true_p) (`true_p)

let bind (a:Type) (b:Type)
  (#framed_f:eqtype_as_type bool) (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] pre_g:a -> pre_t) (#[@@@ framing_implicit] post_g:post_t b)
  (#[@@@ framing_implicit] frame_f:slprop) (#[@@@ framing_implicit] frame_g:slprop)
  (#[@@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g)))
  (#[@@@ framing_implicit] m1 : squash (maybe_emp framed_f frame_f))
  (#[@@@ framing_implicit] m2:squash (maybe_emp framed_g frame_g))
  (f:steelK a framed_f pre_f post_f)
  (g:(x:a -> steelK b framed_g (pre_g x) post_g))
: steelK b
    true
    (pre_f `star` frame_f)
    (fun y -> post_g y `star` frame_g)
  = fun #frame (#post:slprop) (k:(y:b -> SteelT unit (frame `star` (post_g y `star` frame_g)) (fun _ -> post))) ->
    // Need SteelT unit (frame `star` (pre_f `star` frame_f)) (fun _ -> post)
    change_slprop_equiv (frame `star` (pre_f `star` frame_f)) ((frame `star` frame_f) `star` pre_f)  (rearrange3 frame frame_f pre_f;
        equiv_symmetric ((frame `star` frame_f) `star` pre_f) (frame `star` (pre_f `star` frame_f)) );
    f #(frame `star` frame_f) #post
      ((fun (x:a) ->
        // Need SteelT unit ((frame `star` frame_f) `star` post_f x) (fun _ -> post)
        change_slprop
          (frame `star` (post_f x `star` frame_f))
          (frame `star` (pre_g x `star` frame_g))
          (fun _ -> can_be_split_forall_frame (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g) frame x);
        g x #(frame `star` frame_g) #post
          ((fun (y:b) -> k y)
            <: (y:b -> SteelT unit ((frame `star` frame_g) `star` post_g y) (fun _ -> post)))

        )

      <: (x:a -> SteelT unit ((frame `star` frame_f) `star` post_f x) (fun _ -> post)))

let subcomp (a:Type)
  (#framed_f:eqtype_as_type bool) (#framed_g:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre_f:pre_t) (#[@@@ framing_implicit] post_f:post_t a)
  (#[@@@ framing_implicit] pre_g:pre_t) (#[@@@ framing_implicit] post_g:post_t a)
  (#[@@@ framing_implicit] p1:squash (can_be_split pre_g pre_f))
  (#[@@@ framing_implicit] p2:squash (can_be_split_forall post_f post_g))
  (f:steelK a framed_f pre_f post_f)
: Tot (steelK a framed_g pre_g post_g)
= fun #frame #postf (k:(x:a -> SteelT unit (frame `star` post_g x) (fun _ -> postf))) ->
    change_slprop pre_g pre_f (fun _ -> ()); f
      ((fun x -> change_slprop (frame `star` post_f x) (frame `star` post_g x)
                            (fun _ -> can_be_split_forall_frame post_f post_g frame x);
               k x) <: (x:a -> SteelT unit (frame `star` post_f x) (fun _ -> postf)))

// let if_then_else (a:Type u#aa)
//                  (#[@@@ framing_implicit] pre1:pre_t)
//                  (#[@@@ framing_implicit] post1:post_t a)
//                  (f : steelK a pre1 post1)
//                  (g : steelK a pre1 post1)
//                  (p:Type0) : Type =
//                  steelK a pre1 post1

// We did not define a bind between Div and Steel, so we indicate
// SteelKF as total to be able to reify and compose it when implementing fork
// This module is intended as proof of concept
[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  SteelKBase : a:Type -> framed:bool -> pre:(slprop u#1) -> post:(a->slprop u#1) -> Effect
  with
  repr = steelK;
  return = return_;
  bind = bind;
  subcomp = subcomp
  // if_then_else = if_then_else
}

effect SteelK (a:Type) (pre:pre_t) (post:post_t a) =
  SteelKBase a false pre post
effect SteelKF (a:Type) (pre:pre_t) (post:post_t a) =
  SteelKBase a true pre post

// We would need requires/ensures in SteelK to have a binding with Pure.
// But for our example, Tot is here sufficient
let bind_tot_steelK_ (a:Type) (b:Type)
  (#framed:eqtype_as_type bool)
  (#[@@@ framing_implicit] pre:pre_t) (#[@@@ framing_implicit] post:post_t b)
  (f:eqtype_as_type unit -> PURE a (fun _ -> True)) (g:(x:a -> steelK b framed pre post))
: steelK b
    framed
    pre
    post
  = fun #frame #postf (k:(x:b -> SteelT unit (frame `star` post x) (fun _ -> postf))) ->
      let x = f () in
      g x k

polymonadic_bind (PURE, SteelKBase) |> SteelKBase = bind_tot_steelK_

// (* Sanity check *)
let test_lift #p #q (f : unit -> SteelK unit p (fun _ -> q)) : SteelK unit p (fun _ -> q) =
  ();
  f ();
  ()

(* Identity cont with frame, to eliminate a SteelK *)

let idk (#frame:slprop) (#a:Type) (x:a) : SteelT a frame (fun x -> frame)
  = noop(); return x

let kfork (#p:slprop) (#q:slprop) (f : unit -> SteelK unit p (fun _ -> q))
: SteelK (thread q) p (fun _ -> emp)
=
  SteelK?.reflect (
  fun (#frame:slprop) (#postf:slprop)
    (k : (x:(thread q) -> SteelT unit (frame `star` emp) (fun _ -> postf))) ->
      noop ();
      let t1 () : SteelT unit (emp `star` p) (fun _ -> q) =
        let r : steelK unit false p (fun _ -> q) = reify (f ()) in
        r #emp #q (fun _ -> idk())
      in
      let t2 (t:thread q) () : SteelT unit frame (fun _ -> postf) = k t in
      let ff () : SteelT unit (p `star` frame) (fun _ -> postf) =
        fork #p #q #frame #postf t1 t2
      in
      ff())

let kjoin (#p:slprop) (t : thread p) : SteelK unit emp (fun _ -> p)
 = SteelK?.reflect (fun #f k -> join t; k ())

(* Example *)

assume val q : int -> slprop
assume val f : unit -> SteelK unit emp (fun _ -> emp)
assume val g : i:int -> SteelK unit emp (fun _ -> q i)
assume val h : unit -> SteelK unit emp (fun _ -> emp)

let example () : SteelK unit emp (fun _ -> q 1 `star` q 2) =
  let p1:thread (q 1) = kfork (fun () -> g 1) in
  let p2:thread (q 2) = kfork (fun () -> g 2) in
  kjoin p1;
  h();
  kjoin p2

let as_steelk_repr' (a:Type) (pre:slprop) (post:post_t a) (f:unit -> SteelT a pre post)
  : steelK a false pre post
  = fun #frame #postf (k:(x:a -> SteelT unit (frame `star` post x) (fun _ -> postf))) ->
      let x = f () in
      k x


let triv_pre (req:slprop) : req_t req = fun _ -> True
let triv_post (#a:Type) (req:slprop) (ens:post_t a) : ens_t req a ens = fun _ _ _ -> True

let as_steelk_repr (a:Type) (pre:slprop) (post:post_t a)
  (f:repr a false pre post (triv_pre pre) (triv_post pre post))// unit -> SteelT a pre post)
  : steelK a false pre post
  = as_steelk_repr' a pre post (fun _ -> SteelBase?.reflect f)

// let as_steelk_repr' (a:Type) (pre:slprop) (post:post_t a) (f:unit -> SteelT a pre post)
//   : steelK a pre post
//   = fun #frame #postf (k:(x:a -> SteelT unit (frame `star` post x) (fun _ -> postf))) ->
//       let x = f () in
//       k x

// let as_steelk (#a:Type) (#pre:slprop) (#post:post_t a) ($f:unit -> SteelT a pre post)
//   : SteelK a pre post
//   = SteelK?.reflect (as_steelk_repr a pre post f)

open Steel.FractionalPermission

sub_effect SteelBase ~> SteelKBase = as_steelk_repr

let example2 (r:ref int) : SteelK (thread (pts_to r full_perm 1)) (pts_to r full_perm 0) (fun _ -> emp) =
  let p1 = kfork (fun _ -> write #_ #0 r 1) in
  p1

let example3 (r:ref int) : SteelK (ref int) (pts_to r full_perm 0) (fun x -> pts_to r full_perm 1 `star` pts_to x full_perm 2) =
  let p1 = kfork (fun _ -> write #_ #0 r 1) in
  let x = alloc 2 in
  kjoin p1;
  x

let example4 () : SteelK (ref int) emp (fun r -> pts_to r full_perm 2) =
  let x = alloc 0 in
  let y = alloc 1 in
  let p1:thread (pts_to x full_perm 1) = kfork (fun _ -> write #_ #0 x 1) in
  let p2:thread emp = kfork (fun _ -> free #_ #1 y) in
  kjoin p1;
  write #_ #1 x 2;
  kjoin p2;
  x
