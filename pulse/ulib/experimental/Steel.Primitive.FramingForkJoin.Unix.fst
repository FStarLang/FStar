module Steel.Primitive.FramingForkJoin.Unix

(* This module shows that it's possible to layer continuations on top
of SteelT to get a direct style (or Unix style) fork/join. Very much a
prototype for now. *)

open Steel.FramingEffect
open Steel.Memory
module L = Steel.SpinLock
open FStar.Ghost
open Steel.FramingReference
open Steel.SteelT.Basics
open Steel.Primitive.FramingForkJoin

module U = FStar.Universe


// (* Some helpers *)
assume val can_be_split_forall_frame (#a:Type) (p q:post_t a) (frame:slprop u#1) (x:a)
 : Lemma (requires can_be_split_forall p q)
         (ensures (frame `star` p x)  `equiv` (frame `star` q x))

assume
val change_slprop (p q : slprop)
              (_ : squash (p `sl_implies` q))
   : SteelT unit p (fun _ -> q)

let change_slprop_equiv (p q : slprop)
              (proof : squash (p `equiv` q))
   : SteelT unit p (fun _ -> q)
   = change_slprop p q (proof; equiv_sl_implies p q)

(* Continuations into unit, but parametrized by the final heap
 * proposition and with an implicit framing. I think ideally these would
 * also be parametric in the final type (instead of being hardcoded to
 * unit) but that means fork needs to be extended to be polymorphic in
 * at least one of the branches. *)
type steelK (t:Type u#aa) (pre : slprop u#1) (post:t->slprop u#1) =
  #frame:slprop -> #postf:slprop ->
  f:(x:t -> SteelT unit (frame `star` post x) (fun _ -> postf)) ->
  SteelT unit (frame `star` pre) (fun _ -> postf)

(* The classic continuation monad *)
let return a (x:a) (#[@@ framing_implicit] p: a -> slprop) : steelK a (p x) p =
  fun k -> k x

let bind (a:Type) (b:Type)
  (#[@@ framing_implicit] pre:pre_t) (#[@@ framing_implicit] post:post_t a)
  (#[@@ framing_implicit] pre':a -> pre_t) (#[@@ framing_implicit] post' : post_t b)
  (#[@@ framing_implicit] p:squash (can_be_split_forall post pre'))
  (f : steelK a pre post)
  (g : (x:a -> steelK b (pre' x) post'))
  : steelK b pre post'
  = fun #frame #postf (k:(x:b -> SteelT unit (frame `star` post' x) (fun _ -> postf))) ->
      f
      ((fun (x:a) -> change_slprop (frame `star` post x) (frame `star` pre' x)
                  (can_be_split_forall_frame post pre' frame x;
                  equiv_sl_implies (frame `star` post x) (frame `star` pre' x));
        g x k) <: (x:a -> SteelT unit (frame `star` post x) (fun _ -> postf)))

let subcomp (a:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:pre_t) (#[@@ framing_implicit] post_g:post_t a)
  (#[@@ framing_implicit] p1:squash (delay (can_be_split pre_g pre_f)))
  (#[@@ framing_implicit] p2:squash (annot_sub_post (can_be_split_forall post_f post_g)))
  (f:steelK a pre_f post_f)
: Tot (steelK a pre_g post_g)
= fun #frame #postf (k:(x:a -> SteelT unit (frame `star` post_g x) (fun _ -> postf))) ->
    change_slprop pre_g pre_f (); f
      ((fun x -> change_slprop (frame `star` post_f x) (frame `star` post_g x)
                            (can_be_split_forall_frame post_f post_g frame x;
                             equiv_sl_implies (frame `star` post_f x) (frame `star` post_g x));
              k x) <: (x:a -> SteelT unit (frame `star` post_f x) (fun _ -> postf)))

let if_then_else (a:Type u#aa)
                 (#[@@ framing_implicit] pre1:pre_t)
                 (#[@@ framing_implicit] post1:post_t a)
                 (f : steelK a pre1 post1)
                 (g : steelK a pre1 post1)
                 (p:Type0) : Type =
                 steelK a pre1 post1

total
reifiable
reflectable
layered_effect {
  SteelKF : a:Type -> pre:(slprop u#1) -> post:(a->slprop u#1) -> Effect
  with
  repr = steelK;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

new_effect SteelK = SteelKF

private
let rearrange3 (p q r:slprop) : Lemma
  (((p `star` q) `star` r) `equiv` (p `star` (r `star` q)))
  = assert   (((p `star` q) `star` r) `equiv` (p `star` (r `star` q))) by canon'()

let bind_steelk_steelk (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (#[@@ framing_implicit] frame_f:slprop) (#[@@ framing_implicit] frame_g:slprop)
  (#[@@ framing_implicit] p:squash (can_be_split_forall
    (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g)))
  (f:steelK a pre_f post_f)
  (g:(x:a -> steelK b (pre_g x) post_g))
: steelK b
    (pre_f `star` frame_f)
    (fun y -> post_g y `star` frame_g)
  = fun #frame (#post:slprop) (k:(y:b -> SteelT unit (frame `star` (post_g y `star` frame_g)) (fun _ -> post))) ->
    // Need SteelT unit (frame `star` (pre_f `star` frame_f)) (fun _ -> post)
    change_slprop_equiv (frame `star` (pre_f `star` frame_f)) ((frame `star` frame_f) `star` pre_f)  (rearrange3 frame frame_f pre_f;
        equiv_symmetric ((frame `star` frame_f) `star` pre_f) (frame `star` (pre_f `star` frame_f)) );
    f #(frame `star` frame_f) #post
      ((fun (x:a) ->
        // Need SteelT unit ((frame `star` frame_f) `star` post_f x) (fun _ -> post)
        change_slprop_equiv
          (frame `star` (post_f x `star` frame_f))
          (frame `star` (pre_g x `star` frame_g))
          (can_be_split_forall_frame (fun x -> post_f x `star` frame_f) (fun x -> pre_g x `star` frame_g) frame x);
        g x #(frame `star` frame_g) #post
          ((fun (y:b) -> k y)
            <: (y:b -> SteelT unit ((frame `star` frame_g) `star` post_g y) (fun _ -> post)))

        )

      <: (x:a -> SteelT unit ((frame `star` frame_f) `star` post_f x) (fun _ -> post)))


polymonadic_bind (SteelK, SteelK) |> SteelKF = bind_steelk_steelk

let bind_steelk_steelkf (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (#[@@ framing_implicit] frame_f:slprop)
  (#[@@ framing_implicit] p:squash (can_be_split_forall (fun x -> post_f x `star` frame_f) pre_g))
  (f:steelK a pre_f post_f)
  (g:(x:a -> steelK b (pre_g x) post_g))
: steelK b
    (pre_f `star` frame_f)
    post_g
  = fun #frame #post (k:(y:b -> SteelT unit (frame `star` post_g y) (fun _ -> post))) ->
    // Need SteelT unit (frame `star` (pre_f `star` frame_f)) (fun _ -> post)
    change_slprop_equiv (frame `star` (pre_f `star` frame_f)) ((frame `star` frame_f) `star` pre_f)  (rearrange3 frame frame_f pre_f;
        equiv_symmetric ((frame `star` frame_f) `star` pre_f) (frame `star` (pre_f `star` frame_f)) );
    f #(frame `star` frame_f) #post
      ((fun (x:a) ->
          change_slprop_equiv
            (frame `star` (post_f x `star` frame_f))
            (frame `star` pre_g x)
            (can_be_split_forall_frame (fun x -> post_f x `star` frame_f) pre_g frame x);

          g x #frame #post k
       )
       <: (x:a -> SteelT unit ((frame `star` frame_f) `star` post_f x) (fun _ -> post)))


polymonadic_bind (SteelK, SteelKF) |> SteelKF = bind_steelk_steelkf

let bind_steelkf_steelk (a:Type) (b:Type)
  (#[@@ framing_implicit] pre_f:pre_t) (#[@@ framing_implicit] post_f:post_t a)
  (#[@@ framing_implicit] pre_g:a -> pre_t) (#[@@ framing_implicit] post_g:post_t b)
  (#[@@ framing_implicit] frame_g:slprop)
  (#[@@ framing_implicit] p:squash (can_be_split_forall post_f (fun x -> pre_g x `star` frame_g)))
  (f:steelK a pre_f post_f)
  (g:(x:a -> steelK b (pre_g x) post_g))
: steelK b
    pre_f
    (fun y -> post_g y `star` frame_g)
  = fun #frame (#post:slprop) (k:(y:b -> SteelT unit (frame `star` (post_g y `star` frame_g)) (fun _ -> post))) ->
    // Need SteelT unit (frame `star` pre_f) (fun _ -> post)
    f #frame #post
      ((fun (x:a) ->
        // Need SteelT unit (frame `star` post_f x) (fun _ -> post)
        change_slprop_equiv
          (frame `star` post_f x)
          (frame `star` (pre_g x `star` frame_g))
          (can_be_split_forall_frame post_f (fun x -> pre_g x `star` frame_g) frame x);

        g x #(frame `star` frame_g) #post
          ((fun (y:b) ->
              k y
           ) <: (y:b -> SteelT unit ((frame `star` frame_g) `star` post_g y) (fun _ -> post)))
       ) <: (x:a -> SteelT unit (frame `star` post_f x) (fun _ -> post)))


polymonadic_bind (SteelKF, SteelK) |> SteelKF = bind_steelkf_steelk

//assume val ksorry : #a:Type -> #p:_ -> #q:_ -> unit -> SteelK a p q

let bind_tot_steelK_ (a:Type) (b:Type)
  (wp:pure_wp a)
  (#[@@ framing_implicit] pre:pre_t) (#[@@ framing_implicit] post:post_t b)
  (f:unit -> PURE a (fun _ -> True)) (g:(x:a -> steelK b pre post))
: steelK b
    pre
    post
  = fun #frame #postf (k:(x:b -> SteelT unit (frame `star` post x) (fun _ -> postf))) ->
      let x = f () in
      g k x

polymonadic_bind (PURE, SteelK) |> SteelK = bind_tot_steelK_

polymonadic_bind (PURE, SteelKF) |> SteelKF = bind_tot_steelK_


polymonadic_subcomp SteelKF <: SteelK = subcomp

(* Sanity check *)
let test_lift #p #q (f : unit -> SteelK unit p (fun _ -> q)) : SteelK unit p (fun _ -> q) =
  ();
  f ();
  ()

(* Identity cont with frame, to eliminate a SteelK *)
assume
val idk (#frame:slprop) (#a:Type) (x:a) : SteelT a frame (fun x -> frame)
//  Steel.SteelT.Basics.return x

assume
val kfork : #p:slprop -> #q:slprop -> (unit -> SteelK unit p (fun _ -> q)) -> SteelK (thread q) p (fun _ -> emp)

// let kfork (#p:slprop) (#q:slprop) (f : unit -> SteelK unit p (fun _ -> q))
// : SteelK (thread q) p (fun _ -> emp)
// =
//   SteelK?.reflect (
//   l_id ();
//   fun (#frame:slprop) (#postf:slprop)
//     (k : (x:(thread q) -> SteelT unit (frame `star` emp) (fun _ -> postf))) ->
//     let t1 () : SteelT unit p (fun _ -> q) =
//       let k : (unit -> SteelT unit q (fun _ -> q)) = fun () -> idk #q () in
//       let r : steelK _ _ _ = reify (f ()) in
//       reshuffle0 ();
//       r #emp #q (fun x -> reshuffle0 (); k x)
//     in
//     let t2 (t:thread q) () : SteelT unit frame (fun _ -> postf) = reshuffle0 (); k t in
//     let ff () : SteelT unit (p `star` frame) (fun _ -> postf)
//               = fork #p #q #frame #postf t1 t2
//     in
//     l_comm ();
//     let ff2 : unit -> SteelT unit (star frame p) (fun _ -> postf) = change_pre ff in
//     ff2 ())

(* just a flip of the usual frame *)
// assume val frame' : #a:_ -> #pre:_ -> #post:_ ->
//                     (f: unit -> SteelT a pre post) ->
//                     (frame : slprop) ->
//                     SteelT a (frame `star` pre) (fun x -> frame `star` (post x))

assume
val kjoin (#p:slprop) (t : thread p) : SteelK unit emp (fun _ -> p)
// SteelK?.reflect (fun #f k -> frame' (fun () -> join t) f; k ())

// assume
// val kframe : #a:Type -> #p:slprop -> #q:(a->slprop) ->
//              (f : slprop) ->
//              ($c : (unit -> SteelK a p q)) ->
//              SteelK a (f `star` p) (fun x -> f `star` q x)

// let kframe #a #p #q (f : slprop) ($c : (unit -> SteelK a p q))
//   : SteelK a (f `star` p) (fun x -> f `star` q x)
//   = SteelK?.reflect (fun #f0 #postf
//       (k : (x:a -> SteelT unit (f0 `star` (f `star` q x)) (fun _ -> postf))) ->
//       l_assoc ();
//       l_comm (); (* blasting with AC.. seems to work fine *)
//       let k' (x:a) : SteelT unit ((f0 `star` f) `star` q x) (fun _ -> postf) =
//           change_pre (fun () -> k x) ()
//       in
//       let cc0 () : SteelT unit ((f0 `star` f) `star` p) (fun _ -> postf) =
//         reify (c ()) #(f0 `star` f) #postf k'
//       in
//       let cc () : SteelT unit (f0 `star` (f `star` p)) (fun _ -> postf) =
//         change_pre cc0 ()
//       in
//       cc ())

// let cancel #p #q (c : steelK unit (p `star` emp) q) : steelK unit p q =
//   l_id ();
//   subcomp _ _ _ _ _ c

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
