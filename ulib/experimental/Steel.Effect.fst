(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.Effect

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.Memory

open Steel.Semantics.Instantiate
module Ins = Steel.Semantics.Instantiate

open Steel.Memory

let join_preserves_interp hp m0 m1
  = intro_emp m1;
    intro_star hp emp m0 m1;
    affine_star hp emp (join m0 m1)

#push-options "--query_stats"
let _test (pre:slprop) (h_pre:hmem pre) (h:mem{disjoint h_pre h}) =
  assert (interp pre (join h_pre h))
#pop-options

let respects_fp #fp p = 
  forall (m0:hmem fp) (m1:mem{disjoint m0 m1}). p m0 <==> p (join m0 m1)
let reveal_respects_fp p = ()

let respects_binary_fp #a #pre #post q
  = (forall x (h_pre:hmem pre) h_post (h:mem{disjoint h_pre h}).
      q h_pre x h_post <==> q (join h_pre h) x h_post) /\
    (forall x h_pre (h_post:hmem (post x)) (h:mem{disjoint h_post h}).
      q h_pre x h_post <==> q h_pre x (join h_post h))
let reveal_respects_binary_fp q = ()


#push-options "--warn_error -271"
let ens_depends_only_on (#a:Type) (pre:Mem.slprop) (post:a -> Mem.slprop)
  (q:(hmem pre -> x:a -> hmem (post x) -> prop))

= let join_preserves_interp (hp:slprop) (m0:hmem hp) (m1:mem{disjoint m0 m1})
    : Lemma (interp hp (join m0 m1))
      [SMTPat ()] = join_preserves_interp hp m0 m1 in
  (
  //can join any disjoint heap to the pre-heap and q is still valid
  (forall x (h_pre:hmem pre) h_post (h:mem{disjoint h_pre h}).
     q h_pre x h_post <==> q (join h_pre h) x h_post) /\  //at this point we need to know interp pre (join h_pre h) -- use join_preserves_interp for that

  //can join any disjoint heap to the post-heap and q is still valid
  (forall x h_pre (h_post:hmem (post x)) (h:mem{disjoint h_post h}).
     q h_pre x h_post <==> q h_pre x (join h_post h))

  )
#pop-options

type pre_t = slprop u#1
type post_t (a:Type) = a -> slprop u#1
type req_t (pre:pre_t) = q:(hmem pre -> prop){
  forall (m0:hmem pre) (m1:mem{disjoint m0 m1}). q m0 <==> q (join m0 m1)
}

type ens_t (pre:pre_t) (a:Type u#a) (post:post_t u#a a) : Type u#(max 2 a) =
  q:(hmem pre -> x:a -> hmem (post x) -> prop){
    ens_depends_only_on pre post q
  }



#push-options "--warn_error -271"
let interp_depends_only_on_post (#a:Type) (hp:a -> slprop)
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

let req_to_act_req (#pre:slprop) (req:fp_mprop pre) : Sem.l_pre #state pre =
  interp_depends_only_on pre;
  fun m -> interp pre m /\ req m

let ens_to_act_ens (#pre:slprop) (#a:Type) (#post:a -> slprop) (ens:fp_binary_mprop pre post)
: Sem.l_post #state #a pre post
= interp_depends_only_on pre;
  interp_depends_only_on_post post;
  fun m0 x m1 -> interp pre m0 /\ interp (post x) m1 /\ ens m0 x m1

let repr a pre post req ens =
  Sem.action_t #state #a pre post
    (req_to_act_req req)
    (ens_to_act_ens ens)

let returnc (a:Type u#a) (x:a) (p:a -> slprop) = fun _ -> x

let bind a b pre_f post_f req_f ens_f post_g req_g ens_g f g
  = fun m0 ->
      let x = f () in
      g x ()

let subcomp a pre post req_f ens_f req_g ens_g f = f

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let bind_pure_steel a b wp pre_g post_b req_g ens_g f g
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun m0 ->
      let x = f () in
      g x m0
#pop-options

let bind_steel_pure a b pre_f post_f req_f ens_f wp_g f g
  = 
    FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun _ ->
    let x = f () in
    g x ()


unfold
let bind_div_steel_req (#a:Type) (wp:pure_wp a)
  (#pre_g:pre_t) (req_g:a -> req_t pre_g)
: req_t pre_g
= FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun h -> wp (fun _ -> True) /\ (forall x. (req_g x) h)

unfold
let bind_div_steel_ens (#a:Type) (#b:Type)
  (wp:pure_wp a)
  (#pre_g:pre_t) (#post_g:post_t b) (ens_g:a -> ens_t pre_g b post_g)
: ens_t pre_g b post_g
= fun h0 r h1 -> wp (fun _ -> True) /\ (exists x. ens_g x h0 r h1)

(*
 * A polymonadic bind between DIV and NMSTATE
 *
 * This is ultimately used when defining par and frame
 * par and frame try to compose reified Steel with Steel, since Steel is non total, its reification
 *   incurs a Div effect, and so, we need a way to compose Div and Steel
 *
 * This polymonadic bind gives us bare minimum to realize that
 * It is quite imprecise, in that it doesn't say anything about the post of the Div computation
 * That's because, the as_ensures combinator is not encoded for Div effect in the SMT,
 *   the way it is done for PURE and GHOST
 *
 * However, since the reification usecase gives us Dv anyway, this is fine for now
 *)
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let bind_div_steel (a:Type) (b:Type)
  (wp:pure_wp a)
  (pre_g:pre_t) (post_g:post_t b) (req_g:a -> req_t pre_g) (ens_g:a -> ens_t pre_g b post_g)
  (f:eqtype_as_type unit -> DIV a wp) (g:(x:a -> repr b pre_g post_g (req_g x) (ens_g x)))
: repr b pre_g post_g
    (bind_div_steel_req wp req_g)
    (bind_div_steel_ens wp ens_g)
= FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun m0 ->
  let x = f () in
  g x m0
#pop-options

polymonadic_bind (DIV, Steel) |> Steel = bind_div_steel


(*
 * This proof relies on core_mem_interp lemma from Steel.Memory
 *)
let par0 (#aL:Type u#a) (#preL:slprop) (#postL:aL -> slprop) 
         (#lpreL:fp_mprop preL) (#lpostL:fp_binary_mprop preL postL)
         (f:repr aL preL postL lpreL lpostL)
         (#aR:Type u#a) (#preR:slprop) (#postR:aR -> slprop)
         (#lpreR:fp_mprop preR) (#lpostR:fp_binary_mprop preR postR)
         (g:repr aR preR postR lpreR lpostR)
  : Steel (aL & aR)
          (preL `Mem.star` preR)
          (fun (xL, xR) -> postL xL `Mem.star` postR xR)
          (fun h -> lpreL h /\ lpreR h)
          (fun h0 (xL, xR) h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 xL h1 /\ lpostR h0 xR h1)
  = Steel?.reflect (fun _ -> Sem.run #state #_ #_ #_ #_ #_ (Sem.Par (Sem.Act f) (Sem.Act g)))

let par f g = par0 (reify (f ())) (reify (g ()))

let ( || ) f g = par f g

let frame0 (#a:Type) (#pre:slprop) (#post:a -> slprop) (#req:fp_mprop pre) (#ens:fp_binary_mprop pre post)
           (f:repr a pre post req ens)
           (frame:Mem.slprop)
           (f_frame:mprop frame)
    : Steel a
      (pre `Mem.star` frame)
      (fun x -> post x `Mem.star` frame)
      (fun h -> req h /\ f_frame h)
      (fun h0 r h1 -> req h0 /\ ens h0 r h1 /\ f_frame h1)
    = Steel?.reflect (fun _ -> Sem.run #state #_ #_ #_ #_ #_ (Sem.Frame (Sem.Act f) frame f_frame))

let frame f frame f_frame = frame0 (reify (f ())) frame f_frame

(** Reflecting actions in to the Steel effect ***)
let action_as_repr (#a:Type) (#p:slprop) (#q:a -> slprop) (f:action_except a Set.empty p q)
  : repr a p q (fun _ -> True) (fun _ _ _ -> True)
  = Ins.state_correspondence Set.empty; f
let read r v0 = Steel?.reflect (action_as_repr (sel_action FStar.Set.empty r v0))
let write r v0 v1 = Steel?.reflect (action_as_repr (upd_action FStar.Set.empty r v0 v1))
let alloc x = Steel?.reflect (action_as_repr (alloc_action FStar.Set.empty x))
let free r x = Steel?.reflect (action_as_repr (free_action FStar.Set.empty r x))
let split r v0 v1 = Steel?.reflect (action_as_repr (split_action FStar.Set.empty r v0 v1))
let gather r v0 v1 = Steel?.reflect (action_as_repr (gather_action FStar.Set.empty r v0 v1))
let witness r fact v _ = Steel?.reflect (action_as_repr (Steel.Memory.witness FStar.Set.empty r fact v ()))
let recall r v = Steel?.reflect (action_as_repr (Steel.Memory.recall FStar.Set.empty r v))

let cond_aux (#a:Type) (b:bool) (p: bool -> slprop) (q: bool -> a -> slprop)
             (then_:unit -> Steel a (p b) (q b) (fun _ -> b==true) (fun _ _ _ -> True))
             (else_:unit -> Steel a (p b) (q b) (fun _ -> b==false) (fun _ _ _ -> True))
  : SteelT a (p b) (q b)
  = if b then then_ () else else_ ()

let aux1 (#a:Type) (b:bool{b == true}) (p: bool -> slprop) (q: bool -> a -> slprop)
         (then_: (unit -> SteelT a (p true) (q true)))
  : unit -> SteelT a (p b) (q b)
  = fun _ -> then_ ()

let aux2 (#a:Type) (b:bool) (p: bool -> slprop) (q: bool -> a -> slprop)
         (then_: (unit -> SteelT a (p true) (q true)))
  : unit -> Steel a (p b) (q b) (fun _ -> b == true) (fun _ _ _ -> True)
  = fun _ -> (aux1 b p q then_) ()

let aux3 (#a:Type) (b:bool{b == false}) (p: bool -> slprop) (q: bool -> a -> slprop)
         (else_: (unit -> SteelT a (p false) (q false)))
  : unit -> SteelT a (p b) (q b)
  = fun _ -> else_ ()

let aux4 (#a:Type) (b:bool) (p: bool -> slprop) (q: bool -> a -> slprop)
         (else_: (unit -> SteelT a (p false) (q false)))
  : unit -> Steel a (p b) (q b) (fun _ -> b == false) (fun _ _ _ -> True)
  = fun _ -> (aux3 b p q else_) ()

let cond (#a:Type) (b:bool) (p: bool -> slprop) (q: bool -> a -> slprop)
         (then_: (unit -> SteelT a (p true) (q true)))
         (else_: (unit -> SteelT a (p false) (q false)))
  : SteelT a (p b) (q b)
  = let a1 = aux2 b p q then_ in
    let a2 = aux4 b p q else_ in
    cond_aux b p q a1 a2

let add_action f = Steel?.reflect (action_as_repr f)


(***** Bind and Subcomp relation with Steel.Atomic *****)

friend Steel.Effect.Atomic
open Steel.Effect.Atomic

#push-options "--z3rlimit 40"
let bind_atomic_steel _ _ _ _ _ _ _ _ f g
= fun m0 ->
  assume (forall m0. inames_ok Set.empty m0);
  let x = f () in
  g x ()
#pop-options

let subcomp_atomic_steel _ _ _ _ f = fun m0 -> f m0
