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

module Steel.PCM.Effect

module Sem = Steel.Semantics.Hoare.MST
module Mem = Steel.PCM.Memory

open Steel.PCM.Semantics.Instantiate
module Ins = Steel.PCM.Semantics.Instantiate

open Steel.PCM.Memory

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

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let bind_steel_pure a b pre_f post_f req_f ens_f wp_g f g
  = admit(); //We don't really need this direction anymore and it takes ages to prove (not sure why)
    FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun _ ->
    let x = f () in
    g x ()
#pop-options

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


