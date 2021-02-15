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

#set-options "--warn_error -330"  //turn off the experimental feature warning

#push-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let repr (a:Type) (pre:pre_t) (post:post_t a) (req:req_t pre) (ens:ens_t pre a post) =
  Sem.action_t #state #a pre post (req_to_act_req req) (ens_to_act_ens ens)

let return (a:Type) (x:a) (#[@@@ framing_implicit] p:a -> slprop)
: repr a (p x) p (return_req (p x)) (return_ens a x p)
  = fun _ -> x

let bind a b f g = fun frame ->
  let x = f frame in
  (g x) frame

let subcomp a f = f

(*
 * Keeping f_frame aside for now
 *)
let frame_aux (#a:Type)
  (#pre:pre_t) (#post:post_t a) (#req:req_t pre) (#ens:ens_t pre a post)
  ($f:repr a pre post req ens) (frame:slprop)
: repr a (pre `star` frame) (fun x -> post x `star` frame) req ens
= fun frame' ->
  Sem.run #state #_ #_ #_ #_ #_ frame' (Sem.Frame (Sem.Act f) frame (fun _ -> True))

let nmst_get (#st:Sem.st) ()
  : Sem.Mst (Sem.full_mem st)
           (fun _ -> True)
           (fun s0 s s1 -> s0 == s /\ s == s1)
  = NMST.get ()

let rewrite_l_3 (p1 p2 q r:slprop) : Lemma
    (requires p1 `equiv` p2)
    (ensures (p1 `star` q `star` r) `equiv` (p2 `star` q `star` r))
    = calc (equiv) {
        p1 `star` q `star` r;
        (equiv) { star_associative p1 q r }
        p1 `star` (q `star` r);
        (equiv) { equiv_extensional_on_star p1 p2 (q `star` r) }
        p2 `star` (q `star` r);
        (equiv) { star_associative p2 q r }
        p2 `star` q `star` r;
      }

#push-options "--z3rlimit_factor 2"
let bind_steel_steel a b #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #frame_g #post f g =
  fun frame' ->
  let x = frame_aux f frame_f frame' in
  let y = frame_aux (g x) (frame_g x) frame' in

  let m1 = nmst_get() in

  // We have the following
  // assert (interp
  //   ((post_g x y `star` frame_g x) `star` frame' `star` locks_invariant Set.empty m1)
  //     m1);

  // We need to prove
  // assert ((post y `star` frame' `star` locks_invariant Set.empty m1) `equiv`
  //   ((post_g x y `star` frame_g x) `star` frame' `star` locks_invariant Set.empty m1));

  // We do this by calling the following lemma
  rewrite_l_3 (post y) (post_g x y `star` frame_g x) frame' (locks_invariant Set.empty m1);

  // To get
  // assert (interp (post y `star` frame' `star` locks_invariant Set.empty m1) m1);

  y

let bind_steel_steelf (a:Type) (b:Type)
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_f #post
  f g =
  fun frame' ->
  let x = frame_aux f frame_f frame' in
  let y = (g x) frame' in

  let m1 = nmst_get () in
  rewrite_l_3 (post y) (post_g x y) frame' (locks_invariant Set.empty m1);

  y
#pop-options

let bind_steelf_steel (a:Type) (b:Type)
  #pre_f #post_f #req_f #ens_f #pre_g #post_g #req_g #ens_g #frame_g #post
  f g =
  fun frame' ->
  let x = f frame' in
  let y = frame_aux (g x) (frame_g x) frame' in

  let m1 = nmst_get () in
  rewrite_l_3 (post y) (post_g x y `star` frame_g x) frame' (locks_invariant Set.empty m1);

  y

let bind_pure_steel_ a b f g = fun frame ->
  let x = f () in
  (g x) frame



// unfold
let bind_div_steel_req (#a:Type) (wp:pure_wp a)
  (#pre_g:pre_t) (req_g:a -> req_t pre_g)
: req_t pre_g
= FStar.Monotonic.Pure.wp_monotonic_pure ();
  fun h -> wp (fun _ -> True) /\ (forall x. (req_g x) h)

// unfold
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
  (#[@@@ framing_implicit] pre_g:pre_t) (#[@@@ framing_implicit] post_g:post_t b)
  (#[@@@ framing_implicit] req_g:a -> req_t pre_g)
  (#[@@@ framing_implicit] ens_g:a -> ens_t pre_g b post_g)
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

let par0 (#aL:Type u#a) (#preL:slprop u#1) (#postL:aL -> slprop u#1)
         (#lpreL:req_t preL) (#lpostL:ens_t preL aL postL)
         (f:repr aL preL postL lpreL lpostL)
         (#aR:Type u#a) (#preR:slprop u#1) (#postR:aR -> slprop u#1)
         (#lpreR:req_t preR) (#lpostR:ens_t preR aR postR)
         (g:repr aR preR postR lpreR lpostR)
  : Steel (aL & aR)
    (preL `Mem.star` preR)
    (fun y -> postL (fst y) `Mem.star` postR (snd y))
    (fun h -> lpreL h /\ lpreR h)
    (fun h0 y h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 (fst y) h1 /\ lpostR h0 (snd y) h1)
  = Steel?.reflect (fun frame -> Sem.run #state #_ #_ #_ #_ #_ frame (Sem.Par (Sem.Act f) (Sem.Act g)))

let par (#aL:Type u#a)
        (#preL:slprop u#1)
        (#postL:aL -> slprop u#1)
        (#lpreL:req_t preL)
        (#lpostL:ens_t preL aL postL)
        ($f:unit -> Steel aL preL postL lpreL lpostL)
        (#aR:Type u#a)
        (#preR:slprop u#1)
        (#postR:aR -> slprop u#1)
        (#lpreR:req_t preR)
        (#lpostR:ens_t preR aR postR)
        ($g:unit -> Steel aR preR postR lpreR lpostR)
  : Steel (aL & aR)
    (preL `Mem.star` preR)
    (fun y -> postL (fst y) `Mem.star` postR (snd y))
    (fun h -> lpreL h /\ lpreR h)
    (fun h0 y h1 -> lpreL h0 /\ lpreR h0 /\ lpostL h0 (fst y) h1 /\ lpostR h0 (snd y) h1)
  = par0 (reify (f ())) (reify (g()))

let action_as_repr (#a:Type) (#p:slprop) (#q:a -> slprop) (f:action_except a Set.empty p q)
  : repr a p q (fun _ -> True) (fun _ _ _ -> True)
  = Ins.state_correspondence Set.empty; f

let add_action f = Steel?.reflect (action_as_repr f)

let change_slprop p q proof = add_action (Steel.Memory.change_slprop p q proof)

let rewrite_context #p #q _ =
  assert (p `equiv` q);
  SteelF?.reflect (action_as_repr (Steel.Memory.change_slprop p q (fun m -> ())))

let sladmit #a #p #q _ = SteelF?.reflect (fun _ -> NMST.nmst_admit ())

let intro_pure p = change_slprop emp (pure p) (fun m -> pure_interp p m)

let read r v0 = Steel?.reflect (action_as_repr (sel_action FStar.Set.empty r v0))
let write r v0 v1 = Steel?.reflect (action_as_repr (upd_action FStar.Set.empty r v0 v1))
let alloc x = Steel?.reflect (action_as_repr (alloc_action FStar.Set.empty x))
let free r x = Steel?.reflect (action_as_repr (free_action FStar.Set.empty r x))

val split' (#a:Type)
          (#p:FStar.PCM.pcm a)
          (r:ref a p)
          (v0:Ghost.erased a)
          (v1:Ghost.erased a{FStar.PCM.composable p v0 v1})
  : SteelT unit (pts_to r (FStar.PCM.op p v0 v1))
                (fun _ -> pts_to r v0 `star` pts_to r v1)

let split' #a #p r v0 v1 = Steel?.reflect (action_as_repr (split_action FStar.Set.empty r v0 v1))

let split #a #p r v v0 v1 =
  change_slprop (pts_to r v) (pts_to r (FStar.PCM.op p v0 v1)) (fun _ -> ());
  split' r v0 v1

let gather r v0 v1 = Steel?.reflect (action_as_repr (gather_action FStar.Set.empty r v0 v1))
let witness r fact v _ = Steel?.reflect (action_as_repr (Steel.Memory.witness FStar.Set.empty r fact v ()))
let recall r v = Steel?.reflect (action_as_repr (Steel.Memory.recall FStar.Set.empty r v))

let cond_aux (#a:Type) (b:bool) (p: (b':bool{b == b'}) -> slprop)
             (q: bool -> a -> slprop)
             ($then_:squash (b==true) -> Steel a (p b) (q b) (fun _ -> b==true) (fun _ _ _ -> True))
             ($else_:squash (b==false) -> Steel a (p b) (q b) (fun _ -> b==false) (fun _ _ _ -> True))
  : SteelT a (p b) (q b)
  = if b then then_ () else else_ ()

let aux1 (#a:Type) (b:bool{b == true})
         (p: (b':bool{b == b'}) -> slprop)
         (q: bool -> a -> slprop)
         (then_: (squash (b==true) -> SteelT a (p true) (q true)))
  : unit -> SteelT a (p b) (q b)
  = fun _ ->
      change_slprop (p b) (p true) (fun _ -> ());
      let x = then_ () in change_slprop (q true x) (q b x) (fun _ -> ());
      x

let aux2 (#a:Type) (b:bool)
         (p: (b':bool{b == b'}) -> slprop)
         (q: bool -> a -> slprop)
         (then_: (squash (b==true) -> SteelT a (p true) (q true)))
  : squash (b==true) -> Steel a (p b) (q b) (fun _ -> b == true) (fun _ _ _ -> True)
  = fun _ -> (aux1 b p q then_) ()

let aux3 (#a:Type) (b:bool{b == false})
         (p: (b':bool{b == b'}) -> slprop)
         (q: bool -> a -> slprop)
         (else_: (squash (b==false) -> SteelT a (p false) (q false)))
  : squash (b==false) -> SteelT a (p b) (q b)
  = fun _ ->
      change_slprop (p b) (p false) (fun _ -> ());
      let x = else_ () in change_slprop (q false x) (q b x) (fun _ -> ());
      x

let aux4 (#a:Type) (b:bool)
         (p: (b':bool{b == b'}) -> slprop)
         (q: bool -> a -> slprop)
         (else_: (squash (b==false) -> SteelT a (p false) (q false)))
  : squash (b==false) -> Steel a (p b) (q b) (fun _ -> b == false) (fun _ _ _ -> True)
  = fun _ -> (aux3 b p q else_) ()

let cond (#a:Type)
         (b:bool)
         (p: (b':bool{b == b'}) -> slprop)
         (q: bool -> a -> slprop)
         (then_: (squash (b == true) -> SteelT a (p true) (q true)))
         (else_: (squash (b == false) -> SteelT a (p false) (q false)))
  : SteelT a (p b) (q b)
  = cond_aux b p q (aux2 b p q then_) (aux4 b p q else_)

let drop p = change_slprop p emp (fun m -> emp_unit p; affine_star p emp m)

let intro_exists #a x p = change_slprop (p x) (h_exists p) (fun m -> intro_h_exists x p m)

let noop #p () = change_slprop p p (fun _ -> ())

let select_refine #a #p r x f = add_action (Steel.Memory.select_refine Set.empty r x f)

let upd_gen #a #p r x y f = add_action (Steel.Memory.upd_gen Set.empty r x y f)
