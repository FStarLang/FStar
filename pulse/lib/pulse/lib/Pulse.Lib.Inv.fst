(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.Inv
#lang-pulse
open Pulse.Lib.Core
open Pulse.Class.Duplicable
module C = Pulse.Lib.Core.Inv

ghost fn placeless_c_inv' (i: iname) (p: slprop) : placeless (C.inv i p) = l1 l2 {
  C.on_inv_eq l1 i p;
  C.on_inv_eq l2 i p;
  rewrite on l1 (C.inv i p) as on l2 (C.inv i p);
}
instance placeless_c_inv = placeless_c_inv'

unfold
let move_tag0 l1 l2 p
  (f: unit -> stt_ghost unit emp_inames (on l1 p) (fun _ -> on l2 p))
  = emp

let move_tag l1 l2 p f g =
  move_tag0 l1 l2 p f ** move_tag0 l2 l1 p g

let inv (i: iname) (p: slprop) =
  exists* l l' f g.
  loc l ** move_tag l l' p f g **
  C.inv i (on l' p)

let aux #p (inst: placeless p) l1 l2 =
  fun () -> inst l1 l2

ghost fn move i p l1 l2
    (fwd: unit -> stt_ghost unit emp_inames (on l1 p) (fun _ -> on l2 p))
    (bwd: unit -> stt_ghost unit emp_inames (on l2 p) (fun _ -> on l1 p))
  requires on l1 (inv i p)
  ensures on l2 (inv i p)
{
  ghost_impersonate l1 (on l1 (inv i p)) (on l2 (inv i p)) fn _ {
    on_elim (inv i p);
    unfold inv i p; with l_ l' f g. _;
    loc_gather l1 #l_;
    drop_ (move_tag l_ l' p _ _);
    ghost_impersonate l2 (C.inv i (on l' p)) (on l2 (inv i p)) fn _ {
      ghost fn f' ()
        requires on l2 p
        ensures on l' p
      {
        bwd ();
        let f = f; f ()
      };
      ghost fn g' ()
        requires on l' p
        ensures on l2 p
      {
        let g = g; g ();
        fwd ();
      };
      fold move_tag l2 l' p f' g';
      loc_dup l2;
      fold inv i p;
      on_intro (inv i p);
    }
  }
}

ghost fn is_send_across_inv #b #g i p {| inst: is_send_across #b g p |} : is_send_across g (inv i p) = l1 l2 {
  move i p l1 l2
    fn _ { inst l1 l2 }
    fn _ { inst l2 l1 }
}

ghost fn dup_inv' i p () : duplicable_f (inv i p) = {
  unfold inv i p; with l l' f g. _;
  C.dup_inv i (on l' p);
  loc_dup _;
  fold move_tag l l' p f g;
  fold inv i p;
  fold inv i p;
}

instance duplicable_inv i p : duplicable (inv i p) =
  { dup_f = dup_inv' i p }

ghost fn fresh_invariant
    (ctx: inames { Pulse.Lib.GhostSet.is_finite ctx })
    (p: slprop)
  requires p
  returns i: iname
  ensures inv i p
  ensures pure (~(Pulse.Lib.GhostSet.mem i ctx))
{
  let l = loc_get ();
  on_intro p;
  let i = C.fresh_invariant ctx (on l p);
  ghost fn f () requires on l p ensures on l p {};
  fold move_tag l l p f f;
  fold inv i p;
  i
}

ghost fn new_invariant (p: slprop)
  requires p
  returns i: iname
  ensures inv i p
{
  fresh_invariant emp_inames p
}

inline_for_extraction noextract
unobservable fn with_inv_unobs u#a (a: Type u#a)
    is (i: iname { not (mem_inv is i) }) (p: slprop) pre (post: a->slprop)
    (k: unit -> stt_atomic a #Neutral is (pre ** p) (fun x -> post x ** p))
  opens add_inv is i
  preserves inv i p
  requires later_credit 1
  requires pre
  returns x:a
  ensures post x
{
  unfold inv i p; with l l' f g. _;
  let x = C.with_invariant #a #Neutral
      #(pre ** later_credit 1 ** loc l)
      #(fun x -> post x ** loc l) #is #(on l' p) i fn _ {
    unfold C.somewhere (later (on l' p));
    with l''. assert on l'' (later (on l' p));
    on_on_eq l'' l' (later p); on_later_eq l' p;
    rewrite on l'' (later (on l' p)) as later (on l' p);
    later_elim (on l' p);
    { let g=g; g() };
    on_elim p;
    let x = k ();
    on_intro p;
    { let f=f; f() };
    later_intro (on l' p);
    rewrite later (on l' p) as on l'' (later (on l' p));
    fold C.somewhere (later (on l' p));
    x
  };
  fold inv i p;
  x
}

ghost fn with_invariants_g u#a (a: Type u#a)
    is (i: iname { not (mem_inv is i) }) (p: slprop) pre (post: a->slprop)
    (k: unit -> stt_ghost a is (pre ** p) (fun x -> post x ** p))
  opens add_inv is i
  preserves inv i p
  requires later_credit 1
  requires pre
  returns x:a
  ensures post x
{
  ghost fn k ()
    opens is
    requires pre ** p
    returns x: Ghost.erased a
    ensures post x ** p
  {
    let r = k ();
    r
  };
  let r = with_inv_unobs (Ghost.erased a) is i p pre (fun r -> post r) fn _ { k () };
  r
}

inline_for_extraction noextract
atomic fn with_invariants_a u#a (a: Type u#a)
    is (i: iname { not (mem_inv is i) }) (p: slprop) pre (post: a->slprop)
    (k: unit -> stt_atomic a #Observable is (pre ** p) (fun x -> post x ** p))
  opens add_inv is i
  preserves inv i p
  requires later_credit 1
  requires pre
  returns x:a
  ensures post x
{
  unfold inv i p; with l l' f g. _;
  let x = C.with_invariant #a #Observable
      #(pre ** later_credit 1 ** loc l)
      #(fun x -> post x ** loc l) #is #(on l' p) i fn _ {
    unfold C.somewhere (later (on l' p));
    with l''. assert on l'' (later (on l' p));
    on_on_eq l'' l' (later p); on_later_eq l' p;
    rewrite on l'' (later (on l' p)) as later (on l' p);
    later_elim (on l' p);
    { let g=g; g() };
    on_elim p;
    let x = k ();
    on_intro p;
    { let f=f; f() };
    later_intro (on l' p);
    rewrite later (on l' p) as on l'' (later (on l' p));
    fold C.somewhere (later (on l' p));
    x
  };
  fold inv i p;
  x
}

inline_for_extraction noextract
fn with_invariants u#a (a: Type u#a)
    is (i: iname { not (mem_inv is i) }) (p: slprop) pre (post: a->slprop)
    (k: unit -> stt_atomic a #Observable is (pre ** p) (fun x -> post x ** p))
  preserves inv i p
  requires pre
  returns x:a
  ensures post x
{
  later_credit_buy 1;
  with_invariants_a a is i p pre post k
}