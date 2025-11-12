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

module Pulse.Lib.Send
open Pulse.Lib.Core
open Pulse.Class.Duplicable
open Pulse.Main
#lang-pulse

ghost fn placeless_move (p: slprop) {| inst: placeless p |} l1 l2
  requires on l1 p
  ensures on l2 p
{
  inst l1 l2
}

ghost fn placeless_on_intro (p: slprop) {| placeless p |} l
  requires p
  ensures on l p
{
  let l0 = loc_get ();
  on_intro p;
  placeless_move p l0 l;
  drop_ (loc l0)
}

ghost fn placeless_on_elim (p: slprop) {| placeless p |} l
  requires on l p
  ensures p
{
  let l0 = loc_get ();
  placeless_move p l l0;
  on_elim p;
  drop_ (loc l0)
}

ghost fn placeless_on (l: loc_id) (p: slprop) : placeless (on l p) = l1 l2 {
  on_on_eq l1 l p; rewrite on l1 (on l p) as on l p;
  on_on_eq l2 l p; rewrite on l p as on l2 (on l p);
}

[@@deprecated "impersonate is unsound; only use for model implementations"]
noextract inline_for_extraction
fn impersonate
    u#a (a: Type u#a)
    (l: loc_id) (pre: slprop) (post: a -> slprop)
    {| placeless pre, ((x:a) -> placeless (post x)) |}
    (f: unit -> stt a (loc l ** pre) (fun x -> loc l ** post x))
  requires pre
  returns x: a
  ensures post x
{
  on_loc_eq l l; rewrite pure (l == l) as on l (loc l);
  placeless_on_intro pre l;
  on_star_eq l (loc l) pre; rewrite on l (loc l) ** on l pre as on l (loc l ** pre);
  let x = impersonate_core l (loc l ** pre) post fn _ {
    let x = f ();
    drop_ (loc l);
    x
  };
  placeless_on_elim (post x) l;
  x
}

[@@deprecated "atomic_impersonate is unsound; only use for model implementations"]
noextract inline_for_extraction
atomic fn atomic_impersonate
    u#a (a: Type u#a)
    (#[T.exact (`emp_inames)] is: inames)
    (l: loc_id) (pre: slprop) (post: a -> slprop)
    {| placeless pre, ((x:a) -> placeless (post x)) |}
    (f: unit -> stt_atomic a is (loc l ** pre) (fun x -> loc l ** post x))
  opens is
  requires pre
  returns x: a
  ensures post x
{
  on_loc_eq l l; rewrite pure (l == l) as on l (loc l);
  placeless_on_intro pre l;
  on_star_eq l (loc l) pre; rewrite on l (loc l) ** on l pre as on l (loc l ** pre);
  let x = atomic_impersonate_core #a #is #Observable l (loc l ** pre) post fn _ {
    let x = f ();
    drop_ (loc l);
    x
  };
  placeless_on_elim (post x) l;
  x
}

[@@deprecated "unobservable_impersonate is unsound; only use for model implementations"]
noextract inline_for_extraction
unobservable fn unobservable_impersonate
    u#a (a: Type u#a)
    (#[T.exact (`emp_inames)] is: inames)
    (l: loc_id) (pre: slprop) (post: a -> slprop)
    {| placeless pre, ((x:a) -> placeless (post x)) |}
    (f: unit -> stt_atomic a #Neutral is (loc l ** pre) (fun x -> loc l ** post x))
  opens is
  requires pre
  returns x: a
  ensures post x
{
  on_loc_eq l l; rewrite pure (l == l) as on l (loc l);
  placeless_on_intro pre l;
  on_star_eq l (loc l) pre; rewrite on l (loc l) ** on l pre as on l (loc l ** pre);
  let x = atomic_impersonate_core #a #is #Neutral l (loc l ** pre) post fn _ {
    let x = f ();
    drop_ (loc l);
    x
  };
  placeless_on_elim (post x) l;
  x
}

ghost fn ghost_impersonate
    (#[T.exact (`emp_inames)] is: inames)
    (l: loc_id) (pre post: slprop) {| placeless pre, placeless post |}
    (f: unit -> stt_ghost unit is (loc l ** pre) (fun _ -> loc l ** post))
  opens is
  requires pre
  ensures post
{
  on_loc_eq l l; rewrite pure (l == l) as on l (loc l);
  placeless_on_intro pre l;
  on_star_eq l (loc l) pre; rewrite on l (loc l) ** on l pre as on l (loc l ** pre);
  ghost_impersonate_core #is l (loc l ** pre) post fn _ {
    f ();
    drop_ (loc l)
  };
  placeless_on_elim post l;
}

ghost fn placeless_emp' () : placeless emp = l1 l2 {
  ghost_impersonate l2 (on l1 emp) (on l2 emp) fn _ {
    drop_ (on l1 emp);
    on_intro emp;
  }
}
let placeless_emp = placeless_emp' ()

ghost fn placeless_star (a b: slprop) {| placeless a, placeless b |} : placeless (a ** b) = l1 l2 {
  on_star_eq l1 a b; rewrite on l1 (a ** b) as on l1 a ** on l1 b;
  placeless_move a l1 l2;
  placeless_move b l1 l2;
  on_star_eq l2 a b; rewrite on l2 a ** on l2 b as on l2 (a ** b);
}

ghost fn placeless_pure (p: prop) : placeless (pure p) = l1 l2 {
  ghost_impersonate l1 (on l1 (pure p)) (on l2 (pure p)) fn _ {
    on_elim (pure p);
    ghost_impersonate l2 emp (on l2 (pure p)) fn _ {
      on_intro (pure p)
    }
  }
}

ghost fn on_pure_elim l p
  requires on l (pure p)
  ensures pure p
{
  placeless_on_elim (pure p) l;
}

ghost fn placeless_later_credit amt : placeless (later_credit amt) = l1 l2 {
  on_later_credit_eq l1 amt;
  on_later_credit_eq l2 amt;
  rewrite on l1 (later_credit amt) as on l2 (later_credit amt);
}

ghost fn placeless_equiv a b : placeless (equiv a b) = l1 l2 {
  on_equiv_eq l1 a b;
  on_equiv_eq l2 a b;
  rewrite on l1 (equiv a b) as on l2 (equiv a b);
}

ghost fn placeless_slprop_ref_pts_to x y : placeless (slprop_ref_pts_to x y) = l1 l2 {
  on_slprop_ref_pts_to_eq l1 x y;
  on_slprop_ref_pts_to_eq l2 x y;
  rewrite on l1 (slprop_ref_pts_to x y) as on l2 (slprop_ref_pts_to x y);
}

ghost fn placeless_exists' u#a (#a: Type u#a) (p: a -> slprop) {| ((x:a) -> placeless (p x)) |} :
    placeless (exists* x. p x) = l1 l2 {
  ghost_impersonate l1 (on l1 (exists* x. p x)) (on l2 (exists* x. p x)) fn _ {
    on_elim _; with x. assert p x;
    ghost_impersonate l2 (p x) (on l2 (exists* x. p x)) fn _ {
      on_intro (exists* x. p x)
    }
  }
}
let placeless_exists = placeless_exists'

let timeless_in_same_process p =
  assert_norm (in_same_process p == (exists* l. loc l ** pure (process_of l == process_of p)))

ghost fn dup_in_same_process p () : duplicable_f (in_same_process p) = {
  unfold in_same_process p;
  loc_dup _;
  fold in_same_process p;
  fold in_same_process p;
}

instance duplicable_in_same_process p : duplicable (in_same_process p) =
  { dup_f = dup_in_same_process p }

ghost fn on_star_elim #l (p q: slprop)
  requires on l (p ** q)
  ensures on l p
  ensures on l q
{
  ghost_impersonate l (on l (p ** q)) (on l p ** on l q) fn _ {
    on_elim (p ** q);
    on_intro p;
    on_intro q;
  }
}

ghost fn on_star_intro #l (p q: slprop)
  requires on l p
  requires on l q
  ensures on l (p ** q)
{
  ghost_impersonate l (on l p ** on l q) (on l (p ** q)) fn _ {
    on_elim p;
    on_elim q;
    on_intro (p ** q);
  }
}

ghost fn on_exists_elim u#a #l (#a: Type u#a) (p: a -> slprop)
  requires on l (exists* x. p x)
  ensures exists* x. on l (p x)
{
  ghost_impersonate l (on l (exists* x. p x)) (exists* x. on l (p x)) fn _ {
    on_elim (exists* x. p x);
    on_intro (p _);
  }
}

ghost fn is_send_across_elim #b (g: loc_id -> b) p {| inst: is_send_across g p |} #l l'
  requires on l p
  requires pure (g l == g l')
  ensures on l' p
{
  inst l l'
}

ghost fn is_send_elim p {| inst: is_send p |} #l l'
  requires on l p
  requires pure (process_of l == process_of l')
  ensures on l' p
{
  is_send_across_elim process_of p #inst l'
}

ghost fn is_send_elim_on p {| is_send p |} #l
  preserves in_same_process l
  requires on l p
  ensures p
{
  unfold in_same_process l;
  with l0. assert loc l0;
  is_send_elim p l0;
  on_elim p;
  fold in_same_process l;
}

ghost fn is_send_intro_on p {| is_send p |} l
  preserves in_same_process l
  requires p
  ensures on l p
{
  unfold in_same_process l;
  with l0. assert loc l0;
  on_intro p;
  is_send_elim p l;
  fold in_same_process l;
}

ghost fn is_send_elim_on' p {| is_send p |} #l
  preserves loc l
  requires on (process_of l) p
  ensures p
{
  loc_dup l;
  fold in_same_process (process_of l);
  is_send_elim_on p #_;
  drop_ (in_same_process (process_of l));
}

ghost fn is_send_intro_on' p {| is_send p |} l
  preserves loc l
  requires p
  ensures on (process_of l) p
{
  loc_dup l;
  fold in_same_process (process_of l);
  is_send_intro_on p (process_of l);
  drop_ (in_same_process (process_of l));
}

ghost fn is_send_across_placeless #b #g p {| placeless p |} : is_send_across #b g p = l l' {
  placeless_move p l l'
}

ghost fn is_send_across_star #b #g p q {| is_send_across #b g p, is_send_across g q |} : is_send_across g (p ** q) = l l' {
  on_star_elim p q;
  is_send_across_elim g p l';
  is_send_across_elim g q l';
  on_star_intro p q;
}

ghost fn is_send_across_exists' u#a #b #g (#a: Type u#a) (p: a->slprop) {| ((x:a) -> is_send_across #b g (p x)) |} :
    is_send_across g (exists* x. p x) = l l' {
  ghost_impersonate l (on l (exists* x. p x)) (on l' (exists* x. p x)) fn _ {
    on_elim (exists* x. p x);
    with x. assert p x;
    on_intro (p x);
    is_send_across_elim g (p x) l';
    ghost_impersonate l' (on l' (p x)) (on l' (exists* x. p x)) fn _ {
      on_elim (p x);
      on_intro (exists* x. p x)
    };
  }
}
let is_send_across_exists = is_send_across_exists'

ghost fn is_send_in_same_process p : is_send (in_same_process p) = l l' {
  ghost_impersonate l
    (on l (in_same_process p))
    (on l' (in_same_process p))
    fn _ {
      on_elim (in_same_process p);
      unfold in_same_process p;
      loc_gather l #_;
      ghost_impersonate l' emp (on l' (in_same_process p)) fn _ {
        loc_dup l';
        fold in_same_process p;
        on_intro (in_same_process p);
      }
    }
}

let on_same_process (p: slprop) =
  exists* l. in_same_process l ** on l p

ghost fn on_same_process_elim p {| is_send p |}
  requires on_same_process p
  ensures p
{
  unfold on_same_process p;
  is_send_elim_on p #_;
  drop_ (in_same_process _);
}

ghost fn on_same_process_intro p
  requires p
  ensures on_same_process p
{
  let l = loc_get ();
  on_intro p;
  fold in_same_process l;
  fold on_same_process p;
}

let timeless_on_same_process p =
  assert_norm (on_same_process p == (exists* l. in_same_process l ** on l p))

ghost fn is_send_on_same_process p : is_send (on_same_process p) = l1 l2 {
  ghost_impersonate l1
    (on l1 (on_same_process p))
    (on l2 (on_same_process p))
    fn _ {
      on_elim (on_same_process p);
      unfold on_same_process p; with l. _;
      unfold in_same_process l; with l1'. _;
      loc_gather l1 #l1';
      ghost_impersonate l2
        (on l p)
        (on l2 (on_same_process p))
        fn _ {
          loc_dup l2; fold in_same_process l;
          fold on_same_process p;
          on_intro (on_same_process p);
        }
    }
}

let is_send_tag ([@@@mkey] p: slprop) (inst: is_send p) = emp
let sendable p = exists* inst. is_send_tag p inst ** p

ghost fn sendable_elim p
  requires sendable p
  ensures p
{
  unfold sendable p;
  drop_ (is_send_tag p _);
}

ghost fn sendable_intro p {| inst: is_send p |}
  requires p
  ensures sendable p
{
  fold is_send_tag p inst;
  fold sendable p;
}

ghost fn is_send_sendable p : is_send (sendable p) = l1 l2 {
  ghost_impersonate l1 (on l1 (sendable p)) (on l2 (sendable p)) fn _ {
    on_elim (sendable p);
    unfold sendable p;
    with inst. unfold is_send_tag p inst;
    let inst = inst;
    on_intro p;
    is_send_elim p l2;
    ghost_impersonate l2 (on l2 p) (on l2 (sendable p)) fn _ {
      on_elim p;
      fold is_send_tag p inst;
      fold sendable p;
      on_intro (sendable p)
    }
  }
}

inline_for_extraction noextract fn fork'
  (pre:slprop) {| is_send pre |}
  (f: (unit -> stt unit pre (fun _ -> emp)))
  requires pre
{
  let l = loc_get ();
  fork_core pre #l fn _ {
    fold in_same_process l;
    is_send_elim_on pre #_;
    f ();
    drop_ (in_same_process l)
  }
}