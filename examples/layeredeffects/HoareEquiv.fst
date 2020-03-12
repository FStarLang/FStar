(*
   Copyright 2008-2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Guido Martinez, Aseem Rastogi
*)

module HoareEquiv


(* We show that WPs and PrePost pairs are equivalent. We provide
 * an isomorphism between them, assuming usual properties of WPs
 * (monotonicity and conjunctivity, both finite and infinite
 * (for non-empty domains). *)

open FStar.Calc
open FStar.Tactics

let inhabited (a:Type) : prop = (exists (x:a). True)

let is_inhabited_by #a (x:a) : Lemma (inhabited a) = ()

(* The base WP type, unrefined *)
let pure_wp' a = pure_wp a

(* Properties of WPs *)
let monotonic (#a:Type) (wp : pure_wp a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

let conjunctive (#a:Type) (wp : pure_wp a) =
  forall p1 p2. wp (fun x -> p1 x /\ p2 x) <==> (wp p1 /\ wp p2)

let conjunctive_fa (#a:Type) (wp : pure_wp a) =
  forall b (p : a -> b -> Type0).
    inhabited b  ==>
    (wp (fun x -> forall y. p x y) <==> (forall y. wp (fun x -> p x y)))

(* The type of proper WPs *)
let pure_wp a = wp:(pure_wp' a){monotonic wp /\ conjunctive wp /\ conjunctive_fa wp}

(* Just a helper *)
let faconj (#a #b:Type) (wp : pure_wp a) (p : a -> b -> Type0) :
  Lemma
    (requires (inhabited b))
    (ensures (wp (fun x -> forall y. p x y) <==> (forall y. wp (fun x -> p x y)))) = ()

(* Equivalence of WPs *)
let equiv_wp (#a:Type) (wp1 wp2 : pure_wp a) =
  forall p1 p2. (forall x. p1 x <==> p2 x) ==> (wp1 p1 <==> wp2 p2)

let prepo (a:Type) = (pure_pre & pure_post a)

(* Equivalence of PrePost pairs, note we assume the precondition
 * when comparing postconditions, hence (False, p) `equiv_pp` (False, q)
 * forall p and q. *)
let equiv_pp (#a:Type) (pp1 pp2 : prepo a) =
  (fst pp1 <==> fst pp2) /\ (forall x. fst pp1 ==> (snd pp1 x <==> snd pp2 x))

// GM: TODO, fix the parser so we can use (==>) and (<==>) here
let forall_switch #a (wp : pure_wp a) (p : pure_post a)
  : Lemma (requires (inhabited a))
          (ensures ((forall y. wp (fun x -> x == y ==> p y)) <==> wp p))
  =
  calc l_iff {
    forall y. wp (fun x -> x == y ==> p y);
    (l_iff) {}
    forall y. wp (fun x -> x == y ==> p x);
    (l_iff) { faconj wp (fun x y -> x == y ==> p x) }
    wp (fun x -> forall y. x == y ==> p x);
    (l_iff) {}
    wp (fun x -> p x);
    (l_iff) {}
    wp p;
  }

let negwp' #a (wp : pure_wp a) (x:a)
  : Lemma ((forall k. wp k ==> k x) <==> ~(wp (fun y -> x =!= y)))
  =
  calc l_iff {
    ~ (forall k. wp k ==> k x);
    l_iff {}
    exists k. wp k /\ ~ (k x);
    l_iff { (* the SMT really blasts through this one!
               the reasoning is roughly:
                 wp k /\ ~(k x)
                 ==> { forall_switch }
                 (forall x. wp (fun y -> x == y ==> k x)) /\ ~(k x)
                 ==> { instantiate x := x }
                 wp (fun y -> x == y ==> k x) /\ ~(k x)
                 ==> {}
                 wp (fun y -> x == y ==> False)
                 ==>
                 wp (fun y -> x =!= y)
             *)
          }
    wp (fun y -> x =!= y);
  }

let hardlemma #a (wp : pure_wp a) (p : pure_post a)
  : Lemma (requires (wp (fun _ -> True) /\ (forall x. (forall k. wp k ==> k x) ==> p x) /\ inhabited a))
          (ensures (wp p))
  =
  calc l_imp {
    forall x. (forall k. wp k ==> k x) ==> p x;
    l_imp {}
    forall x. ~(forall k. wp k ==> k x) \/ p x;
    l_imp { Classical.forall_intro (negwp' wp) }
    forall x. wp (fun y -> x =!= y) \/ p x;
    l_imp {}
    forall x. wp (fun y -> x =!= y) \/ wp (fun y -> p x);
    l_imp { (* motonicity! *) }
    forall x. wp (fun y -> x =!= y \/ p x);
    l_imp {}
    forall x. wp (fun y -> x == y ==> p x);
    l_imp { forall_switch wp p }
    wp p;
  }

let hardlemma_non_ih #a (wp : pure_wp a) (p : pure_post a)
  : Lemma (requires (wp (fun _ -> True) /\ ~(inhabited a)))
          (ensures (wp p))
  =
  let sub (x:a) : Lemma (True ==> p x) =
    assert (inhabited a);
    assert (~ (inhabited a));
    assert False
  in
  calc l_imp {
    wp (fun x -> True);
    l_imp { Classical.forall_intro sub }
    wp (fun x -> p x);
    l_imp {}
    wp p;
  };
  ()

(* WP -> PrePost *)
val f : #a:Type -> pure_wp a -> prepo a
let f #a wp =
  let pre = wp (fun _ -> True) in
  let post x = forall k. wp k ==> k x in
  (pre, post)

(* PrePost -> WP, without the obligation for now *)
val g0 : #a:Type -> prepo a -> pure_wp' a
let g0 #a (pre, post) = 
  let wp = fun p -> pre /\ (forall x. post x ==> p x) in
  wp

(* Just a helper *)
let push_forall #a (phi :Type) (q : a -> Type0)
    : Lemma (requires (inhabited a))
            (ensures ((phi /\ (forall x. q x)) <==> (forall x. phi /\ q x)))
    = ()

let cfa_helper #a (wp : pure_wp' a)
  (pf : (b:Type) -> (p : (a -> b -> Type0)) -> Lemma (requires (inhabited b))
                                                 (ensures (wp (fun x -> forall y. p x y)
                                                        <==> (forall y. wp (fun x -> p x y)))))
  : Lemma (conjunctive_fa wp)
  = let pf' () : Lemma (forall b (p : a -> b -> Type0). inhabited b  ==> (wp (fun x -> forall y. p x y) <==> (forall y. wp (fun x -> p x y)))) =
        Classical.forall_intro_2 (fun b p -> Classical.move_requires (pf b) p)
    in
    let pf'' () : Lemma (conjunctive_fa wp) =
      //lem'' ();
      // GM: ^ Very puzzled that this doesn't work. I'm assuming it's an issue
      // with the hash-conshing in the SMT encoding, and the tactic call
      // below works around it by using the unifier.
      assert (conjunctive_fa wp) by (apply_lemma (quote pf'));
    ()
    in
    pf'' ()

(* The result of g0 is forall-conjunctive, which apparently is hard to prove for the SMT *)
val g0_conj_fa : #a:Type -> pp:(prepo a) -> Lemma (conjunctive_fa (g0 pp))
let g0_conj_fa #a (pre, post) =
  let wp = g0 (pre, post) in
  let lem (b:Type) (p : a -> b -> Type0) : Lemma (requires (inhabited b))
                                              (ensures (wp (fun x -> forall y. p x y))
                                                         <==> (forall y. wp (fun x -> p x y)))
  =
    calc l_iff {
      wp (fun x -> forall y. p x y);
      l_iff { (* def *) }
      pre /\ (forall x. post x ==> (forall y. p x y));
      l_iff { (* logic *) }
      pre /\ (forall y. (forall x. post x ==> p x y));
      l_iff { push_forall pre (fun y -> forall x. post x ==> p x y) }
      forall y. pre /\ (forall x. post x ==> p x y);
      l_iff { (* def *) }
      forall y. wp (fun x -> p x y);
    }
  in
  cfa_helper wp lem;
  ()

(* PrePost -> WP, now for real *)
val g : #a:Type -> (prepo a) -> pure_wp a
let g #a pp =
  g0_conj_fa pp;
  g0 pp

val iso1 : #a:Type -> wp:(pure_wp a) -> Lemma (g (f wp) `equiv_wp` wp)
let iso1 #a wp =
  let lem_a (p:pure_post a) : Lemma (requires wp p) (ensures g (f wp) p) =
    (* easy *)
    ()
  in
  let lem_b (p:pure_post a) : Lemma (requires g (f wp) p) (ensures wp p) =
    (* hard :) *)
    if StrongExcludedMiddle.strong_excluded_middle (inhabited a)
    then hardlemma wp p
    else hardlemma_non_ih wp p
  in
  Classical.forall_intro (Classical.move_requires lem_a);
  Classical.forall_intro (Classical.move_requires lem_b);
  ()

let iso2_pre (#a:Type) (pre:pure_pre) (post:(pure_post a)) :
    Lemma (pre <==> fst (f (g (pre, post))))
  = ()
  
let iso2_post (#a:Type) (pre:pure_pre) (post:(pure_post a)) (x:a) :
    Lemma (pre ==> (post x <==> snd (f (g (pre, post))) x))
  = ()
let iso2 (#a:Type) (pp:prepo a) :
    Lemma (pp `equiv_pp` f (g pp))
  = let pre, post = pp in
    iso2_pre pre post;
    Classical.forall_intro (iso2_post pre post);
    ()

(* Some lemmas that ended up unused *)
let negwp #a (wp : pure_wp a) (p : pure_post a) (y:a)
  : Lemma (requires (wp p /\ ~(p y)))
          (ensures (wp (fun x -> x =!= y)))
  =
  is_inhabited_by y;
  calc (l_imp) {
    wp p;
    l_iff {}
    wp (fun x -> p x);
    l_iff { forall_switch wp p }
    forall y. wp (fun x -> x == y ==> p y);
    l_imp {}
    wp (fun x -> x == y ==> p y);
    l_imp {}
    wp (fun x -> x =!= y);
  }

let movein #a (wp : pure_wp a) (p : pure_post a)
  : Lemma (wp p <==> wp (fun x -> p x /\ wp p))
  =
  calc l_iff {
    wp p;
    (l_iff) { (* monotonicity *) }
    wp p /\ wp (fun _ -> True);
    (l_iff) { (* True ==> wp p, monotonicity again *)}
    wp p /\ wp (fun _ -> wp p);
    (l_iff) { (* conjunctivity *) }
    wp (fun x -> p x /\ wp p);
  }


(*** Proofs about the wp-req-ens rewriting laws ***)


let as_requires (#a:Type) (wp:pure_wp a) : pure_pre = fst (f wp)
let as_ensures (#a:Type) (wp:pure_wp a) : pure_post a = snd (f wp)

let post_equiv (#a:Type) (p1 p2:pure_post a) =
  forall (x:a). p1 x <==> p2 x

(**** return ****)

let return_wp (#a:Type) (x:a) : pure_wp a =
  let wp = fun p -> p x in
  cfa_helper wp (fun _ _ -> ());
  wp

let as_requires_return (#a:Type) (_:a) : pure_pre = True
let as_ensures_return (#a:Type) (x:a) : pure_post a = fun y -> y == x

let as_req_return_equiv (#a:Type) (x:a)
: Lemma (as_requires (return_wp x) <==> as_requires_return x)
= ()

let as_ens_return_equiv (#a:Type) (x:a)
: Lemma (as_ensures (return_wp x) `post_equiv` as_ensures_return x)
= ()


(**** bind ****)

let bind_wp' (#a:Type) (#b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b) : pure_wp' b =
  fun p -> wp1 (fun x -> wp2 x p)

let cfa_helper_aux (a:Type) (b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b) (c:Type) (p:b -> c -> Type0)
: Lemma
  (requires inhabited c)
  (ensures
    (bind_wp' wp1 wp2) (fun x -> forall y. p x y) <==>
    (forall y. (bind_wp' wp1 wp2) (fun x -> p x y)))
= admit ()

let bind_wp_conjunctive_helper (#a:Type) (#b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b) (p1 p2:pure_post b)
: Lemma
  (let wp = bind_wp' wp1 wp2 in
   wp (fun x -> p1 x /\ p2 x) <==> (wp p1 /\ wp p2))
= let apply_conj (#a:Type) (wp:pure_wp a) (p1 p2:pure_post a)
    : Lemma (wp (fun x -> p1 x /\ p2 x) <==> (wp p1 /\ wp p2))
    = () in
  let aux ()
    : Lemma
      (wp1 (fun x -> wp2 x p1 /\ wp2 x p2) <==> (wp1 (fun x -> wp2 x p1) /\ wp1 (fun x -> wp2 x p2)))
    = apply_conj wp1 (fun x -> wp2 x p1) (fun x -> wp2 x p2)
  in
  aux ()

let bind_wp_conjunctive (#a:Type) (#b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b)
: Lemma (conjunctive (bind_wp' wp1 wp2))
= Classical.forall_intro_2 (bind_wp_conjunctive_helper wp1 wp2)

let bind_wp (#a:Type) (#b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b) : pure_wp b =
  let wp = bind_wp' wp1 wp2 in
  cfa_helper (bind_wp' wp1 wp2) (cfa_helper_aux a b wp1 wp2);
  bind_wp_conjunctive wp1 wp2;
  wp

let as_requires_bind (#a:Type) (#b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b) : pure_pre =
  as_requires wp1 /\ (forall (x:a). as_ensures wp1 x ==> as_requires (wp2 x))

let as_ensures_bind (#a:Type) (#b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b) : pure_post b =
  fun y -> exists (x:a). (as_ensures wp1) x /\ as_ensures (wp2 x) y

#push-options "--warn_error -271"
let as_req_bind_equiv (#a:Type) (#b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b)
: Lemma (as_requires (bind_wp wp1 wp2) <==> as_requires_bind wp1 wp2)
= let aux ()
    : Lemma
      (requires
        wp1 (fun _ -> True) /\ (forall x. (forall k. wp1 k ==> k x) ==> wp2 x (fun _ -> True)))
      (ensures wp1 (fun x -> wp2 x (fun _ -> True)))
      [SMTPat ()]
    = if FStar.StrongExcludedMiddle.strong_excluded_middle (inhabited a)
      then hardlemma wp1 (fun x -> wp2 x (fun _ -> True))
      else hardlemma_non_ih wp1 (fun x -> wp2 x (fun _ -> True))
  in
  ()
#pop-options

let as_ens_bind_equiv1 (#a:Type) (#b:Type) (wp1:pure_wp a{wp1 (fun _ -> True)}) (wp2:a -> pure_wp b) (x:b)
: Lemma (requires as_ensures (bind_wp wp1 wp2) x) (ensures as_ensures_bind wp1 wp2 x)
= let wp_property (#a:Type) (wp:pure_wp a) (p:pure_post a)
    : Lemma
      (requires wp (fun _ -> True) /\ (forall (x:a). wp (fun y -> y =!= x) \/ p x))
      (ensures wp p)
    = Classical.forall_intro (negwp' wp);
      if StrongExcludedMiddle.strong_excluded_middle (inhabited a)
      then hardlemma wp p
      else hardlemma_non_ih wp p in

  let as_ensures' (#a:Type) (wp:pure_wp a) : pure_post a =
    fun y -> ~ (wp (fun x -> x =!= y)) in

  let as_ensures_bind' (#a:Type) (#b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b) : pure_post b =
    fun y -> exists (x:a). (as_ensures' wp1) x /\ as_ensures' (wp2 x) y in

  let as_ens_bind_equiv_helper (#a:Type) (#b:Type) (wp1:pure_wp a) (wp2:a -> pure_wp b) (y:b)
    : Lemma
      (requires wp1 (fun _ -> True) /\ (forall (x:a). wp1 (fun z -> z =!= x) \/ (wp2 x) (fun z -> z =!= y)))
      (ensures wp1 (fun x -> (wp2 x) (fun z -> z =!= y)))
    = wp_property wp1 (fun x -> (wp2 x) (fun z -> z =!= y)) in
  Classical.move_requires (as_ens_bind_equiv_helper wp1 wp2) x;

  negwp' (bind_wp wp1 wp2) x

#push-options "--warn_error -271"
let as_ens_bind_equiv (#a:Type) (#b:Type) (wp1:pure_wp a{wp1 (fun _ -> True)}) (wp2:a -> pure_wp b)
: Lemma (as_ensures (bind_wp wp1 wp2) `post_equiv` as_ensures_bind wp1 wp2)
= let aux1 x
    : Lemma (requires as_ensures (bind_wp wp1 wp2) x) (ensures as_ensures_bind wp1 wp2 x)
      [SMTPat ()]
    = as_ens_bind_equiv1 wp1 wp2 x
  in
  ()
#pop-options


(**** assume ****)

let assume_wp (p:Type) : pure_wp unit =
  let wp = fun post -> p ==> post () in
  cfa_helper wp (fun _ _ -> ());
  wp

let as_requires_assume (p:Type) : pure_pre = True
let as_ensures_assume (p:Type) : pure_post unit = fun _ -> p

let as_req_assume_equiv (p:Type)
: Lemma (as_requires_assume p <==> as_requires (assume_wp p))
= ()

let as_ens_assume_equiv (p:Type)
: Lemma (as_ensures_assume p `post_equiv` as_ensures (assume_wp p))
= ()


(**** assert ****)

let assert_wp (p:Type) : pure_wp unit =
  let wp = fun post -> p /\ post () in
  cfa_helper wp (fun _ _ -> ());
  wp

let as_requires_assert (p:Type) : pure_pre = p
let as_ensures_assert (p:Type) : pure_post unit = fun _ -> True

let as_req_assert_equiv (p:Type)
: Lemma (as_requires_assert p <==> as_requires (assert_wp p))
= ()

let as_ens_assert_equiv (p:Type)
: Lemma (as_ensures_assert p `post_equiv` as_ensures (assert_wp p))
= ()


(**** weaken ****)

let weaken_wp (#a:Type) (wp:pure_wp a) (p:Type0) : pure_wp a =
  let wp = fun post -> p ==> wp post in
  cfa_helper wp (fun _ _ -> ());
  wp

let as_requires_weaken (#a:Type) (wp:pure_wp a) (p:Type0) : pure_pre =
  p ==> as_requires wp

let as_ensures_weaken (#a:Type) (wp:pure_wp a) (p:Type0) : pure_post a =
  fun x -> p /\ (as_ensures wp) x

let as_req_weaken_equiv (#a:Type) (wp:pure_wp a) (p:Type0)
: Lemma (as_requires_weaken wp p <==> as_requires (weaken_wp wp p))
= ()

let as_ens_weaken_equiv (#a:Type) (wp:pure_wp a) (p:Type0)
: Lemma (as_ensures_weaken wp p `post_equiv` as_ensures (weaken_wp wp p))
= ()


(**** strengthen ****)

let strengthen_wp (#a:Type) (wp:pure_wp a) (p:Type0) : pure_wp a =
  let wp = fun post -> p /\ wp post in
  cfa_helper wp (fun _ _ -> ());
  wp

let as_requires_strengthen (#a:Type) (wp:pure_wp a) (p:Type0) : pure_pre = p /\ as_requires wp
let as_ensures_strengthen (#a:Type) (wp:pure_wp a) (p:Type0) : pure_post a = fun x -> as_ensures wp x

let as_req_strengthen_equiv (#a:Type) (wp:pure_wp a) (p:Type0)
: Lemma (as_requires_strengthen wp p <==> as_requires (strengthen_wp wp p))
= ()

let as_ens_strengthen_equiv (#a:Type) (wp:pure_wp a) (p:Type0{p})
: Lemma (as_ensures_strengthen wp p `post_equiv` as_ensures (strengthen_wp wp p))
= ()


(**** if_then_else ****)

/// TODO


(**** ite ****)

/// TODO


(**** close ****)

/// TODO


(**** null ****)

let null_wp (a:Type) : pure_wp a =
  let wp = fun post -> forall (x:a). post x in
  assume (monotonic wp);
  assume (conjunctive wp);
  cfa_helper wp (fun _ _ -> ());
  wp

let as_requires_null (_:Type) : pure_pre = True
let as_ensures_null (a:Type) : pure_post a = fun _ -> True

module T = FStar.Tactics

let as_req_null (a:Type) : Lemma (as_requires_null a <==> as_requires (null_wp a)) =
  let aux (a:Type)
    : Lemma (as_requires (null_wp a)) by (T.norm [delta_only [`%as_requires; `%null_wp; `%f; `%fst]])
    = () in
  aux a

let as_ens_null (a:Type) : Lemma (as_ensures_null a `post_equiv` as_ensures (null_wp a))
  by (T.norm [delta_only [`%as_ensures; `%null_wp; `%f; `%snd]])
= ()
