(*
   Copyright 2019 Microsoft Research

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
module ParDivWP
module T = FStar.Tactics

(**
 * This module provides a semantic model for a combined effect of
 * divergence, state and parallel composition of atomic actions.
 *
 * It also builds a generic separation-logic-style program logic
 * for this effect, in a partial correctness setting.

 * It is also be possible to give a variant of this semantics for
 * total correctness. However, we specifically focus on partial correctness
 * here so that this semantics can be instantiated with lock operations,
 * which may deadlock. See ParTot.fst for a total-correctness variant of
 * these semantics.
 *
 *)
#push-options "--using_facts_from '+Prims +FStar.Pervasives +ParDivWP' --max_fuel 0 --max_ifuel 2 --initial_ifuel 2"

/// We start by defining some basic notions for a commutative monoid.
///
/// We could reuse FStar.Algebra.CommMonoid, but this style with
/// quanitifers was more convenient for the proof done here.

let symmetry #a (equals: a -> a -> prop) =
  forall x y. {:pattern (x `equals` y)}
    x `equals` y ==> y `equals` x

let transitive #a (equals:a -> a -> prop) =
  forall x y z. x `equals` y /\ y `equals` z ==> x `equals` z

let associative #a (equals: a -> a -> prop) (f: a -> a -> a)=
  forall x y z.{:pattern f x (f y z) \/ f (f x y) z}
    f x (f y z) `equals` f (f x y) z

let commutative #a (equals: a -> a -> prop) (f: a -> a -> a) =
  forall x y.{:pattern f x y}
    f x y `equals` f y x

let is_unit #a (x:a) (equals: a -> a -> prop) (f:a -> a -> a) =
  forall y. {:pattern f x y \/ f y x}
    f x y `equals` y /\
    f y x `equals` y

let equals_ext #a (equals:a -> a -> prop) (f:a -> a -> a) =
  forall x1 x2 y. x1 `equals` x2 ==> f x1 y `equals` f x2 y

noeq
type st0 = {
  s:Type;
  r:Type;
  equals: r -> r -> prop;
  emp: r;
  star: r -> r -> r;
  interp: r -> s -> prop;
  split: r -> s -> s & s;
  join: s & s -> s;
  lift: x:r -> (s:s{interp x s} -> prop) -> r
}

let interp_extensionality #r #s (equals:r -> r -> prop) (f:r -> s -> prop) =
  forall x y h. {:pattern equals x y; f x h} equals x y /\ f x h ==> f y h

let rs (#st:st0) (pre:st.r) = state:st.s{st.interp pre state}

let rs_prop' (#st:st0) (pre:st.r) = rs pre -> prop

// only depends on the `pre` footprint of s
let rs_prop  (#st:st0) (pre:st.r) =
  p: rs_prop' pre {
    forall (s:st.s).{:pattern st.interp pre s \/ st.split pre s}
      st.interp pre s ==>
      (st.interp pre (fst (st.split pre s)) /\
      (p s <==> p (fst (st.split pre s))))
  }


let split_idem (st:st0) =
  forall r s. {:pattern st.split r s}
    let s0, _ = st.split r s in
    let s0', _ = st.split r s0 in
    s0 == s0'

let split_join (st:st0) =
    forall r0 s. {:pattern st.join (st.split r0 s)}
      st.join (st.split r0 s) == s

let join_split (st:st0) =
    forall r0 r1 s0 s1. {:pattern st.join (s0, s1); st.interp r0 s0; st.interp r1 s1}
       st.interp (r0 `st.star` r1) (st.join (s0, s1)) /\
       st.interp r0 s0 /\
       st.interp r1 s1 ==>
       fst (st.split r0 (st.join (s0, s1))) == s0

let split_star (st:st0) =
    forall r0 r1 s. {:pattern (st.interp (r0 `st.star` r1) s)}
      st.interp (r0 `st.star` r1) s ==> (
      let s0, s = st.split r0 s in
      st.interp r0 s0 /\
      st.interp r1 s)

let affine (st:st0) =
  forall r0 r1 s. {:pattern (st.interp (r0 `st.star` r1) s) }
    st.interp (r0 `st.star` r1) s ==> st.interp r0 s

let lift_star (st:st0) =
  forall (r0 r1:st.r) (p:rs_prop r0) (s:st.s).
    {:pattern  (st.interp (st.lift r0 p `st.star` r1) s)}
    st.interp (st.lift r0 p `st.star` r1) s <==>
    (st.interp (r0 `st.star` r1) s /\
     st.interp r0 s /\
     st.interp r1 s /\
     p s)

let split_empty (st:st0) =
  forall s0 s1.{:pattern (st.split st.emp s0); fst (st.split st.emp s1)}
    fst (st.split st.emp s0) == fst (st.split st.emp s1)

let emp_valid (st:st0) =
  forall s.{:pattern st.interp st.emp s}
    st.interp st.emp s

let join_assoc (st:st0) =
  forall (s0 s1 s2:st.s).{:pattern st.join (s0, st.join (s1, s2))}
    st.join (s0, st.join (s1, s2)) ==
    st.join (st.join(s0, s1), s2)

let join_emp (st:st0) =
  forall (s0 s1:st.s).{:pattern st.join (s0, fst (st.split st.emp s1))}
    st.join (s0, fst (st.split st.emp s1)) == s0

let join_left_bias (st:st0) =
  forall (r:st.r) (s0 s1:st.s). {:pattern  st.interp r (st.join (s0, s1))}
    st.interp r s0 ==>
    st.interp r (st.join (s0, s1))

let split_assoc (st:st0) =
  forall (r0 r1:st.r) (s:st.s). {:pattern st.split (r0 `st.star` r1) s}
    st.interp (r0 `st.star` r1) s ==>
    (let s01, rest = st.split (r0 `st.star` r1) s in
     let s0, s1_emp = st.split r0 s01 in
     let s1, emp = st.split r1 s1_emp in

     let s0', s1_rest = st.split r0 s in
     let s1', rest' = st.split r1 s1_rest in
     s0 == s0' /\
     s1 == s1' /\
     rest == rest')

let split_comm (st:st0) =
  forall (r0 r1:st.r) (s:st.s). {:pattern st.interp (r0 `st.star` r1) s; st.split r0 s; st.split r1 s}
    st.interp (r0 `st.star` r1) s ==>
    (let s0, rest = st.split r0 s in
     let s1, rest = st.split r1 rest in

     let s1', rest = st.split r1 s in
     let s0', rest = st.split r0 rest in
     s0 == s0' /\
     s1 == s1')

let st_laws (st:st0) =
    (* standard laws about the equality relation *)
    symmetry st.equals /\
    transitive st.equals /\
    interp_extensionality st.equals st.interp /\
    (* standard laws for star forming a CM *)
    associative st.equals st.star /\
    commutative st.equals st.star /\
    is_unit st.emp st.equals st.star /\
    equals_ext st.equals st.star /\
    (* We're working in an affine interpretation of SL *)
    affine st /\
    emp_valid st /\
    (* lift refines a resource *)
    lift_star st /\
    (* split is AC, idempotent, with st.emp a unit *)
    split_assoc st /\
    split_comm st /\
    split_idem st /\
    split_empty st /\
    split_star st /\
    (* join is associative, left-biased, with emp a neutral element *)
    join_assoc st /\
    join_left_bias st /\ //not commutative!
    join_emp st /\
    (* join/split are partial inverses *)
    split_join st /\
    join_split st

let st = s:st0 { st_laws s }

let split_interp (st:st) (r:st.r) (s:rs r)
  : Lemma
    (ensures
        st.interp r (fst (st.split r s)))
    [SMTPat (st.split r s)]
  =
  assert (st.interp (r `st.star` st.emp) s)

(** [post a c] is a postcondition on [a]-typed result *)
let post (st:st) (a:Type) = a -> st.r

noeq
type action (st:st) (a:Type) = {
   pre: st.r;
   post: a -> st.r;
   sem: (s0:st.s{st.interp pre s0}) -> (a & st.s);
   action_ok: squash (
     (forall (frame:st.r) (s0:st.s).{:pattern st.interp (pre `st.star` frame) s0}
       st.interp (pre `st.star` frame) s0 ==>
       (let x, s1 = sem s0 in
        st.interp (post x `st.star` frame) s1)) /\
     (forall s. {:pattern st.interp pre s}
       st.interp pre s ==>
       (let s_pre, s_frame = st.split pre s in
        let x, s1 = sem s_pre in
        sem s == (x, st.join (s1, s_frame)))))
}

let wp_post (#st:st) (a:Type) (post:post st a) = x:a -> rs_prop (post x)
let wp_pre (#st:st) (pre:st.r) = rs_prop pre
let wp (#st:st) (pre:st.r) (a:Type) (post:post st a) = wp_post a post -> wp_pre pre

let return_wp (#st:st) (#a:Type) (x:a) (post: post st a)
  : wp (post x) a post
  = fun (k:wp_post a post) ->
      let pre : rs_prop' (post x) =
        fun s0 -> k x s0
      in
      pre

let bind_wp (#st:st)
            (#pre_a:st.r) (#a:Type) (#post_a:post st a)
            (#b:Type) (#post_b:post st b)
            (f:wp pre_a a post_a)
            (g: (x:a -> wp (post_a x) b post_b))
  : wp pre_a b post_b
  = fun k -> f (fun x -> g x k)

let wp_action (#st:st) #b (f:action st b)
  : wp f.pre b f.post
  = fun (k:wp_post b f.post) ->
     assert (f.pre `st.star` st.emp `st.equals` f.pre);
     let pre : rs_prop' f.pre =
        fun (s0:rs f.pre) ->
         let s0, s_frame = st.split f.pre s0 in
         let x, s0' = f.sem s0 in
         let s1 = st.join (s0', s_frame) in
         assert (st.interp (f.post x `st.star` st.emp) s1);
         k x s1
     in
     pre

let bind_action (#st:st) #a #b
                (f:action st b)
                (#post_g:post st a)
                (wp_g:(x:b -> wp (f.post x) a post_g))
   : wp f.pre a post_g
   = bind_wp (wp_action f) wp_g

let triv_post #st (a:Type) (p:post st a) : wp_post a p =
  let k (x:a) : rs_prop (p x) =
    let p : rs_prop' (p x) = fun s -> True in
    p
  in
  k

let as_requires (#st:st) (#aL:Type) (#preL:st.r) (#postL: post st aL) (wpL: wp preL aL postL)
  : rs_prop preL
  = wpL (triv_post aL postL)

let join_ext (#st:st) (l r : st.r) (sL sR rest: st.s)
    : Lemma
      (requires
        st.interp l sL /\
        st.interp r sR /\
        st.interp (l `st.star` r)
                  (st.join (sL, st.join(sR, rest))))
      (ensures
        st.interp (l `st.star` r)
                  (st.join (sL, sR)))
   = admit()

let wp_par_post (#st:st)
           #aL (#preL:st.r) (#postL: post st aL) (wpL: wp preL aL postL)
           #aR (#preR:st.r) (#postR: post st aR) (wpR: wp preR aR postR)
           (k:wp_post (aL & aR) (fun (xL, xR) -> postL xL `st.star` postR xR))
  : rs_prop st.emp
  = let app_k xL xR : rs_prop (postL xL `st.star` postR xR) = k (xL, xR) in
    let p : rs_prop' st.emp =
        fun (rest:rs st.emp) ->
          forall (xL:aL) (sL':rs (postL xL))
            (xR:aR) (sR':rs (postR xR)).
              {:pattern (st.interp (postL xL) sL'); (st.interp (postR xR) sR')}
            let s1 = st.join (sL', st.join (sR', rest)) in
            st.interp (postL xL) sL' /\
            st.interp (postR xR) sR' /\
            st.interp (postL xL `st.star` postR xR) s1 ==>
            app_k xL xR s1
    in
    let aux (rest:st.s)
      : Lemma
        (requires
          p rest)
        (ensures
          p (fst (st.split st.emp rest)))
        [SMTPat ()] //(st.split st.emp rest)]
      = let aux' xL sL' xR sR'
            : Lemma
              (requires
                st.interp (postL xL) sL' /\
                st.interp (postR xR) sR' /\
                st.interp (postL xL `st.star` postR xR)
                          (st.join (sL', st.join(sR', (fst (st.split st.emp rest))))))
              (ensures
                app_k xL xR (st.join (sL', st.join(sR', (fst (st.split st.emp rest))))))
              [SMTPat ()]
            = let s1' = (st.join (sL', st.join(sR', rest))) in
              let s1 = (st.join (sL', st.join(sR', (fst (st.split st.emp rest))))) in
              assert (s1 == st.join (sL', sR'));
              assert (s1' == st.join (s1, rest));
              assert (st.interp (postL xL `st.star` postR xR) s1');
              assert (app_k xL xR s1');
              assert (app_k xL xR (fst (st.split (postL xL `st.star` postR xR) s1')));
              assert (fst (st.split (postL xL `st.star` postR xR) s1') ==
                      fst (st.split (postL xL `st.star` postR xR) s1));
              assert (app_k xL xR s1)
        in
        ()
    in
    let aux (rest:st.s)
      : Lemma
        (requires
          p (fst (st.split st.emp rest)))
        (ensures
          p rest)
        [SMTPat ()] //st.split st.emp rest)]
      = let aux' xL sL' xR sR'
            : Lemma
              (requires
                st.interp (postL xL) sL' /\
                st.interp (postR xR) sR' /\
                st.interp (postL xL `st.star` postR xR)
                          (st.join (sL', st.join(sR', rest))))
              (ensures
                app_k xL xR (st.join (sL', st.join(sR', rest))))
              [SMTPat ()]
            = let s1 = (st.join (sL', st.join(sR', rest))) in
              let s1' = (st.join (sL', st.join(sR', (fst (st.split st.emp rest))))) in
              join_ext (postL xL) (postR xR) sL' sR' rest;
              assert (st.interp (postL xL `st.star` postR xR) (st.join(sL', sR')));
              assert (st.interp (postL xL `st.star` postR xR) s1');
              assert (app_k xL xR s1');
              assert (app_k xL xR (fst (st.split (postL xL `st.star` postR xR) s1')));
              assert (fst (st.split (postL xL `st.star` postR xR) s1') ==
                      fst (st.split (postL xL `st.star` postR xR) s1));
              assert (app_k xL xR s1)
        in
        ()
    in
    assert (forall rest. p rest <==> p (fst (st.split st.emp rest)));
    p


let rs_prop_emp_any (#st:st) (k:rs_prop st.emp) (s0 s1:st.s)
  : Lemma (k s0 ==> k s1)
  = ()

let wp_par (#st:st)
           #aL (#preL:st.r) (#postL: post st aL) (wpL: wp preL aL postL)
           #aR (#preR:st.r) (#postR: post st aR) (wpR: wp preR aR postR)
   : wp (preL `st.star` preR)
        (aL & aR)
        (fun (xL, xR) -> postL xL `st.star` postR xR)
   = fun (k:wp_post (aL & aR) (fun (xL, xR) -> postL xL `st.star` postR xR)) ->
       let pre : rs_prop' (preL `st.star` preR) =
         fun (s0:rs (preL `st.star` preR)) ->
           let sL = fst (st.split preL s0) in
           let rest = snd (st.split preL s0) in
           let sR = fst (st.split preR rest) in
           let rest = snd (st.split preR rest) in
           assert (st.interp preL sL);
           assert (st.interp preR sR);
           as_requires wpL sL /\
           as_requires wpR sR /\
           wp_par_post wpL wpR k rest
       in
       let aux0 (s:rs (preL `st.star` preR))
         : Lemma
           (ensures (pre s <==>
                     pre (fst (st.split (preL `st.star` preR) s))))
           [SMTPat ()]
         = let sL, rest = st.split preL s in
           let sR, rest = st.split preR rest in
           let s', _ = st.split (preL `st.star` preR) s in
           let sL', rest' = st.split preL s' in
           let sR', rest' = st.split preR rest' in
           assert (st.interp (preL `st.star` preR) s);
           assert (sL == sL');
           assert (sR == sR');
           rs_prop_emp_any (wp_par_post wpL wpR k) rest rest';
           rs_prop_emp_any (wp_par_post wpL wpR k) rest' rest
       in
       pre

let bind_par (#st:st)
           #aL (#preL:st.r) (#postL: post st aL) (wpL: wp preL aL postL)
           #aR (#preR:st.r) (#postR: post st aR) (wpR: wp preR aR postR)
           #a  #post (wp_k:(xL:aL -> xR:aR -> wp (postL xL `st.star` postR xR) a post))
  : wp (preL `st.star` preR)
       a
       post
  = bind_wp (wp_par wpL wpR) (fun (xL, xR) -> wp_k xL xR)


(** [m s c a pre post] :
 *  A free monad for divergence, state and parallel composition
 *  with generic actions. The main idea:
 *
 *  Every continuation may be divergent. As such, [m] is indexed by
 *  pre- and post-conditions so that we can do proofs
 *  intrinsically.
 *
 *  Universe-polymorphic in both the state and result type
 *
 *)
noeq
type m (st:st) : (a:Type u#a) -> pre:st.r -> post:post st a -> wp pre a post -> Type =
  | Ret : #a:_
        -> #post:post st a
        -> x:a
        -> m st a (post x) post (return_wp x post)

  | Act : #a:_
        -> #b:_
        -> f:action st b
        -> #post_g:post st a
        -> #wp_g:(x:b -> wp (f.post x) a post_g)
        -> g:(x:b -> Dv (m st a (f.post x) post_g (wp_g x)))
        -> m st a f.pre post_g (bind_action f wp_g)

  | Par : preL:_ -> aL:_ -> postL:_ -> wpL:wp preL aL postL -> mL: m st aL preL postL wpL ->
          preR:_ -> aR:_ -> postR:_ -> wpR:wp preR aR postR -> mR: m st aR preR postR wpR ->
          #a:_ -> post:_ -> wp_k:(xL:aL -> xR:aR -> wp (postL xL `st.star` postR xR) a post)
          -> k:(xL:aL -> xR:aR -> Dv (m st a (postL xL `st.star` postR xR) post (wp_k xL xR))) ->
          m st a (st.star preL preR) post (bind_par wpL wpR wp_k)


/// We assume a stream of booleans for the semantics given below
/// to resolve the nondeterminism of Par
assume
val bools : nat -> bool

/// The semantics comes is in two levels:
///
///   1. A single-step relation [step] which selects an atomic action to
///      execute in the tree of threads
///
///   2. A top-level driver [run] which repeatedly invokes [step]
///      until it returns with a result and final state.

noeq
type step_result (#st:st) a (q:post st a) (frame:st.r) (k:wp_post a q) =
  | Step: p:_ -> //precondition of the reduct
          wp:wp p a q ->
          m st a p q wp -> //the reduct
          state:rs (p `st.star` frame) {
             wp k state
          } ->
          //the next state, satisfying the precondition of the reduct
          nat -> //position in the stream of booleans (less important)
          step_result a q frame k

/// [step i f frame state]: Reduces a single step of [f], while framing
/// the assertion [frame]

// #reset-options
// #restart-solver
// #push-options "--max_fuel 0 --max_ifuel 4 --initial_ifuel 4 --z3rlimit_factor 4 --query_stats"

let step_act (#st:st) (i:nat) #pre #a #post
             (frame:st.r)
             (#wp:wp pre a post)
             (f:m st a pre post wp { Act? f })
             (k:wp_post a post)
             (state:st.s)
  : Div (step_result a post frame k)
        (requires
          st.interp (pre `st.star` frame) state /\
          st.interp pre state /\
          wp k state)
        (ensures fun _ -> True)
  =
    let Act act1 #post_g #wp_g g = f in
        //Evaluate the action and return the continuation as the reduct
    let b, state' = act1.sem state in
    assert (st.interp (act1.pre `st.star` frame) state);
    assert (st.interp (act1.post b `st.star` frame) state');
    assert (wp == bind_action act1 wp_g);
    assert (bind_action act1 wp_g k state);
    assert (st.interp (act1.post b) state');
    assert (wp_g b k state');
    Step (act1.post b) (wp_g b) (g b) state' i

#push-options "--query_stats"
#push-options "--max_ifuel 4 --initial_ifuel 4"
let step_par_ret (#st:st) (i:nat) #pre #a #post
                      (frame:st.r)
                      (#wp:wp pre a post)
                      (f:m st a pre post wp { Par? f /\ Ret? (Par?.mL f) /\ Ret? (Par?.mR f) })
                      (k:wp_post a post)
                      (state:st.s)
  : Div (step_result a post frame k)
        (requires
          st.interp (pre `st.star` frame) state /\
          st.interp pre state /\
          wp k state)
        (ensures fun _ -> True)
  =  let Par preL aL postL wpL (Ret xL)
          preR aR postR wpR (Ret xR)
          post wp_k kk = f in
      assert (wpL == return_wp xL postL);
      assert (wpR == return_wp xR postR);
      assert (wp == bind_par wpL wpR wp_k);
      assert (wp k state);
      let sL, rest = st.split preL state in
      let sR, rest = st.split preR rest in
      let s' = st.join (sL, st.join (sR, rest)) in
      assert (st.interp (postL xL) sL);
      assert (st.interp (postR xR) sR);
      assert (s' == state);
      assert (st.interp (postL xL `st.star` postR xR) s');
      assert (bind_par wpL wpR wp_k k state);
      assert (bind_par wpL wpR wp_k k state ==> wp_k xL xR k state)
          by (T.norm [delta_only [`%wp_par; `%bind_wp; `%bind_par; `%wp_par_post]; iota];
              T.dump "A");
      Step (postL xL `st.star` postR xR)
           (wp_k xL xR)
           (kk xL xR)
           state
           i

#push-options "--z3rlimit_factor 2 --z3cliopt 'smt.qi.eager_threshold=100'"
let elim_lift (#st:st) (r0 r1:st.r) (p:rs_prop r0) (s:st.s)
  : Lemma
    (requires
      st.interp (st.lift r0 p `st.star` r1) s)
    (ensures
      st.interp (r0 `st.star` r1) s /\
      st.interp r0 s /\
      st.interp r1 s /\
      p s)
   = ()

let elim_rs_prop (#st:st) (r:st.r) (p:rs_prop r) (s:st.s)
  : Lemma
    (requires
      st.interp r s /\
      p s)
    (ensures
//      st.interp r (fst (st.split r s)) /\
      p (fst (st.split r s)))
  = ()

#push-options "--z3rlimit_factor 8"
let rec step (#st:st) (i:nat) #pre #a #post
             (frame:st.r)
             (#wp:wp pre a post)
             (f:m st a pre post wp)
             (k:wp_post a post)
             (state:st.s)
  : Div (step_result a post frame k)
        (requires
          st.interp (pre `st.star` frame) state /\
          st.interp pre state /\
          wp k state)
        (ensures fun _ -> True)
  = match f with
    | Ret x ->
        //Nothing to do, just return
        Step (post x) wp (Ret x) state i

    | Act _ _  ->
      step_act i frame f k state

    | Par preL aL postL wpL (Ret _)
          preR aR postR wpR (Ret _)
          post wp_kont kont ->
      step_par_ret i frame f k state

    | Par preL aL postL wpL mL
          preR aR postR wpR mR
          post wp_kont kont ->

      assert (wp == bind_par wpL wpR wp_kont);
      assert (st.interp (preL `st.star` (preR `st.star` frame)) state);
      assert (st.interp (preL `st.star` preR) state);

      let sL, rest0 = st.split preL state in
      let sR, rest = st.split preR rest0 in
      assert (as_requires wpL sL);
      assert (as_requires wpR sR);

      assert (as_requires wpL state);
      assert (as_requires wpR rest0);
      assert (fst (st.split preR rest0) == fst (st.split preR state));
      assert (as_requires wpR state);

      if bools i
      then begin
        calc (st.equals) {
          preL `st.star` (preR `st.star` frame);
          (st.equals) { }
          (preL `st.star` preR) `st.star` frame;
          (st.equals) { }
          (preR `st.star` preL) `st.star` frame;
          (st.equals) { }
          preR `st.star` (preL `st.star` frame);
        };
        assert (st.interp ((st.lift preR (as_requires wpR)) `st.star` (preL `st.star` frame)) state);
        calc (st.equals) {
          (st.lift preR (as_requires wpR)) `st.star` (preL `st.star` frame);
          (st.equals) { }
          (st.lift preR (as_requires wpR) `st.star` preL) `st.star` frame;
          (st.equals) { }
          (preL `st.star` st.lift preR (as_requires wpR)) `st.star` frame;
          (st.equals) { }
          preL `st.star` ((st.lift preR (as_requires wpR)) `st.star` frame);
        };
        assert (st.interp (preL `st.star` ((st.lift preR (as_requires wpR)) `st.star` frame)) state);
        let Step preL' wpL' mL' state' j =
            //Notice that, inductively, we instantiate the frame extending
            //it to include the precondition of the other side of the par
            step (i + 1)
                 ((st.lift preR (as_requires wpR)) `st.star` frame)
                 mL
                 (triv_post aL postL)
                 state
        in
        assert (as_requires wpL' state');
        assert (as_requires wpR state');
        let sL', rest0' = st.split preL' state' in
        let sR', rest' = st.split preR rest0' in
        assert (bind_par wpL wpR wp_kont k state ==>
               bind_par wpL' wpR wp_kont k state')
               by  (T.norm [delta_only [`%wp_par; `%bind_wp; `%bind_par; `%wp_par_post]];
               T.dump "A";
               T.smt());
        Step (preL' `st.star` preR)
             (bind_par wpL' wpR wp_kont)
             (Par preL' aL postL wpL' mL'
                  preR  aR postR wpR  mR
                  post wp_kont kont)
             state'
             j
      end else begin
        assert (st.interp ((st.lift preL (as_requires wpL)) `st.star` (preR `st.star` frame)) state);
        calc (st.equals) {
          (st.lift preL (as_requires wpL)) `st.star` (preR `st.star` frame);
          (st.equals) { }
          (st.lift preL (as_requires wpL) `st.star` preR) `st.star` frame;
          (st.equals) { }
          (preR `st.star` st.lift preL (as_requires wpL)) `st.star` frame;
          (st.equals) { }
          preR `st.star` ((st.lift preL (as_requires wpL)) `st.star` frame);
        };
        assert (st.interp (preR `st.star` ((st.lift preL (as_requires wpL)) `st.star` frame)) state);
        let Step preR' wpR' mR' state' j =
            //Notice that, inductively, we instantiate the frame extending
            //it to include the precondition of the other side of the par
            step (i + 1)
                 ((st.lift preL (as_requires wpL)) `st.star` frame)
                 mR
                 (triv_post aR postR)
                 state
        in
        assert (as_requires wpL state');
        assert (as_requires wpR' state');
        let sL', rest0' = st.split preL state' in
        let sR', rest' = st.split preR' rest0' in
        assert (bind_par wpL wpR wp_kont k state ==>
                bind_par wpL wpR' wp_kont k state')
               by  (T.norm [delta_only [`%wp_par; `%bind_wp; `%bind_par; `%wp_par_post]];
               T.dump "A";
               T.smt());
        let p' = (preL `st.star` preR') in
        let wp' = bind_par wpL wpR' wp_kont in
        calc (st.equals) {
          preR' `st.star` (preL `st.star` frame);
          (st.equals) { }
          (preR' `st.star` preL) `st.star` frame;
          (st.equals) { }
          (preL `st.star` preR') `st.star` frame;
        };
        Step p'
             wp'
             (Par preL aL postL wpL mL
                  preR'  aR postR wpR' mR'
                  post wp_kont kont)
             state'
             j
      end


(**
//  * [run i f state]: Top-level driver that repeatedly invokes [step]
//  *
//  * The type of [run] is the main theorem. It states that it is sound
//  * to interpret the indices of `m` as a Hoare triple in a
//  * partial-correctness semantics
//  *
//  *)
let rec run (#st:st) (i:nat)
            #pre #a #post (#wp:wp pre a post)
            (f:m st a pre post wp) (state:st.s)
            (k:wp_post a post)
  : Div (a & st.s)
    (requires
      st.interp pre state /\
      wp k state)
    (ensures fun (x, state') ->
      st.interp (post x) state' /\
      k x state')
  = match f with
    | Ret x -> x, state
    | _ ->
      let Step pre' wp' f' state' j = step i st.emp f k state in
      run j f' state' k


////////////////////////////////////////////////////////////////////////////////
//The rest of this module shows how these semantics can be packaged up as an
//effect in F*
////////////////////////////////////////////////////////////////////////////////

(** [eff a pre post] : The representation-type for a layered effect
//  *
//  *   - Note, we'll probably have to add a thunk to make it work with
//  *     the current implementation but that's a detail
//  *)
let eff (#st:st) a
        (expects:st.r)
        (provides: a -> st.r)
        (wp:wp expects a provides)
  = m st a expects provides wp

/// eff is a monad: we give a return and bind for it, though we don't
/// prove the monad laws


(** [return]: easy, just use Ret *)
let return (#st:st) #a (x:a) (post:a -> st.r)
  : eff a (post x) post (return_wp x post)
  = Ret x

let eta2 #a #b #c (f:a -> b -> c) : Lemma ((fun x y -> f x y) == f) = ()

(**
//  * [bind]: sequential composition works by pushing `g` into the continuation
//  * at each node, finally applying it at the terminal `Ret`
//  *)
let rec bind (#st:st) #a #b (#p:st.r) (#q:a -> st.r) (#r:b -> st.r)
             (#wp_f: wp p a q) (f:eff a p q wp_f)
             (#wp_g: (x:a -> wp (q x) b r)) (g: (x:a -> eff b (q x) r (wp_g x)))
  : Dv (eff b p r (bind_wp wp_f wp_g))
  = match f with
    | Ret x ->
      assert (p == q x);
      assert (wp_f == return_wp x q);
      assert (eq2 #(wp_post b r -> rs (q x) -> prop) (bind_wp (return_wp x q) wp_g) (wp_g x))
        by (T.norm [delta_only [`%bind_wp; `%return_wp]];
            T.dump "A";
            T.mapply (`eta2));
      g x

    | Act #_ #a' f #post_h #wp_h h ->
      assert (wp_f == bind_action f wp_h);
      let g' (x:_) : Dv (eff b (f.post x) r (bind_wp (wp_h x) wp_g))
        = bind #st #a' #b (h x) g
      in
      let res : eff b p r (bind_action f (fun x -> bind_wp (wp_h x) wp_g)) = Act f g' in
      calc (==) {
        bind_action f (fun x -> bind_wp (wp_h x) wp_g);
          == {}
        bind_wp (wp_action f) (fun x -> bind_wp (wp_h x) wp_g);
          == { admit() (* assoc *) }
        bind_wp (bind_wp (wp_action f) (fun x -> wp_h x)) wp_g;
          == { }
        bind_wp wp_f wp_g;
      };
      res

    | Par preL aL postL wpL mL
          preR aR postR wpR mR
          post wp_kont kont ->
      let kont x0 x1 : Dv (eff b (postL x0 `st.star` postR x1) r (bind_wp (wp_kont x0 x1) wp_g)) = bind (kont x0 x1) g in
      let res : m st b (st.star preL preR) r (bind_par wpL wpR (fun x0 x1 -> (bind_wp (wp_kont x0 x1) wp_g))) =
          Par preL aL postL wpL mL
                    preR aR postR wpR mR
                    r (fun x0 x1 -> (bind_wp (wp_kont x0 x1) wp_g)) kont in
      calc (==) {
        (bind_par wpL wpR (fun x0 x1 -> (bind_wp (wp_kont x0 x1) wp_g)));
        == { _ by (T.dump "A"; T.norm [delta_only [`%bind_par]]; T.dump "B"; T.trefl()) }
        bind_wp (wp_par wpL wpR) (fun (x0, x1) -> (bind_wp (wp_kont x0 x1) wp_g));
        == { admit () (* assoc *) }
        bind_wp (bind_wp (wp_par wpL wpR) (fun (x0, x1) -> wp_kont x0 x1)) wp_g;
        == {}
        (bind_wp (bind_par wpL wpR wp_kont) wp_g);
      };
      res


// // // // (**
// // // //  * [par]: Parallel composition
// // // //  * Works by just using the `Par` node and `Ret` as its continuation
// // // //  **)
// // // // let par #s (#c:comm_monoid s)
// // // //         #a0 #p0 #q0 (m0:eff a0 p0 q0)
// // // //         #a1 #p1 #q1 (m1:eff a1 p1 q1)
// // // //  : eff (a0 & a1) (p0 `c.star` p1) (fun (x0, x1) -> q0 x0 `c.star` q1 x1)
// // // //  = Par p0 q0 m0
// // // //        p1 q1 m1
// // // //        #_ #(fun (x0, x1) -> c.star (q0 x0) (q1 x1)) (fun x0 x1 -> Ret (x0, x1))


// // // // /// Now for an instantiation of the state with a heap
// // // // /// just to demonstrate how that would go

// // // // /// Heaps are usually in a universe higher than the values they store
// // // // /// Pick it in universe 1
// // // // assume val heap : Type u#1

// // // // /// Assume some monoid of heap assertions
// // // // assume val hm : comm_monoid heap

// // // // /// For this demo, we'll also assume that this assertions are affine
// // // // ///  i.e., it's ok to forget some properties of the heap
// // // // assume val hm_affine (r0 r1:hm.r) (h:heap)
// // // //   : Lemma (hm.interp (r0 `hm.star` r1) h ==>
// // // //            hm.interp r0 h)

// // // // /// Here's a ref type
// // // // assume val ref : Type u#0 -> Type u#0

// // // // /// And two atomic heap assertions
// // // // assume val ptr_live (r:ref 'a) : hm.r
// // // // assume val pts_to (r:ref 'a) (x:'a) : hm.r

// // // // /// sel: Selected a reference from a heap, when that ref is live
// // // // assume val sel (x:ref 'a) (h:heap{hm.interp (ptr_live x) h})
// // // //   : Tot 'a
// // // // /// this tells us that sel is frameable
// // // // assume val sel_ok (x:ref 'a) (h:heap) (frame:hm.r)
// // // //   : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
// // // //            (hm_affine (ptr_live x) frame h;
// // // //             let v = sel x h in
// // // //             hm.interp (pts_to x v `hm.star` frame) h))


// // // // /// upd: updates a heap at a given reference, when the heap contains it
// // // // assume val upd (x:ref 'a) (v:'a) (h:heap{hm.interp (ptr_live x) h})
// // // //   : Tot heap
// // // // /// and upd is frameable too
// // // // assume val upd_ok (x:ref 'a) (v:'a) (h:heap) (frame:hm.r)
// // // //   : Lemma (hm.interp (ptr_live x `hm.star` frame) h ==>
// // // //            (hm_affine (ptr_live x) frame h;
// // // //             let h' = upd x v h in
// // // //             hm.interp (pts_to x v `hm.star` frame) h'))

// // // // /// Here's a sample action for dereference
// // // // let (!) (x:ref 'a)
// // // //   : eff 'a (ptr_live x) (fun v -> pts_to x v)
// // // //   = let act : action hm 'a =
// // // //     {
// // // //       pre = ptr_live x;
// // // //       post = pts_to x;
// // // //       sem = (fun frame h0 ->
// // // //         hm_affine (ptr_live x) frame h0;
// // // //         sel_ok x h0 frame;
// // // //         (| sel x h0, h0 |))
// // // //     } in
// // // //     Act act Ret

// // // // /// And a sample action for assignment
// // // // let (:=) (x:ref 'a) (v:'a)
// // // //   : eff unit (ptr_live x) (fun _ -> pts_to x v)
// // // //   = let act : action hm unit =
// // // //     {
// // // //       pre = ptr_live x;
// // // //       post = (fun _ -> pts_to x v);
// // // //       sem = (fun frame h0 ->
// // // //         hm_affine (ptr_live x) frame h0;
// // // //         upd_ok x v h0 frame;
// // // //         (| (), upd x v h0 |))
// // // //     } in
// // // //     Act act Ret
