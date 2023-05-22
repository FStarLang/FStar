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

module CSL.Semantics

module P = FStar.Preorder

open FStar.Tactics

open FStar.NMST


(*
 * This module provides a semantic model for a combined effect of
 * divergence, state, and parallel composition of atomic actions.
 *
 * It is built over a monotonic state effect -- so that we can give
 * lock semantics using monotonicity
 *
 * Using the semantics, we derive a CSL in a partial correctness setting.
*)


#push-options "--fuel  0 --ifuel 2 --z3rlimit 20 --print_implicits --print_universes \
   --using_facts_from 'Prims FStar.Pervasives FStar.Preorder MST NMST CSL.Semantics'"

(**** Begin state defn ****)


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
  forall x y z.
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
  mem:Type u#2;

  evolves:P.preorder mem;
  hprop:Type u#2;
  invariant: mem -> hprop;

  interp: hprop -> mem -> prop;

  emp:hprop;
  star: hprop -> hprop -> hprop;

  equals: hprop -> hprop -> prop;
}


////////////////////////////////////////////////////////////////////////////////

let interp_extensionality #r #s (equals:r -> r -> prop) (f:r -> s -> prop) =
  forall x y h. {:pattern equals x y; f x h} equals x y /\ f x h ==> f y h

let affine (st:st0) =
  forall r0 r1 s. {:pattern (st.interp (r0 `st.star` r1) s) }
    st.interp (r0 `st.star` r1) s ==> st.interp r0 s

////////////////////////////////////////////////////////////////////////////////

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
  affine st

let st = s:st0 { st_laws s }

(**** End state defn ****)


(**** Begin expects, provides defns ****)


/// expects (the heap assertion expected by a computation) is simply an st.hprop
///
/// provides, or the post heap assertion, is a st.hprop on [a]-typed result

type post_t (st:st) (a:Type) = a -> st.hprop

(**** End expects, provides defns ****)


effect Mst (a:Type) (#st:st) (req:st.mem -> Type0) (ens:st.mem -> a -> st.mem -> Type0) =
  NMSTATE a st.mem st.evolves req ens


(**** Begin interface of actions ****)


/// Actions are essentially state transformers that preserve frames

let preserves_frame (#st:st) (pre post:st.hprop) (m0 m1:st.mem) =
  forall (frame:st.hprop).
    st.interp ((pre `st.star` frame) `st.star` (st.invariant m0)) m0 ==>
    st.interp ((post `st.star` frame) `st.star` (st.invariant m1)) m1

let action_t
      (#st:st)
      (#a:Type)
      (pre:st.hprop)
      (post:post_t st a)
= unit ->
  Mst a
  (requires fun m0 -> st.interp (pre `st.star` st.invariant m0) m0)
  (ensures fun m0 x m1 ->
    st.interp ((post x) `st.star` st.invariant m1) m1 /\
    preserves_frame pre (post x) m0 m1)

(**** End interface of actions ****)


(**** Begin definition of the computation AST ****)

let weaker_pre (#st:st) (pre:st.hprop) (next_pre:st.hprop) =
  forall (h:st.mem) (frame:st.hprop).
    st.interp (pre `st.star` frame) h ==>
    st.interp (next_pre `st.star` frame) h

let stronger_post (#st:st) (#a:Type u#a) (post next_post:post_t st a) =
  forall (x:a) (h:st.mem) (frame:st.hprop).
    st.interp (next_post x `st.star` frame) h ==>
    st.interp (post x `st.star` frame) h

let weakening_ok (#st:st) (#a:Type u#a) (pre:st.hprop) (post:post_t st a)
  (wpre:st.hprop) (wpost:post_t st a)
= weaker_pre wpre pre /\ stronger_post wpost post


noeq
type m (st:st) :
      a:Type u#a ->
      pre:st.hprop ->
      post:post_t st a -> Type
    =
  | Ret:
    #a:Type u#a ->
    post:post_t st a ->
    x:a ->
    m st a (post x) post

  | Bind:
    #a:Type u#a ->
    #pre:st.hprop ->
    #post_a:post_t st a ->
    #b:Type u#a ->
    #post_b:post_t st b ->
    f:m st a pre post_a ->
    g:(x:a -> Dv (m st b (post_a x) post_b)) ->
    m st b pre post_b

  | Act:
    #a:Type u#a ->
    #pre:st.hprop ->
    #post:post_t st a ->
    f:action_t #st #a pre post ->
    m st a pre post

  | Frame:
    #a:Type ->
    #pre:st.hprop ->
    #post:post_t st a ->
    f:m st a pre post ->
    frame:st.hprop ->
    m st a (pre `st.star` frame) (fun x -> post x `st.star` frame)

  | Par:
    #aL:Type u#a ->
    #preL:st.hprop ->
    #postL:post_t st aL ->
    mL:m st aL preL postL ->
    #aR:Type u#a ->
    #preR:st.hprop ->
    #postR:post_t st aR ->
    mR:m st aR preR postR ->
    m st (aL & aR) (preL `st.star` preR) (fun (xL, xR) -> postL xL `st.star` postR xR)

  | Weaken:
    #a:Type u#a ->
    #pre:st.hprop ->
    #post:post_t st a ->
    wpre:st.hprop ->
    wpost:post_t st a ->
    _:squash (weakening_ok pre post wpre wpost) ->
    m st a pre post ->
    m st a wpre wpost

(**** End definition of the computation AST ****)


(**** Stepping relation ****)

/// All steps preserve frames

noeq
type step_result (st:st) (a:Type u#a) =
  | Step:
    #next_pre:st.hprop ->
    #next_post:post_t st a ->
    m st a next_pre next_post ->
    step_result st a


(**** Type of the single-step interpreter ****)


/// Interpreter is setup as an NMST function from computation trees to computation trees
///
/// As the computation evolves, the post becomes stronger


unfold
let step_req (#st:st) (#a:Type u#a) (#pre:st.hprop) (#post:post_t st a) (f:m st a pre post)
: st.mem -> Type0
= fun m0 -> st.interp (pre `st.star` st.invariant m0) m0

unfold
let step_ens (#st:st) (#a:Type u#a) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post)
: st.mem -> step_result st a -> st.mem -> Type0
= fun m0 r m1 ->
  let Step #_ #_ #next_pre #next_post  _ = r in
  st.interp (next_pre `st.star` st.invariant m1) m1 /\
  stronger_post post next_post /\
  preserves_frame pre next_pre m0 m1


/// The type of the stepping function

type step_t =
  #st:st ->
  #a:Type u#a ->
  #pre:st.hprop ->
  #post:post_t st a ->
  f:m st a pre post ->
  Mst (step_result st a) (step_req f) (step_ens f)


(**** Auxiliary lemmas ****)

/// Some AC lemmas on `st.star`

let apply_assoc (#st:st) (p q r:st.hprop)
: Lemma (st.equals (p `st.star` (q `st.star` r)) ((p `st.star` q) `st.star` r))
= ()

let equals_ext_right (#st:st) (p q r:st.hprop)
: Lemma
  (requires q `st.equals` r)
  (ensures (p `st.star` q) `st.equals` (p `st.star` r))
= calc (st.equals) {
    p `st.star` q;
       (st.equals) { }
    q `st.star` p;
       (st.equals) { }
    r `st.star` p;
       (st.equals) { }
    p `st.star` r;
  }

let commute_star_right (#st:st) (p q r:st.hprop)
: Lemma ((p `st.star` (q `st.star` r)) `st.equals` (p `st.star` (r `st.star` q)))
= calc (st.equals) {
    p `st.star` (q `st.star` r);
       (st.equals) { equals_ext_right p (q `st.star` r) (r `st.star` q) }
    p `st.star` (r `st.star` q);
  }

let assoc_star_right (#st:st) (p q r s:st.hprop)
: Lemma
  ((p `st.star` ((q `st.star` r) `st.star` s)) `st.equals`
   (p `st.star` (q `st.star` (r `st.star` s))))
= calc (st.equals) {
    p `st.star` ((q `st.star` r) `st.star` s);
       (st.equals) { equals_ext_right p ((q `st.star` r) `st.star` s)
                                        (q `st.star` (r `st.star` s)) }
    p `st.star` (q `st.star` (r `st.star` s));
  }

let commute_assoc_star_right (#st:st) (p q r s:st.hprop)
: Lemma
  ((p `st.star` ((q `st.star` r) `st.star` s)) `st.equals`
   (p `st.star` (r `st.star` (q `st.star` s))))
= calc (st.equals) {
    p `st.star` ((q `st.star` r) `st.star` s);
       (st.equals) { equals_ext_right p
                       ((q `st.star` r) `st.star` s)
                       ((r `st.star` q) `st.star` s) }
    p `st.star` ((r `st.star` q) `st.star` s);
       (st.equals) { assoc_star_right p r q s }
    p `st.star` (r `st.star` (q `st.star` s));
  }


/// Apply extensionality manually, control proofs

let apply_interp_ext (#st:st) (p q:st.hprop) (m:st.mem)
: Lemma
  (requires (st.interp p m /\ p `st.equals` q))
  (ensures st.interp q m)
= ()


/// Lemmas about preserves_frame

let preserves_frame_trans (#st:st) (hp1 hp2 hp3:st.hprop) (m1 m2 m3:st.mem)
: Lemma
  (requires preserves_frame hp1 hp2 m1 m2 /\ preserves_frame hp2 hp3 m2 m3)
  (ensures preserves_frame hp1 hp3 m1 m3)
= ()

#push-options "--warn_error -271"
let preserves_frame_stronger_post (#st:st) (#a:Type)
  (pre:st.hprop) (post post_s:post_t st a) (x:a)
  (m1 m2:st.mem)
: Lemma
  (requires preserves_frame pre (post_s x) m1 m2 /\ stronger_post post post_s)
  (ensures preserves_frame pre (post x) m1 m2)
= let aux (frame:st.hprop)
    : Lemma
      (requires st.interp (st.invariant m1 `st.star` (pre `st.star` frame)) m1)
      (ensures st.interp (st.invariant m2 `st.star` (post x `st.star` frame)) m2)
      [SMTPat ()]
    = assert (st.interp (st.invariant m2 `st.star` (post_s x `st.star` frame)) m2);
      calc (st.equals) {
        st.invariant m2 `st.star` (post_s x `st.star` frame);
           (st.equals) { }
        (st.invariant m2 `st.star` post_s x) `st.star` frame;
           (st.equals) { }
        (post_s x `st.star` st.invariant m2) `st.star` frame;
           (st.equals) { }
       post_s x `st.star` (st.invariant m2 `st.star` frame);
      };
      assert (st.interp (post_s x `st.star` (st.invariant m2 `st.star` frame)) m2);
      assert (st.interp (post x `st.star` (st.invariant m2 `st.star` frame)) m2);
      calc (st.equals) {
        post x `st.star` (st.invariant m2 `st.star` frame);
           (st.equals) { }
        (post x `st.star` st.invariant m2) `st.star` frame;
           (st.equals) { }
        (st.invariant m2 `st.star` post x) `st.star` frame;
           (st.equals) { apply_assoc (st.invariant m2) (post x) frame }
        st.invariant m2 `st.star` (post x `st.star` frame);
        };
      assert (st.interp (st.invariant m2 `st.star` (post x `st.star` frame)) m2)
  in
  ()
#pop-options

#push-options "--z3rlimit 40 --warn_error -271"
let preserves_frame_star (#st:st) (pre post:st.hprop) (m0 m1:st.mem) (frame:st.hprop)
: Lemma
  (requires preserves_frame pre post m0 m1)
  (ensures preserves_frame (pre `st.star` frame) (post `st.star` frame) m0 m1)
= let aux (frame':st.hprop)
    : Lemma
      (requires
        st.interp (st.invariant m0 `st.star` ((pre `st.star` frame) `st.star` frame')) m0)
      (ensures
        st.interp (st.invariant m1 `st.star` ((post `st.star` frame) `st.star` frame')) m1)
      [SMTPat ()]
    = assoc_star_right (st.invariant m0) pre frame frame';
      apply_interp_ext
        (st.invariant m0 `st.star` ((pre `st.star` frame) `st.star` frame'))
        (st.invariant m0 `st.star` (pre `st.star` (frame `st.star` frame')))
        m0;
      assoc_star_right (st.invariant m1) post frame frame';
      apply_interp_ext
        (st.invariant m1 `st.star` (post `st.star` (frame `st.star` frame')))
        (st.invariant m1 `st.star` ((post `st.star` frame) `st.star` frame'))
        m1
  in
  ()

let preserves_frame_star_left (#st:st) (pre post:st.hprop) (m0 m1:st.mem) (frame:st.hprop)
: Lemma
  (requires preserves_frame pre post m0 m1)
  (ensures preserves_frame (frame `st.star` pre) (frame `st.star` post) m0 m1)
= let aux (frame':st.hprop)
    : Lemma
      (requires
        st.interp (st.invariant m0 `st.star` ((frame `st.star` pre) `st.star` frame')) m0)
      (ensures
        st.interp (st.invariant m1 `st.star` ((frame `st.star` post) `st.star` frame')) m1)
      [SMTPat ()]
    = commute_assoc_star_right (st.invariant m0) frame pre frame';
      apply_interp_ext
        (st.invariant m0 `st.star` ((frame `st.star` pre) `st.star` frame'))
        (st.invariant m0 `st.star` (pre `st.star` (frame `st.star` frame')))
        m0;
      commute_assoc_star_right (st.invariant m1) frame post frame';
      apply_interp_ext
        (st.invariant m1 `st.star` (post `st.star` (frame `st.star` frame')))
        (st.invariant m1 `st.star` ((frame `st.star` post) `st.star` frame'))
        m1
  in
  ()
#pop-options


/// Lemmas for proving that in the par rules preconditions get weaker
///   and postconditions get stronger

let par_weaker_lpre_and_stronger_lpost_r (#st:st)
  (preL:st.hprop) (#aL:Type) (postL:post_t st aL)
  (preR:st.hprop) (#aR:Type) (postR:post_t st aR)
  (next_preR:st.hprop) (next_postR:post_t st aR)
  (state next_state:st.mem)
: Lemma
  (requires
    preserves_frame preR next_preR state next_state /\
    st.interp ((preL `st.star` preR) `st.star` st.invariant state) state)
  (ensures
    st.interp ((preL `st.star` next_preR) `st.star` st.invariant next_state) next_state)
= commute_star_right (st.invariant state) preL preR;
  apply_interp_ext
    (st.invariant state `st.star` (preL `st.star` preR))
    (st.invariant state `st.star` (preR `st.star` preL))
    state;
  commute_star_right (st.invariant next_state) next_preR preL;
  apply_interp_ext
    (st.invariant next_state `st.star` (next_preR `st.star` preL))
    (st.invariant next_state `st.star` (preL `st.star` next_preR))
    next_state

#push-options "--warn_error -271"
let stronger_post_par_r (#st:st) (#aL #aR:Type u#a)
  (postL:post_t st aL) (postR:post_t st aR) (next_postR:post_t st aR)
: Lemma
  (requires stronger_post postR next_postR)
  (ensures
    forall xL xR frame h.
      st.interp ((postL xL `st.star` next_postR xR) `st.star` frame) h ==>
      st.interp ((postL xL `st.star` postR xR) `st.star` frame) h)
= let aux xL xR frame h
    : Lemma
      (requires st.interp ((postL xL `st.star` next_postR xR) `st.star` frame) h)
      (ensures st.interp ((postL xL `st.star` postR xR) `st.star` frame) h)
      [SMTPat ()]
    = calc (st.equals) {
        (postL xL `st.star` next_postR xR) `st.star` frame;
           (st.equals) { }
        (next_postR xR `st.star` postL xL) `st.star` frame;
           (st.equals) { }
        next_postR xR `st.star` (postL xL `st.star` frame);
      };
      assert (st.interp (next_postR xR `st.star` (postL xL `st.star` frame)) h);
      assert (st.interp (postR xR `st.star` (postL xL `st.star` frame)) h);
      calc (st.equals) {
        postR xR `st.star` (postL xL `st.star` frame);
           (st.equals) { }
        (postR xR `st.star` postL xL) `st.star` frame;
           (st.equals) { }
        (postL xL `st.star` postR xR) `st.star` frame;
      }
  in
  ()
#pop-options


(**** Begin stepping functions ****)

let step_ret (#st:st) (#a:Type u#a) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post{Ret? f})
: Mst (step_result st a) (step_req f) (step_ens f)
= let Ret p x = f in
  Step f

let step_act (#st:st) (#a:Type u#a) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post {Act? f})
: Mst (step_result st a) (step_req f) (step_ens f)
= let Act f = f in
  let x = f () in
  Step (Ret post x)

module M = FStar.MST

let step_bind_ret_aux (#st:st) (#a:Type) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post{Bind? f /\ Ret? (Bind?.f f)})
: M.MSTATE (step_result st a) st.mem st.evolves (step_req f) (step_ens f)
= M.MSTATE?.reflect (fun m0 ->
    match f with
    | Bind (Ret p x) g -> Step (g x), m0)

let step_bind_ret (#st:st) (#a:Type) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post{Bind? f /\ Ret? (Bind?.f f)})
: Mst (step_result st a) (step_req f) (step_ens f)
= NMSTATE?.reflect (fun (_, n) -> step_bind_ret_aux f, n)

let step_bind (#st:st) (#a:Type) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post{Bind? f})
  (step:step_t)
: Mst (step_result st a) (step_req f) (step_ens f)
= match f with
  | Bind (Ret _ _) _ -> step_bind_ret f

  | Bind #_ #_ #_ #_ #_ #post_b f g ->
    let Step #_ #_ #next_pre #next_post f = step f in

    Step #_ #_ #next_pre #post_b
      (Bind f (fun x -> Weaken (next_post x) _ () (g x)))

let step_frame_ret (#st:st) (#a:Type) (#pre:st.hprop) (#p:post_t st a)
  (f:m st a pre p{Frame? f /\ Ret? (Frame?.f f)})
: Mst (step_result st a) (step_req f) (step_ens f)
= let Frame (Ret p x) frame = f in
  Step (Ret (fun x -> p x `st.star` frame) x)

let step_frame (#st:st) (#a:Type) (#pre:st.hprop) (#p:post_t st a)
  (f:m st a pre p{Frame? f})
  (step:step_t)
: Mst (step_result st a) (step_req f) (step_ens f)
= match f with
  | Frame (Ret _ _) _ -> step_frame_ret f

  | Frame #_ #_ #f_pre #_ f frame ->
    let m0 = get () in

    let Step #_ #_ #next_fpre #next_fpost f = step f in

    let m1 = get () in

    preserves_frame_star f_pre next_fpre m0 m1 frame;

    Step (Frame f frame)

let step_par_ret_aux (#st:st) (#a:Type) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post{Par? f /\ Ret? (Par?.mL f) /\ Ret? (Par?.mR f)})
: M.MSTATE (step_result st a) st.mem st.evolves (step_req f) (step_ens f)
= M.MSTATE?.reflect (fun m0 ->
    let Par (Ret pL xL) (Ret pR xR) = f in
    Step (Ret (fun (xL, xR) -> pL xL `st.star` pR xR) (xL, xR)), m0)

let step_par_ret (#st:st) (#a:Type) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post{Par? f /\ Ret? (Par?.mL f) /\ Ret? (Par?.mR f)})
: Mst (step_result st a) (step_req f) (step_ens f)
= NMSTATE?.reflect (fun (_, n) -> step_par_ret_aux f, n)

let step_par (#st:st) (#a:Type) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post{Par? f}) (step:step_t)
: Mst (step_result st a) (step_req f) (step_ens f)
= match f with
  | Par (Ret _ _) (Ret _ _) -> step_par_ret f

  | Par #_ #aL #preL #postL mL #aR #preR #postR mR ->
    let b = sample () in

    if b then begin
      let m0 = get () in

      let Step #_ #_ #next_preL #next_postL mL = step mL in

      let m1 = get () in

      preserves_frame_star preL next_preL m0 m1 preR;

      let next_post = (fun (xL, xR) -> next_postL xL `st.star` postR xR) in

      assert (stronger_post post next_post) by (norm [delta_only [`%stronger_post]]);

      Step (Par mL mR)
    end
    else begin
      let m0 = get () in

      let Step #_ #_ #next_preR #next_postR mR = step mR in

      let m1 = get () in

      preserves_frame_star_left preR next_preR m0 m1 preL;
      par_weaker_lpre_and_stronger_lpost_r preL postL preR postR next_preR next_postR  m0 m1;

      let next_post = (fun (xL, xR) -> postL xL `st.star` next_postR xR) in

      stronger_post_par_r postL postR next_postR;

      Step (Par mL mR)
    end

let step_weaken (#st:st) (#a:Type u#a) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post{Weaken? f})
: Mst (step_result st a) (step_req f) (step_ens f)
= let Weaken _ _ _ f = f in
  Step f


/// Step function

let rec step (#st:st) (#a:Type u#a) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post)
: Mst (step_result st a) (step_req f) (step_ens f)
= match f with
  | Ret _ _ -> step_ret f
  | Bind _ _ -> step_bind f step
  | Act _ -> step_act f
  | Frame _ _ -> step_frame f step
  | Par _ _ -> step_par f step
  | Weaken _ _ _ _ -> step_weaken f

let rec run (#st:st) (#a:Type u#a) (#pre:st.hprop) (#post:post_t st a)
  (f:m st a pre post)
: Mst a
  (requires fun m0 -> st.interp (pre `st.star` st.invariant m0) m0)
  (ensures fun m0 x m1 ->
    st.interp (post x `st.star` st.invariant m1) m1 /\
    preserves_frame pre (post x) m0 m1)
= match f with
  | Ret _ x -> x
  | _ ->
    let Step f = step f in
    run f
