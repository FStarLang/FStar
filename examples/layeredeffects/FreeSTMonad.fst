(*
   Copyright 2008-2018 Microsoft Research

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

module FreeSTMonad
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics

noeq
type m (s:Type0) (a:Type) =
  | Ret : a -> m s a
  | Get : (s -> m s a) -> m s a
  | Put : x:s -> m s a -> m s a

let rec bind_m #s #a #b (x:m s a) (y: (a -> m s b)) : m s b =
  match x with
  | Ret x -> y x
  | Get k -> Get (fun s -> W.axiom1 k s; bind_m (k s) y)
  | Put s k -> Put s (bind_m k y)

////////////////////////////////////////////////////////////////////////////////
// A WP-indexed variant of `m`
////////////////////////////////////////////////////////////////////////////////

let post_t (s:Type0) (a:Type) = a * s -> Type0
let pre_t (s:Type) = s -> Type0
let wp_t (s:Type0) (a:Type) = s ^-> (post_t s a -> Type0)

let wp_put #s #a (f: wp_t s a) : s -> wp_t s a = fun s -> F.on _ (fun s0 -> f s)
let wp_return #s #a (x:a) : wp_t s a = F.on _ (fun s0 post -> post (x, s0))

let rec wp_of #a #s (x:m s a)
  : wp_t s a
  = match x with
    | Ret v -> wp_return v
    | Get k -> F.on _ (fun s0 -> W.axiom1 k s0; (wp_of (k s0)) s0)
    | Put s k -> wp_put (wp_of k) s

// soundness of wp_of
let rec run (#a:_) (#s:_) (m:m s a) (s0:s) (post: post_t s a)
  : Pure (a * s)
         (requires
           wp_of m s0 post)
         (ensures
           post)
  = match m with
    | Ret x -> (x, s0)
    | Get k ->
      W.axiom1 k s0;
      run (k s0) s0 post
    | Put s k ->
      run k s post


let irepr a s (wp: wp_t s a) =
  unit -> m:m s a { wp_of m `F.feq` wp }

let ireturn (a:Type) (s:Type) (x:a)
  : irepr a s (wp_of (Ret x))
  = fun () -> Ret x

let bind_wp #a #b #s (wp_f:wp_t s a) (wp_g: (a -> wp_t s b))
  : wp_t s b
  = F.on _ (fun s0 post -> wp_f s0 (fun (x, s1) -> wp_g x s1 post))


let ( *. ) #a #b #c (f:b -> c) (g:a -> b) : (a ^-> c) = F.on _ (fun x -> f (g x))

let lem_on_comp #a #b #c (f:b -> c) (g:a -> b)
  : Lemma (F.on _ (f *. g) == f *. g)
  = ()

let eta (f:'a -> 'b) : Lemma (f == (fun x -> f x)) = ()

let rec bind_wp_lem' (#a:_) (#b:_) (#s:_) (f:m s a) (g: (a -> m s b))
  : Lemma (wp_of (bind_m f g) `F.feq` bind_wp (wp_of f) (wp_of *. g))
  = match f with
    | Ret x ->
      assert (bind_m f g == g x);
      assert_norm (wp_of #a #s (Ret x) `F.feq` (fun s0 post -> post (x, s0)));
      assert (wp_of (bind_m (Ret x) g) `F.feq` bind_wp (wp_of (Ret x)) (wp_of *. g))
           by (T.dump "A";
               T.norm [delta];
               T.dump "B";
               let x = T.forall_intro () in
               T.dump "C";
               T.mapply (`eta);
               T.dump "D")
    | Put s k ->
      bind_wp_lem' k g;
      assert_norm (wp_put (bind_wp (wp_of k) (wp_of *. g)) s `F.feq`
                   bind_wp (wp_put (wp_of k) s) (wp_of *. g))

    | Get k ->
      let aux (x:s)
        : Lemma
          (ensures (wp_of (bind_m (k x) g) `F.feq`
                    bind_wp (wp_of (k x)) (wp_of *. g)))
          [SMTPat (k x)]
        = W.axiom1 k x;
          bind_wp_lem' (k x) g
      in
      assert_norm (wp_of (bind_m (Get k) g) ==
                   wp_of (Get (fun x -> bind_m (k x) g)));
      assert_norm (wp_of (Get (fun x -> bind_m (k x) g)) ==
                   F.on _ (fun s0 -> (wp_of (bind_m (k s0) g)) s0));

      assert ((fun s0 -> (wp_of (bind_m (k s0) g)) s0) `F.feq`
              (fun s0 -> bind_wp (wp_of (k s0)) (wp_of *. g) s0));
      assert_norm (bind_wp (wp_of (Get k)) (wp_of *. g) ==
                   bind_wp (F.on _ (fun s0 -> wp_of (k s0) s0))
                            (wp_of *. g));
      assert_norm (bind_wp (F.on _ (fun s0 -> wp_of (k s0) s0)) (wp_of *. g) ==
                   F.on _ (fun s0 -> bind_wp (wp_of (k s0)) (wp_of *. g) s0))

let bind_wp_lem (#a:_) (#b:_) (#s:_) (f:m s a) (g: (a -> m s b))
  : Lemma (wp_of (bind_m f g) == bind_wp (wp_of f) (wp_of *. g))
  = bind_wp_lem' f g

let ibind a b s wp_f (wp_g: a ^-> wp_t s b)
    (f:irepr a s wp_f)
    (g : (x:a -> irepr b s (wp_g x)))
  : irepr b s (bind_wp wp_f wp_g)
  = let m_f = f () in
    let m_g = fun x -> g x () in
    fun () ->
         bind_wp_lem m_f m_g;
         assert (forall x. (wp_of *. m_g) x == wp_g x);
         assert (wp_f == wp_of m_f);
         assert ((wp_of *. m_g) `F.feq` wp_g);
         F.extensionality _ _ ((wp_of *. m_g)) wp_g;
         assert (F.on _ (wp_of *. m_g) == F.on _ wp_g);
         assert (F.on _ wp_g == wp_g);
         lem_on_comp wp_of m_g;
         assert (F.on _ (wp_of *. m_g) == (wp_of *. m_g));
         bind_m m_f m_g

let iget s : irepr s s (wp_of (Get Ret)) =
    fun () -> Get Ret

let iput s (x:s) : irepr unit s (wp_of (Put x (Ret ()))) =
    fun () -> Put x (Ret ())

// This representation doesn't yet allow for subsumption
// So faking out these rules for now

//a fake subsumption rule for now
let isubcomp (a:Type) (s:Type) (wp wp':wp_t s a) (f:irepr a s wp)
  : Pure (irepr a s wp')
    (requires
      forall s0 post. wp' s0 post ==> wp s0 post)
    (ensures fun _ -> True)
  = admit()

//no meaningful conditional rule for now
let i_if_then_else (a:Type) (s:Type) (wp:_)
                   (f:irepr a s wp)
                   (g:irepr a s wp)
                   (p:Type0)
  : Type
  = irepr a s wp


//a fake lift for now
let lift_pure_ifst
    (a:Type)
    (s:Type0)
    (wp:pure_wp a)
    (f:unit -> PURE a wp)
  : irepr a s (F.on _ (fun (s0:s) (k:post_t s a) ->
                    wp (fun a -> k (a, s0))))
  = admit();
    ireturn a s (f())

reifiable reflectable
layered_effect {
  IFST : a:Type -> s:Type0 -> wp:wp_t s a -> Effect
  with repr         = irepr;
       return       = ireturn;
       bind         = ibind;
       subcomp      = isubcomp;
       if_then_else = i_if_then_else;

       get = iget;
       put = iput
}


sub_effect PURE ~> IFST = lift_pure_ifst

effect IFst (a:Type) (s:Type) (pre:s -> Type) (post: s -> a -> s -> Type)
  = IFST a s (F.on _ (fun s0 k -> pre s0 /\ (forall x s1. post s0 x s1 ==> k (x, s1))))

let iincr ()
  : IFst unit int
    (requires fun s -> True)
    (ensures fun s0 x s1 ->
      s1 == s0 + 1)
  by (T.norm [delta; zeta; iota]; T.smt())
  =
  let x = IFST?.get int in
  let y = x + 1 in
  IFST?.put int y
