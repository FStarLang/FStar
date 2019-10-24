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

noeq
type m (s:Type0) (a:Type) =
  | Ret : a -> m s a
  | Get : (s -> m s a) -> m s a
  | Put : x:s -> m s a -> m s a
module W = FStar.WellFounded

let rec bind_m #s #a #b (x:m s a) (y: (a -> m s b)) : m s b =
  match x with
  | Ret x -> y x
  | Get k -> Get (fun s -> W.axiom1 k s; bind_m (k s) y)
  | Put s k -> Put s (bind_m k y)


(* First a simply typed variant *)
let repr a s =
  unit -> m s a

let return (a:Type) (s:Type) (x:a)
  : repr a s
  = fun () -> Ret x

let rec bind a b s (f:repr a s) (g : (a -> repr b s))
  : repr b s
  = let m_f = f () in
    let m_g = fun x -> g x () in
    fun () -> bind_m #s #a #b m_f m_g

//no subsumption rule
let subcomp (a:Type) (s:Type) (f:repr a s)
  : Tot (repr a s)
  = f

let if_then_else (a:Type) (s:Type)
                 (f:repr a s)
                 (g:repr a s)
                 (p:Type0)
  : Type
  = repr a s

let if_then_else_true
     (a:Type) (s:Type)
     (f:repr a s)
     (g:repr a s)
     (p:Type0 { p })
  : if_then_else a s f g p
  = subcomp a s f

let if_then_else_false
     (a:Type) (s:Type)
     (f:repr a s)
     (g:repr a s)
     (p:Type0 { ~p })
  : if_then_else a s f g p
  = subcomp a s g

let get s : repr s s =
    fun () -> Get Ret

let put s (x:s) : repr unit s =
    fun () -> Put x (Ret ())

reifiable reflectable
layered_effect {
  FST : a:Type -> s:Type0 -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp;
       if_then_else = if_then_else;

       get = get;
       put = put
}

let lift_pure_fst
    (a:Type)
    (s:Type)
    (wp:pure_wp a)
    (f:unit -> PURE a wp)
  : repr a s
  = assume(wp (fun x -> True)); //to suppress the WP
    return a s (f())

sub_effect PURE ~> FST = lift_pure_fst

let incr () : FST unit int =
  let x = FST?.get int in
  let y = x + 1 in
  FST?.put int y

////////////////////////////////////////////////////////////////////////////////
// Now for a WP-indexed variant
////////////////////////////////////////////////////////////////////////////////
open FStar.FunctionalExtensionality
let post_t (s:Type0) (a:Type) = a * s -> Type0
let pre_t (s:Type) = s -> Type0
let wp_t (s:Type0) (a:Type) = s -> (post_t s a -> Type0)
module F = FStar.FunctionalExtensionality
let wp_put #s #a (f: wp_t s a) : s -> wp_t s a = fun s s0 -> f s
let wp_return #s #a (x:a) : wp_t s a = F.on_dom _ (fun s0 -> let f : post_t s a -> Type0 = fun post -> post (x, s0) in f)
// let wp_get #s #a #b (f:m s b)
//                     (wp_of: (g:m s a{g << f} -> wp_t s a))
//                     (k: (s -> m s a) {k << f})
//   : wp_t s a
//   = fun post s0 ->
//       W.axiom1 k s0;
//       wp_of (k s0) post s0

let rec wp_of #a #s (x:m s a)
  : wp_t s a
  = match x with
    | Ret v -> fun s0 post -> post (v, s0)
    | Get k -> fun s0 -> W.axiom1 k s0; (wp_of (k s0)) s0
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
  = fun s0 post -> wp_f s0 (fun (x, s1) -> wp_g x s1 post)

module T = FStar.Tactics
let ( *. ) (f:'b -> 'c) (g:'a -> 'b) : 'a -> 'c = fun x -> f (g x)

let rec bind_wp_lem (#a:_) (#b:_) (#s:_) (f:m s a) (g: (a -> m s b))
  : Lemma (wp_of (bind_m f g) `F.feq` bind_wp (wp_of f) (wp_of *. g))
  = match f with
    | Ret x ->
      assert (bind_m f g == g x);
      assert_norm (wp_of #a #s (Ret x) == (fun s0 post -> post (x, s0)));
      assert_norm (wp_of (bind_m (Ret x) g) == bind_wp (wp_of (Ret x)) (wp_of *. g))

    | Put s k ->
      bind_wp_lem k g;
      assert_norm (wp_put (bind_wp (wp_of k) (wp_of *. g)) s ==
                   bind_wp (wp_put (wp_of k) s) (wp_of *. g))

    | Get k ->
      let aux (x:s)
        : Lemma
          (ensures (wp_of (bind_m (k x) g) `F.feq`
                    bind_wp (wp_of (k x)) (wp_of *. g)))
          [SMTPat (k x)]
        = W.axiom1 k x;
          bind_wp_lem (k x) g
      in
      assert_norm (wp_of (bind_m (Get k) g) ==
                   wp_of (Get (fun x -> bind_m (k x) g)));
      assert_norm (wp_of (Get (fun x -> bind_m (k x) g)) ==
                   (fun s0 -> (wp_of (bind_m (k s0) g)) s0));

      assert ((fun s0 -> (wp_of (bind_m (k s0) g)) s0) `F.feq`
              (fun s0 -> bind_wp (wp_of (k s0)) (wp_of *. g) s0));
      assert_norm (bind_wp (wp_of (Get k)) (wp_of *. g) ==
                   bind_wp ((fun s0 -> wp_of (k s0) s0))
                            (wp_of *. g));
      assert_norm (bind_wp ((fun s0 -> wp_of (k s0) s0)) (wp_of *. g) ==
                  (fun s0 -> bind_wp (wp_of (k s0)) (wp_of *. g) s0))

let ibind a b s wp_f wp_g
    (f:irepr a s wp_f)
    (g : (x:a -> irepr b s (wp_g x)))
  : irepr b s (bind_wp wp_f wp_g)
  = let m_f = f () in
    let m_g = fun x -> g x () in
    fun () ->
         bind_wp_lem m_f m_g;
         assert (wp_f `F.feq` wp_of m_f);
         assert (forall x. (wp_of *. m_g) x `F.feq` wp_g x);
         assume (wp_f == wp_of m_f);
         assume (wp_of *. m_g == wp_g);
         bind_m m_f m_g
