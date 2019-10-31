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

module Locals.Effect

module M = FStar.Map

/// Layering an effect over PURE to work with local variables
/// The locals are modeled as a map, that is threaded through in the state passing style
///
/// It's a total effect, and tests below include some termination checking

noeq
type locals_t'= {
  next:nat;
  m:M.t nat (a:Type0 & a)
}

type locals_t = m:locals_t'{
  forall (i:nat). i >= m.next ==> not (M.contains m.m i)
}

type pre_t = locals_t -> Type0
type post_t (a:Type) = a -> locals_t -> Type0
type wp_t (a:Type) = wp:(post_t a -> pre_t){
  forall (p q:post_t a).
    (forall x m. p x m ==> q x m) ==>
    (forall m. wp p m ==> wp q m)
}

type repr (a:Type) (wp:wp_t a) =
  m:locals_t ->
  PURE (a & locals_t) (fun p -> wp (fun r m1 -> p (r, m1)) m)

let return (a:Type) (x:a)
: repr a (fun p m -> p x m)
= fun m -> (x, m)

let bind (a:Type) (b:Type)
  (wp_f:wp_t a)
  (wp_g:a -> wp_t b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
: repr b (fun p -> wp_f (fun x -> (wp_g x) p))
= fun m ->
  let (x, m) = f m in
  (g x) m

let subcomp (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f)
: Pure (repr a wp_g)
  (requires forall p m. wp_g p m ==> wp_f p m)
  (ensures fun _ -> True)
= f

let if_then_else (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f) (g:repr a wp_g)
  (p:Type0)
: Type
= repr a (fun post m -> (p ==> wp_f post m) /\ ((~ p) ==> wp_g post m))

total reifiable reflectable
layered_effect {
  LVARS : a:Type -> wp_t a -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp;
       if_then_else = if_then_else
}

assume Pure_wp_monotonicity:
  forall (a:Type) (wp:pure_wp a).
    (forall (p q:pure_post a).
       (forall (x:a). p x ==> q x) ==>
       (wp p ==> wp q))

let lift_pure_lvars (a:Type)
  (wp:pure_wp a) (f:unit -> PURE a wp)
: repr a (fun p m -> wp (fun x -> p x m))
= fun m -> f (), m

sub_effect PURE ~> LVARS = lift_pure_lvars

effect LV (a:Type) (pre:locals_t -> Type0) (post:locals_t -> a -> locals_t -> Type0) =
  LVARS a (fun p m -> pre m /\ (forall x m1. post m x m1 ==> p x m1))


let create (a:Type0) (x:a)
: LVARS nat
  (fun p m0 ->
    forall r m1.
      (not (m0.m `M.contains` r) /\
       m1.m == Map.upd m0.m r (| a, x |)) ==> p r m1)
= LVARS?.reflect (fun m ->
    let next = m.next in
    next, {
      next = next + 1;
      m = Map.upd m.m next (| a, x |)
    })


let read (#a:Type0) (n:nat)
: LVARS a
  (fun p m0 ->
   m0.m `M.contains` n /\
   dfst (m0.m `M.sel` n) == a /\
   (forall r. r == dsnd (m0.m `M.sel` n) ==> p r m0))
= LVARS?.reflect (fun m -> dsnd (m.m `M.sel` n), m)

let write (#a:Type0) (n:nat) (x:a)
: LVARS unit
  (fun p m0 ->
   m0.m `M.contains` n /\
   dfst (m0.m `M.sel` n) == a /\
   (forall m1.
     (m1.next == m0.next /\
      m1.m == Map.upd m0.m n (| a, x |)) ==> p () m1))
= LVARS?.reflect (fun m -> (), { m with m = Map.upd m.m n (| a, x |) })

let get ()
: LVARS (Map.t nat (a:Type0 & a))
  (fun p m0 -> p m0.m m0)
= LVARS?.reflect (fun m -> m.m, m)


let test () : LV unit (fun _ -> True) (fun _ _ _ -> True) =
  let n1 = create nat 0 in
  let n2 = create bool true in
  let n3 = create unit () in


  let v1: nat = read n1 in
  assert (v1 == 0)

let emp_locals = {
  next = 0;
  m = Map.restrict Set.empty (Map.const (| unit, () |))
}

let run_with_locals (#a:Type)
  (#pre:locals_t -> Type0) (#post:locals_t -> a -> locals_t -> Type0)
  ($f:unit -> LV a pre post)
: Pure a
  (requires pre emp_locals)
  (ensures fun r -> exists m. post emp_locals r m)
= fst (reify (f ()) emp_locals)


/// Testing some termination

let rec sum (n:nat) : LV nat (fun _ -> True) (fun _ _ _ -> True)
= if n = 0 then 0
  else
    let s = sum (n - 1) in  //let binding is important, can't write 1 + sum (n - 1), see #881
    1 + s

module L = FStar.List.Tot

let rec test1 (l:list nat) : LV nat (fun _ -> True) (fun _ n _ -> n == L.length l)
= match l with
  | [] -> 0
  | _::tl ->
   let n = test1 tl in  //let binding is important, can't write 1 + test1 tl, see #881
   n + 1


/// Termination check failure

[@expect_failure]
let rec test2 (l:list nat) : LV nat (fun _ -> True) (fun _ _ _ -> True)
= test2 l
