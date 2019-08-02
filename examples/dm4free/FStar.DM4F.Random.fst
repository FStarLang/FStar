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
module FStar.DM4F.Random

open FStar.DM4F.Heap.Random

(* for some reason this `unfold` makes everything 25% faster *)
unfold type store = id * tape

(** Read-only tape with a pointer to the next unread position *)
type rand (a:Type) = (id * tape) -> M (option a * id)

let return (a:Type) (x:a) : rand a = fun (next,_) -> Some x, next

let bind (a b:Type) (c:rand a) (f:a -> rand b) : rand b =
  fun s ->
    let r, next' = c s in
    match r with
    | None   -> None, next'
    | Some x -> f x (next', snd s)

(*
// Tm_refine is outside of the definition language: ...
let sample () : rand elem = fun store ->
  let next, t = store in
  if incrementable next then
    (Some (index t next), incr next)
  else
    (None, next)
*)

(** Get store *)
let get () : rand store = fun s -> Some s, fst s

(** Update tape pointer *)
let put i : rand unit = fun _ -> Some (), i

(** Raise exception *)
let raise (a:Type) () : rand a = fun s -> None, fst s

total reifiable reflectable new_effect {
  RAND: a:Type -> Effect
  with repr   = rand
     ; bind   = bind
     ; return = return
     ; get   = get
     ; put   = put
     ; raise = raise
}

effect Rand (a:Type) =
  RAND a (fun initial_tape post -> forall (x:option a * id). post x)


(** If not past the end of the tape, read a value and advance pointer *)
reifiable val sample: unit -> RAND elem (fun (next,t) p ->
  if incrementable next then p (Some (index t next), incr next)
  else p (None, next))
let sample () =
  let next, t = RAND?.get () in
  if incrementable next then
    begin
    RAND?.put (incr next);
    index t next
    end
  else
    RAND?.raise elem ()


(* GM: This is failing now... I couldn't make it go through even trying to
 * manually trigger reification. *)
let test_sample_some (v:elem) (t:tape{sel t (to_id 0) == v}) =
  let f = reify (sample ()) in
  admit ();
  assert (f (to_id 0,t) == (Some v, to_id 1))

let test_sample_none (v:elem) (t:tape) =
  let f = reify (sample ()) in
  admit ();
  assert (f (to_id 9,t) == (None, to_id 9))

(** Bijection over tapes, the inverse function acts as a witness *)
noeq type bijection =
  | Bijection:
      f:(tape -> tape) ->
      finv:(tape -> tape){forall (h:tape). equal (f (finv h)) h /\ equal (finv (f h)) h} ->
      bijection

(** Inverse of a bijection *)
let inverse (bij:bijection) : bijection =
  Bijection bij.finv bij.f


(** Assume `sum` over `tape`. Definable as long as tape is finite *)
assume val sum: f:(tape -> nat) -> nat

(** Reordering terms in a sum doesn't change the result *)
assume val sum_bijection: f:(tape -> nat) -> bij:bijection -> Lemma
  (sum f == sum (fun h -> f (bij.f h)))

(** The sum of non-negative function is monotonic *)
assume val sum_monotonic: f:(tape -> nat) -> g:(tape -> nat) -> Lemma
  (requires (forall h. f h <= g h))
  (ensures (sum f <= sum g))

(** Corollary *)
val sum_extensional: f:(tape -> nat) -> g:(tape -> nat) -> Lemma
  (requires (forall h. f h == g h))
  (ensures (sum f == sum g))
let sum_extensional f g =
  sum_monotonic f g;
  sum_monotonic g f

(** Unnormalized measure of a function `p` wrt the denotation of a probabilistic
    computation `f`.
    Assumes that the initial random tape is uniformly distributed
    When `p:a -> {0,1}` and `tape` is finite
    Pr[f : p] == 1/|tape| * sum_{h:tape} p (f h) == 1/|tape| * mass f p
*)
val mass: #a:Type -> f:(store -> M (a * id)) -> p:(a -> nat) -> nat
let mass #a f p = sum (fun h -> let r,_ = f (to_id 0,h) in p r)

val point: #a:eqtype -> x:a -> y:option a -> nat
let point #a x = fun y -> if y = Some x then 1 else 0


(** If there exists a bijection over tapes such that `p1` evaluated
    on the result of `c1` is less than or equal to `p2` evaluated
    on the resulf of `c2`, then the measure of `p1` wrt `c1` is less than or
    equal to the measure of `p2` wrt `c2` *)
val pr_leq: #a:Type -> #b:Type ->
  c1:(store -> M (a * id)) ->
  c2:(store -> M (b * id)) ->
  p1:(a -> nat) ->
  p2:(b -> nat) ->
  bij:bijection -> Lemma
  (requires
    (forall t.
      let r1,_ = c1 (to_id 0,t) in
      let r2,_ = c2 (to_id 0,bij.f t) in
      p1 r1 <= p2 r2))
  (ensures (mass c1 p1 <= mass c2 p2))
let pr_leq #a #b c1 c2 p1 p2 bij =
  let bij' = inverse bij in
  let f1 = (fun h -> let r1,_ = c1 (to_id 0,h) in p1 r1) in
  let f2 = (fun h -> let r2,_ = c2 (to_id 0,h) in p2 r2) in
  sum_monotonic f1 (fun h -> let r2,_ = c2 (to_id 0,bij.f h) in p2 r2);
  sum_bijection (fun h -> let r2,_ = c2 (to_id 0,bij.f h) in p2 r2) bij';
  sum_extensional (fun h -> let r2,_ = c2 (to_id 0,bij.f (bij'.f h)) in p2 r2) f2

(** Corollary *)
val pr_eq: #a:Type -> #b:Type ->
  c1:(store -> M (a * id)) ->
  c2:(store -> M (b * id)) ->
  p1:(a -> nat) ->
  p2:(b -> nat) ->
  bij:bijection -> Lemma
  (requires
    (forall h. let r1,_ = c1 (to_id 0, h) in
          let r2,_ = c2 (to_id 0, bij.f h) in
          p1 r1 == p2 r2))
  (ensures (mass c1 p1 == mass c2 p2))
let pr_eq #a #b c1 c2 p1 p2 bij =
  pr_leq c1 c2 p1 p2 bij;
  pr_leq c2 c1 p2 p1 (inverse bij)

val cond: #a:Type ->
  pre:Type ->
  post:(a -> a -> Type) ->
  b1:bool ->
  b2:bool ->
  c1 :(store -> M (a * id)) ->
  c1':(store -> M (a * id)) ->
  c2 :(store -> M (a * id)) ->
  c2':(store -> M (a * id)) ->
  h:tape ->
  Lemma
  (requires (
    forall h.
      let r1,_  = c1  (to_id 0, h) in
      let r2,_  = c2  (to_id 0, h) in
      let r1',_ = c1' (to_id 0, h) in
      let r2',_ = c2' (to_id 0, h) in
      (pre ==> b1 == b2) /\
      (pre /\ b1  ==> post r1 r2) /\
      (pre /\ ~b1 ==> post r1' r2')))
  (ensures (
    let r1,_ = (if b1 then c1 else c1') (to_id 0, h) in
    let r2,_ = (if b2 then c2 else c2') (to_id 0, h) in
    pre ==> post r1 r2))
let cond #a pre post b1 b2 c1 c1' c2 c2' h = ()
