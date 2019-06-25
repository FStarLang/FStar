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
module HighComp

open FStar.Classical
open FStar.Tactics
open FStar.Reflection

module U32 = FStar.UInt32


type mint = U32.t
type state = mint * mint

// High-level specs live in [comp]
let comp a = state -> M (a * state)

(** ** High Level DSL **)

let hreturn (a:Type) (x : a) : comp a = fun s -> (x, s)

let hbind (a:Type) (b:Type) (m : comp a) (f : a -> comp b) : comp b =
    fun s -> let (x, s1) = m s in f x s1

let hread (i:int) : comp mint =
    fun s -> if i = 0 then (fst s, s)
          else (snd s, s)

let hwrite (i:int) (v:mint) : comp unit =
    fun s -> if i = 0 then ((), (v, snd s))
          else ((), (fst s, v))

// Effect definition
total reifiable reflectable new_effect {
      HIGH : a:Type -> Effect
      with repr  = comp
      ; bind     = hbind
      ; return   = hreturn
      ; get      = hread
      ; put      = hwrite
}


(** ** High level WPs (monotonic by construction) *)

type hwp a = HIGH?.wp a

type hpre = state -> Type0
type hpost a = state -> a -> state -> Type0

unfold
let as_wp (#a : Type) (pre : hpre) (post : hpost a) : hwp a =
      (fun s0 p -> pre s0 /\ (forall r s1. post s0 r s1 ==> p (r, s1)))


let monotonic #a (wp:hwp a) =
  forall p1 p2 s. {:pattern wp s p1; wp s p2}
    (forall x.{:pattern (p1 x) \/ (p2 x)} p1 x ==> p2 x) ==>
    wp s p1 ==>
    wp s p2

type hwp_mon 'a = (wp:hwp 'a{monotonic wp})

let null_wp 'a : hwp_mon 'a  = fun s0 p -> forall s. p s

// [comp] type with wp
// GM, Oct 23 2018: I think this is just HIGH?.repr 'a wp. If I do that,
// things seem to work until I get a mysterious failure in LowComp.
type comp_wp 'a (wp : hwp_mon 'a) = s0:state -> PURE ('a * state) (wp s0)

type comp_p 'a (pre : hpre) (post : hpost 'a) = comp_wp 'a (as_wp pre post)

(** Effect deffinitions *)

effect H (a: Type) = HIGH a (null_wp a)

effect High (a:Type) (pre:hpre) (post:hpost a) =
       HIGH a (as_wp pre post)


effect HighMon (a:Type) (wp:hwp_mon a) = HIGH a wp

effect Hi (a:Type)
          (pre: state -> Type)
          (post: state -> a -> state -> Type) =
       HighMon a (as_wp pre post)

// GM: Is this qualifying by the current module? How the hell is that succeeding, given #451?
// GM: Also what's the difference with `H`?
effect HTot (a:Type) = HIGH a (null_wp a)


(** WP combinators *)

unfold
let return_wp (#a:Type) (x : a) : hwp_mon a = HIGH?.return_wp a x

unfold
let bind_wp #a #b (wp1:hwp_mon a) (fwp2 : (a -> hwp_mon b)) : (wp:hwp_mon b) =
  HIGH?.bind_wp range_0 a b wp1 fwp2

unfold
let read_wp (i:nat) : hwp_mon mint =
  fun s0 post -> post (hread i s0)

unfold
let write_wp (i:nat) (v:mint) : hwp_mon unit =
  fun s0 post -> post (hwrite i v s0)

unfold
let ite_wp #a (b : bool) (wp1 : hwp_mon a) (wp2 : hwp_mon a) : hwp_mon a =
  HIGH?.wp_if_then_else a b wp1 wp2

val for_wp : (int -> hwp_mon unit) -> (lo : int) -> (hi : int{hi >= lo}) -> Tot (hwp_mon unit) (decreases (hi - lo))
let rec for_wp (wp:int -> hwp_mon unit) (lo : int) (hi : int{hi >= lo}) : Tot (hwp_mon unit) (decreases (hi - lo)) =
  if lo = hi then (return_wp ())
  else (bind_wp (wp lo) (fun (_:unit) -> for_wp wp (lo + 1) hi))

// Unfolding lemma for the rec def
// GM: Oct 23 2018, this goes through by compute () alone
let for_wp_unfold (wp:int -> hwp_mon unit) (lo : int) (hi : int{hi >= lo}) :
    Lemma (requires (lo < hi))
          (ensures (for_wp wp lo hi == bind_wp (wp lo) (fun _ -> for_wp wp (lo + 1) hi)))
       by (compute ()) = ()

(*
//   assert (~ (lo = hi));
//   assert ((if lo = hi then (return_wp ())
//            else (bind_wp (wp lo) (fun (_:unit) -> for_wp wp (lo + 1) hi))) ==
//            bind_wp (wp lo) (fun _ -> for_wp wp (lo + 1) hi));
//            assert_norm (for_wp wp lo hi ==
//                         (if lo = hi then (return_wp ())
//                          else (bind_wp (wp lo) (fun (_:unit) -> for_wp wp (lo + 1) hi))))
// *)



// for combinator
let rec for (#wp : int -> hwp_mon unit) (lo : int) (hi : int{lo <= hi}) (f : (i:int) -> HIGH unit (wp i)) :
    HIGH unit (for_wp wp lo hi) (decreases (hi - lo)) =
  if lo = hi then ()
  else
  (f lo;
   for #wp (lo + 1) hi f)


let get () : H state = (HIGH?.get 0, HIGH?.get 1)

let rec for' (inv : state -> int -> Type0)
             (f : (i:int) -> High unit (requires (fun h0 -> inv h0 i))
                                    (ensures (fun h0 _ h1 -> inv h1 (i + 1))))
             (lo : int) (hi : int{lo <= hi}) :
    High unit (requires (fun h0 -> inv h0 lo))
              (ensures (fun h0 _ h1 -> inv h1 hi)) (decreases (hi - lo)) =
    if lo = hi then ()
    else
      (f lo; for' inv f (lo + 1) hi)

(** ** Elaborated combinators for high DSL **)

let return_elab (#a:Type) (x : a) : comp_wp a (return_wp x) =
  HIGH?.return_elab a x

let bind_elab #a #b #f_w ($f:comp_wp a f_w) #g_w ($g:(x:a) -> comp_wp b (g_w x)) :
    Tot (comp_wp b (bind_wp f_w g_w)) = HIGH?.bind_elab a b f_w f g_w g



let rec for_elab (#wp : int -> hwp_mon unit) (lo : int) (hi : int{lo <= hi}) (f : (i:int) -> comp_wp unit (wp i)) :
    Tot (comp_wp unit (for_wp wp lo hi)) (decreases (hi - lo)) =
  if lo = hi then (return_elab ())
  else (let (m : comp_wp unit (wp lo)) = f lo in
        let f (u:unit) : comp_wp (unit) (for_wp wp (lo+1) hi) = for_elab #wp (lo + 1) hi f in
        let p = for_wp_unfold wp lo hi in
        assert (for_wp wp lo hi == bind_wp (wp lo) (fun _ -> for_wp wp (lo + 1) hi));
        let b = bind_elab m f in b)

// Unfolding lemma for the rec def
let rec for_elab_unfold (#wp : int -> hwp_mon unit) (lo : int) (hi : int{lo <= hi}) (f : (i:int) -> comp_wp unit (wp i)) :
    Lemma (requires (lo < hi))
          (ensures (for_elab #wp lo hi f ==
                    (let (m : comp_wp unit (wp lo)) = f lo in
                     let cf (u:unit) : comp_wp (unit) (for_wp wp (lo+1) hi) = for_elab #wp (lo + 1) hi f in
                     let p = for_wp_unfold wp lo hi in
                     bind_elab m cf))) =
  assert_norm (for_elab #wp lo hi f ==
               (if lo = hi then (return_elab ())
                else (let (m : comp_wp unit (wp lo)) = f lo in
                      let f (u:unit) : comp_wp (unit) (for_wp wp (lo+1) hi) = for_elab #wp (lo + 1) hi f in
                      let p = for_wp_unfold wp lo hi in
                      assert (for_wp wp lo hi == bind_wp (wp lo) (fun _ -> for_wp wp (lo + 1) hi));
                      bind_elab #unit #unit #(wp lo) m f)));
               ()

let rec for_elab' (inv : state -> int -> Type0)
               (f : (i:int) -> comp_p unit (requires (fun h0 -> inv h0 i))
                                        (ensures (fun h0 _ h1 -> inv h1 (i + 1))))
               (lo : int) (hi : int{lo <= hi}) :
      Tot (comp_p unit (requires (fun h0 -> inv h0 lo))
                       (ensures (fun h0 _ h1 -> inv h1 hi))) (decreases (hi - lo)) =
      if lo = hi then (return_elab ())
      else
        begin
          let k () = for_elab' inv f (lo + 1) hi in
          bind_elab (f lo) k
        end

let hread_elab (i:nat) : comp_wp mint (read_wp i) =
  (fun s -> if i = 0 then (fst s, s) else (snd s, s))

let hwrite_elab (i:nat) (v:mint) : comp_wp unit (write_wp i v) =
  fun s -> if i = 0 then ((), (v, snd s))
        else ((), (fst s, v))

let put_action = HIGH?.put
let get_action = HIGH?.get

let ite_elab (#a:Type) (b : bool) (#wp1 : hwp_mon a) (c1:comp_wp a wp1)
    (#wp2 : hwp_mon a) (c2:comp_wp a wp2) : Tot (comp_wp a (ite_wp b wp1 wp2)) by (compute (); explode () ;dump "")  =
    (fun s0 -> if b then c1 s0 else c2 s0)


(** ** Typing inversion axioms **)

let subsumes #a (wp1 : hwp a) (wp2 : hwp a) = forall s0 post. wp2 s0 post ==> wp1 s0 post

// GM, 22 Oct 2018: These axioms look a bit useless now, since they
// require that (comp_wp a wp) and (comp_wp a (return_wp x)) match (due
// to the fix to ===, cf. #1533). So the WPs would have to match. And
// it's not like we could make the WPs "irrelevant", they matter a lot.

assume val return_inv (#a:Type) (#wp : hwp_mon a) (c : comp_wp a wp) (x:a):
  Lemma (requires (c === return_elab x)) (ensures (subsumes (return_wp x) wp))

assume val write_inv (#wp : hwp_mon unit) (c : comp_wp unit wp) (i:nat) (v:mint) :
  Lemma (requires (c === hwrite_elab i v)) (ensures (subsumes (write_wp i v) wp))

assume val read_inv (#wp : hwp_mon mint) (c : comp_wp mint wp) (i:nat) :
  Lemma (requires (c === hread_elab i)) (ensures (subsumes (read_wp i) wp))

assume val bind_inv (#a:Type) (#b:Type) (#f_w : hwp_mon a) (f:comp_wp a f_w)
                    (#g_w: a -> hwp_mon b) (g:(x:a) -> comp_wp b (g_w x)) (#wp : hwp_mon b) (c:comp_wp b wp) :
  Lemma (requires (c === bind_elab f g))
        (ensures (subsumes (bind_wp f_w g_w) wp))

assume val ite_inv (#a:Type) (b:bool) (#f_w:hwp_mon a) (f:comp_wp a f_w)
       (#g_w:hwp_mon a) (g:comp_wp a g_w) (#wp:hwp_mon a) (c:comp_wp a wp) :
  Lemma (requires (c === ite_elab b f g))
        (ensures (subsumes (ite_wp b f_w g_w) wp))

assume val for_inv (#fwp : int -> hwp_mon unit) (lo : int) (hi : int{lo <= hi}) (f : (i:int) -> comp_wp unit (fwp i))
           (#wp:hwp_mon unit) (c:comp_wp unit wp) :
  Lemma (requires (c === for_elab lo hi f))
        (ensures (subsumes (for_wp fwp lo hi) wp))

assume val for_inv'  (inv : state -> int -> Type0)
                     (f : (i:int) -> comp_p unit (requires (fun h0 -> inv h0 i))
                                              (ensures (fun h0 _ h1 -> inv h1 (i + 1))))
       (lo : int) (hi : int{lo <= hi}) (#wp:hwp_mon unit) (c:comp_wp unit wp) :
  Lemma (requires (c === for_elab' inv f lo hi))
        (ensures (subsumes (as_wp (fun h0 -> inv h0 lo)
                                            (fun h0 _ h1 -> inv h1 hi)) wp))

(** ** Explicit casting to stronger WPs **)

let cast #a (#wp1 : hwp_mon a) (wp2: hwp_mon a{subsumes wp1 wp2}) (c : comp_wp a wp1) : comp_wp a wp2 =
  c

//GM: Oct 22, 2018: This lemma now fails to verify due to the fix for #1533. However, it doesn't seem to be used.
(* let cast_eq #a (#wp1 : hwp_mon a) (wp2: hwp_mon a{subsumes wp1 wp2}) (c : comp_wp a wp1) : Lemma (c === cast wp2 c) = () *)


(** ** Equality on high computations **)

let h_eq (#a:Type) (wp1:hwp_mon a) (wp2:hwp_mon a) (c1:comp_wp a wp1) (c2:comp_wp a wp2)
  =
    (forall s0. wp1 s0 (fun _ -> True) <==> wp2 s0 (fun _ -> True)) /\
    (forall s0. (wp1 s0 (fun _ -> True) /\ wp2 s0 (fun _ -> True)) ==> c1 s0 == c2 s0)

(** ** Reify commutes **)

let hwrite_eq (#a:Type) (i:nat) (v:mint) :
   Lemma (h_eq (write_wp i v) (write_wp i v) (hwrite_elab i v) (reify (HIGH?.put i v))) = ()

let hread_eq (#a:Type) (i:nat) :
   Lemma (h_eq (read_wp i) (read_wp i) (hread_elab i) (reify (HIGH?.get i))) = ()


let h_thunk a (wp:hwp_mon a) = unit -> HIGH a wp

let reif (#a:Type) wp (c : h_thunk a wp) :
  comp_wp a wp = reify (c ())

let reify_bind_commutes
          (#a #b : _)
          (#wp1 : _) ($c1:h_thunk a wp1)
          (#wp2 : _) ($c2: (x:a -> h_thunk b (wp2 x)))
          (s0:_{bind_wp wp1 wp2 s0 (fun _ -> True)})
     = reify (let x = c1 () in c2 x ()) s0 ==
       bind_elab (reify (c1 ()))
                 (fun x -> reify (c2 x ())) s0


let ite_reif (#a:Type) (b : bool) (#wp1 : hwp_mon a) ($c1:h_thunk a wp1)
  (#wp2 : hwp_mon a) ($c2:h_thunk a wp2) : comp_wp a (ite_wp b wp1 wp2) =
  reify (if b then c1 () else c2 ())

let reify_ite_commutes (#a:Type) (b : bool) (#wp1 : hwp_mon a) ($c1:h_thunk a wp1)
  (#wp2 : hwp_mon a) ($c2:h_thunk a wp2) (s0:_{ite_wp b wp1 wp2 s0 (fun _ -> True)}) =
  ite_reif b c1 c2 s0 == ite_elab b (reif wp1 c1) (reif wp2 c2) s0

let test (i:nat) (v:mint) (s0:_) =
    assert (reify (let _ = HIGH?.put i v in
                   HIGH?.put i v) s0 ==
            bind_elab (reify (HIGH?.put i v))
                      (fun _ -> reify (HIGH?.put i v)) s0)

let test2_tac (i:nat) (v:mint) (s0:_) =
    assert (reify (let _ = HIGH?.put i v in
                   HIGH?.put i v) s0 ==
            bind_elab (reify (HIGH?.put i v))
                      (fun _ -> reify (HIGH?.put i v)) s0)
         by (norm [reify_; delta_only [`%bind_elab; `%HIGH?.bind_elab; `%reify_bind_commutes]];
             trefl())

let test2_tac_again (i:nat) (v:mint) (s0:_) =
    assert (reify_bind_commutes (fun () -> HIGH?.put i v)
                                (fun () () -> HIGH?.put i v) s0)
        by (norm [reify_; delta_only [`%bind_elab; `%HIGH?.bind_elab; `%reify_bind_commutes]];
            trefl())

let bind_commutes_lemma
          (#a #b : _)
          (#wp1 : _) (c1:h_thunk a wp1)
          (#wp2 : _) (c2: (x:a -> h_thunk b (wp2 x))) (s0:_)
    : Lemma
         (requires (HIGH?.bind_wp range_0 _ _ wp1 wp2 s0 (fun _ -> True)))
         (ensures (reify_bind_commutes c1 c2 s0))
    = assert (reify_bind_commutes c1 c2 s0)
          by (dump "start";
              norm [reify_; delta_only [`%bind_elab; `%HIGH?.bind_elab; `%reify_bind_commutes]];
              dump "after norm";
              trefl())

let ite_commutes_lemma (#a : Type) (b : bool)
      (#wp1 : hwp_mon a) ($c1:h_thunk a wp1)
      (#wp2 : hwp_mon a) ($c2:h_thunk a wp2) (s0:state) :
      Lemma (requires (ite_wp b wp1 wp2 s0 (fun _ -> True)))
            (ensures (reify_ite_commutes b c1 c2 s0)) = ()

