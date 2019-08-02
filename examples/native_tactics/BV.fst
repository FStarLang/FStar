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
module BV

open FStar.Tactics
open FStar.Reflection.Formula
open FStar.Reflection.Arith
open FStar.BV
open FStar.UInt

module U64 = FStar.UInt64

// using uint_t' instead of uint_t breaks the tactic (goes to inl).

(* Congruence lemmas *)
val cong_bvand : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
                   (#y:bv_t n) -> (#z:bv_t n) ->
                   squash (w == y) -> squash (x == z) ->
                   Lemma (bvand #n w x == bvand #n y z)
let cong_bvand #n #w #x #y #z pf1 pf2 = ()

val cong_bvxor : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
                   (#y:bv_t n) -> (#z:bv_t n) ->
                   squash (w == y) -> squash (x == z) ->
                   Lemma (bvxor w x == bvxor y z)
let cong_bvxor #n #w #x #y #z pf1 pf2 = ()

val cong_bvor : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
                   (#y:bv_t n) -> (#z:bv_t n) ->
                   squash (w == y) -> squash (x == z) ->
                   Lemma (bvor w x == bvor y z)
let cong_bvor #n #w #x #y #z pf1 pf2 = ()

val cong_bvshl : #n:pos -> (#w:bv_t n) -> (#x:uint_t n) ->
                 (#y:bv_t n) -> squash (w == y) ->
                 Lemma (bvshl w x == bvshl y x)
let cong_bvshl #n #w #x #y pf = ()

val cong_bvshr : #n:pos -> #w:bv_t n -> (#x:uint_t n) ->
               #y:bv_t n -> squash (w == y) ->
               Lemma (bvshr #n w x == bvshr #n y x)
let cong_bvshr #n #w #x #y pf = ()

val cong_bvdiv : #n:pos -> #w:bv_t n -> (#x:uint_t n{x <> 0}) ->
              #y:bv_t n -> squash (w == y) ->
               Lemma (bvdiv #n w x == bvdiv #n y x)
let cong_bvdiv #n #w #x #y pf = ()

val cong_bvmod : #n:pos -> #w:bv_t n -> (#x:uint_t n{x <> 0}) ->
              #y:bv_t n -> squash (w == y) ->
               Lemma (bvmod #n w x == bvmod #n y x)
let cong_bvmod #n #w #x #y pf = ()

val cong_bvmul : #n:pos -> #w:bv_t n -> (#x:uint_t n) ->
              #y:bv_t n -> squash (w == y) ->
               Lemma (bvmul #n w x == bvmul #n y x)
let cong_bvmul #n #w #x #y pf = ()

val cong_bvadd : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
              (#y:bv_t n) -> (#z:bv_t n) ->
              squash (w == y) -> squash (x == z) ->
              Lemma (bvadd w x == bvadd y z)
let cong_bvadd #n #w #x #y #z pf1 pf2 = ()

val cong_bvsub : #n:pos -> (#w:bv_t n) -> (#x:bv_t n) ->
              (#y:bv_t n) -> (#z:bv_t n) ->
              squash (w == y) -> squash (x == z) ->
              Lemma (bvsub w x == bvsub y z)
let cong_bvsub #n #w #x #y #z pf1 pf2 = ()

(* Used to reduce the initial equation to an equation on bitvectors*)
val eq_to_bv: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) ->
              squash (int2bv #n x == int2bv #n y) -> Lemma (x == y)
let eq_to_bv #n #x #y pf = int2bv_lemma_2 #n x y

val lt_to_bv: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) ->
              (b2t (bvult #n (int2bv #n x) (int2bv #n y))) -> Lemma (x < y)
let lt_to_bv #n #x #y pf = int2bv_lemma_ult_2 #n x y

(* Creates two fresh variables and two equations of the form int2bv
   x = z /\ int2bv y = w. The above lemmas transform these two
   equations before finally instantiating them through reflexivity,
   leaving Z3 to solve z = w *)
val trans: #n:pos -> (#x:bv_t n) -> (#y:bv_t n) -> (#z:bv_t n) -> (#w:bv_t n) ->
          squash (x == z) -> squash (y == w) -> squash (z == w) ->
          Lemma (x == y)
let trans #n #x #y #z #w pf1 pf2 pf3 = ()

val trans_lt: #n:pos -> (#x:bv_t n) -> (#y:bv_t n) -> (#z:bv_t n) -> (#w:bv_t n) ->
          (eq2 #(bv_t n) x z) -> (eq2 #(bv_t n) y w) -> squash (bvult #n z w) ->
          Lemma (bvult #n x y)
let trans_lt #n #x #y #z #w pf1 pf2 pf3 = ()

val trans_lt2: #n:pos -> (#x:uint_t n) -> (#y:uint_t n) -> (#z:bv_t n) -> (#w:bv_t n) ->
          squash (int2bv #n x == z) -> squash (int2bv #n y == w) -> (b2t (bvult #n z w)) ->
          Lemma (x < y)
let trans_lt2 #n #x #y #z #w pf1 pf2 pf3 = int2bv_lemma_ult_2 x y

let rec arith_expr_to_bv (e:expr) : Tac unit =
    match e with
    | NatToBv (MulMod e1 _) | MulMod e1 _ ->
        apply_lemma (`int2bv_mul);
        apply_lemma (`cong_bvmul);
        arith_expr_to_bv e1
    | NatToBv (Umod e1 _) | Umod e1 _ ->
        apply_lemma (`int2bv_mod);
        apply_lemma (`cong_bvmod);
        arith_expr_to_bv e1
    | NatToBv (Udiv e1 _) | Udiv e1 _ ->
        apply_lemma (`int2bv_div);
        apply_lemma (`cong_bvdiv);
        arith_expr_to_bv e1
    | NatToBv (Shl e1 _) | Shl e1 _ ->
        apply_lemma (`int2bv_shl);
        apply_lemma (`cong_bvshl);
        arith_expr_to_bv e1
    | NatToBv (Shr e1 _) | Shr e1 _ ->
        apply_lemma (`int2bv_shr);
        apply_lemma (`cong_bvshr);
        arith_expr_to_bv e1
    | NatToBv (Land e1 e2) | (Land e1 e2) ->
        apply_lemma (`int2bv_logand);
        apply_lemma (`cong_bvand);
        arith_expr_to_bv e1;
        arith_expr_to_bv e2
    | NatToBv (Lxor e1 e2) | (Lxor e1 e2) ->
        apply_lemma (`int2bv_logxor);
        apply_lemma (`cong_bvxor);
        arith_expr_to_bv e1;
        arith_expr_to_bv e2
    | NatToBv (Lor e1 e2) | (Lor e1 e2) ->
        apply_lemma (`int2bv_logor);
        apply_lemma (`cong_bvor);
        arith_expr_to_bv e1;
        arith_expr_to_bv e2
    | NatToBv (Ladd e1 e2) | (Ladd e1 e2) ->
        apply_lemma (`int2bv_add);
        apply_lemma (`cong_bvadd);
        arith_expr_to_bv e1;
        arith_expr_to_bv e2
    | NatToBv (Lsub e1 e2) | (Lsub e1 e2) ->
        apply_lemma (`int2bv_sub);
        apply_lemma (`cong_bvsub);
        arith_expr_to_bv e1;
        arith_expr_to_bv e2
    | _ ->
        trefl ()

let arith_to_bv_tac () : Tac unit =
    // norm [simpl];
    let g = cur_goal () in
    let f = term_as_formula g in
    match f with
    | Comp (Eq _) l r ->
     admit (); // coverage...
     begin match run_tm (as_arith_expr l) with
      | Inl s ->
          dump s;
          trefl ()
      | Inr e ->
            // dump "inr arith_to_bv";
            seq (fun () -> arith_expr_to_bv e) trefl
        end
    | _ ->
        fail ("impossible: ")

(* As things are right now, we need to be able to parse NatToBv
too. This can be useful, if we have mixed expressions so I'll leave it
as is for now *)
[@plugin]
let bv_tac ()  =
  mapply (`eq_to_bv);
  mapply (`trans);
  arith_to_bv_tac ();
  arith_to_bv_tac ();
  set_options "--smtencoding.elim_box true";
  norm [delta] ;
  smt ()

let bv_tac_lt n =
  // apply_lemma (fun () -> `(lt_to_bv #n));
  // dump "after lt_to_bv";
  apply_lemma (quote (trans_lt2 #n));
  arith_to_bv_tac ();
  arith_to_bv_tac ();
  set_options "--smtencoding.elim_box true";
  smt ()

let to_bv_tac ()  =
  apply_lemma (`eq_to_bv);
  apply_lemma (`trans);
  arith_to_bv_tac ();
  arith_to_bv_tac ()

/// U64.t is isomporphic to uint_t 64
/// These next few lemmas use this isomorphism to lift bitwise operations on
/// U64.t to the corresponding operations on uint_t 64

/// First, a lemmas showing that U64.v is injective
let v64_eq (x y: U64.t) : Lemma
  (requires (U64.v x == U64.v y))
  (ensures (x == y))
  = ()


/// v (logand x y) = U64.logand (v x) (v y)
///    -- Note, this is written with an explicit instantiation of the type
///       of `==` (i.e., eq2) since, F* by default, picks only a provablye equivalent
///       type, not a definitionally equal one, which leads to some inefficiencies in tactics
///       where these lemmas are applied repeatedly
let unfold_logand64 (x y: U64.t) : Lemma
  (eq2 #(uint_t U64.n) (U64.v (U64.logand x y))
                       (logand #64 (U64.v x) (U64.v y)))
  = ()

/// v (logor x y) = U64.logor (v x) (v y)
let unfold_logor64 (x y: U64.t) : Lemma
  (eq2 #(uint_t U64.n) (U64.v (U64.logor x y))
                       (logor #64 (U64.v x) (U64.v y)))
  = ()

/// v (logxor x y) = U64.logxor (v x) (v y)
let unfold_logxor64 (x y: U64.t) : Lemma
  (eq2 #(uint_t U64.n) (U64.v (U64.logxor x y))
                       (logxor #64 (U64.v x) (U64.v y)))
  = ()

/// ... add more of your own

/// Now, here's a tactic that will try to rewrite the goal
/// using one of the above three lemmas or fail
let unfold64 () : Tac unit =
  or_else (fun () -> mapply (`unfold_logand64))
          (fun () -> or_else (fun () -> mapply (`unfold_logor64))
                             (fun () -> mapply (`unfold_logxor64)))

let aux () : Tac unit = or_else unfold64 (fun () -> fail "SKIP")

/// Finally, a tactic for bitwise operations on U64.t
[@plugin]
let bv64_tac () : Tac unit =
    //introduce a single `v e = v e'` at the top, if the goal is a U64.t equality
    mapply (`v64_eq);
    norm [];
    //proceed top-down through the goal recursively rewriting to `uint_t 64` further
    // if unfold64 fails, then just skip rewriting this node.
    pointwise' aux;
    norm [];
    //call bv_tac to encode the whole thing to bit vectors
    bv_tac ()
