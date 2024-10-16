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
module FStar.Tactics.BV

open FStar.Tactics.V2.Bare
open FStar.Tactics.MApply0
open FStar.Reflection.V2.Formula
open FStar.Reflection.V2.Arith
open FStar.BV
open FStar.UInt
open FStar.Tactics.BV.Lemmas

// using uint_t' instead of uint_t breaks the tactic (goes to inl).

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

let arith_to_bv_tac () : Tac unit = focus (fun () ->
    norm [delta_only ["FStar.BV.bvult"]];
    let g = cur_goal () in
    let f = term_as_formula g in
    match f with
    | Comp (Eq _) l r ->
     begin match run_tm (as_arith_expr l) with
      | Inl s ->
          dump s;
          trefl ()
      | Inr e ->
            // dump "inr arith_to_bv";
            seq (fun () -> arith_expr_to_bv e) trefl
        end
    | _ ->
        fail ("arith_to_bv_tac: unexpected: " ^ term_to_string g)
)

(* As things are right now, we need to be able to parse NatToBv
too. This can be useful, if we have mixed expressions so I'll leave it
as is for now *)
let bv_tac () = focus (fun () ->
  mapply0 (`eq_to_bv);
  mapply0 (`trans);
  arith_to_bv_tac ();
  arith_to_bv_tac ();
  set_options "--smtencoding.elim_box true";
  norm [delta] ;
  smt ()
)

let bv_tac_lt n = focus (fun () ->
  let nn = pack (Tv_Const (C_Int n)) in
  let t = mk_app (`trans_lt2) [(nn, Q_Implicit)] in
  apply_lemma t;
  arith_to_bv_tac ();
  arith_to_bv_tac ();
  set_options "--smtencoding.elim_box true";
  smt ()
)

let to_bv_tac ()  = focus (fun () ->
  apply_lemma (`eq_to_bv);
  apply_lemma (`trans);
  arith_to_bv_tac ();
  arith_to_bv_tac ()
)
