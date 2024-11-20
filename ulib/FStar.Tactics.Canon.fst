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
module FStar.Tactics.Canon

open FStar.Reflection.V2
open FStar.Tactics.V2.Bare
open FStar.Reflection.V2.Arith
open FStar.Mul
module O = FStar.Order
open FStar.Tactics.Canon.Lemmas

let step (t : unit -> Tac unit) : Tac unit =
    apply_lemma (`trans);
    t ()

let step_lemma (lem : term) : Tac unit =
    step (fun () -> apply_lemma lem)

val canon_point : expr -> Tac expr
let rec canon_point e =
    let skip () : Tac expr = 
        trefl (); e
    in
    match e with
    // Evaluate constants
    | Plus (Lit a) (Lit b) ->
        norm [primops];
        trefl ();
        Lit (a + b)

    | Mult (Lit a) (Lit b) ->
        norm [delta; primops]; // Need delta to turn op_Star into op_Multiply, as there's no primop for it
        trefl ();
        Lit (a * b)

    // Forget about negations
    | Neg e ->
        step_lemma (`neg_minus_one);
        canon_point (Mult (Lit (-1)) e)

    // Distribute
    | Mult a (Plus b c) ->
        step_lemma (`distr);
        step_lemma (`cong_plus);
        let l = canon_point (Mult a b) in
        let r = canon_point (Mult a c) in
        canon_point (Plus l r)

    | Mult (Plus a b) c ->
        step_lemma (`distl);
        step_lemma (`cong_plus);
        let l = canon_point (Mult a c) in
        let r = canon_point (Mult b c) in
        canon_point (Plus l r)

    // Associate to the left
    | Mult a (Mult b c) ->
        step_lemma (`ass_mult_l);
        step_lemma (`cong_mult);
        let l = canon_point (Mult a b) in
        let r = canon_point c in
        canon_point (Mult l r)

    | Plus a (Plus b c) ->
        step_lemma (`ass_plus_l);
        step_lemma (`cong_plus);
        let l = canon_point (Plus a b) in
        let r = canon_point c in
        canon_point (Plus l r)

    | Plus (Plus a b) c ->
        if O.gt (compare_expr b c)
        then begin
            step_lemma (`sw_plus);
            apply_lemma (`cong_plus);
            let l = canon_point (Plus a c) in
            trefl() ;
            Plus l b
        end
        else skip ()

    | Mult (Mult a b) c ->
        if O.gt (compare_expr b c)
        then begin
            step_lemma (`sw_mult);
            apply_lemma (`cong_mult);
            let l = canon_point (Mult a c) in
            trefl ();
            Mult l b
        end
        else skip ()

    | Plus a (Lit 0) ->
        apply_lemma (`x_plus_zero);
        a

    | Plus (Lit 0) b ->
        apply_lemma (`zero_plus_x);
        b

    | Plus a b ->
        if O.gt (compare_expr a b)
        then (apply_lemma (`comm_plus); Plus b a)
        else skip ()

    | Mult (Lit 0) _ ->
        apply_lemma (`zero_mult_x);
        Lit 0

    | Mult _ (Lit 0) ->
        apply_lemma (`x_mult_zero);
        Lit 0

    | Mult (Lit 1) r ->
        apply_lemma (`one_mult_x);
        r

    | Mult l (Lit 1) ->
        apply_lemma (`x_mult_one);
        l

    | Mult a b ->
        if O.gt (compare_expr a b)
        then (apply_lemma (`comm_mult); Mult b a)
        else skip ()

    // Forget about subtraction
    | Minus a b ->
        step_lemma (`minus_is_plus);
        step_lemma (`cong_plus);
        trefl ();
        let negb = match b with | Lit n -> Lit (-n) | _ -> Neg b in
        // ^ We need to take care wrt literals, since an application (- N)
        // will get reduced to the literal -N and then neg_minus_one will not
        // apply.
        let r = canon_point negb in
        canon_point (Plus a r)

    | _ ->
        skip ()

// On canon_point_entry, we interpret the LHS of the goal as an
// arithmetic expression, of which we keep track in canon_point so we
// avoid reinterpreting the goal, which gives a good speedup.
//
// However, we are repeating work between canon_point_entry calls, since
// in (L + R), we are called once for L, once for R, and once for the
// sum which traverses both (their canonized forms, actually).
//
// The proper way to solve this is have some state-passing in pointwise,
// maybe having the inner tactic be of type (list a -> tactic a), where
// the list is the collected results for all child calls.
let canon_point_entry () : Tac unit =
    norm [primops];
    let g = cur_goal () in
    match term_as_formula g with
    | Comp (Eq _) l r ->
        begin match run_tm (is_arith_expr l) with
        | Inr e -> (let _e = canon_point e in ())
        | Inl _ -> trefl ()
        end
    | _ ->
        fail ("impossible: " ^ term_to_string g)

let canon () : Tac unit =
    pointwise canon_point_entry
