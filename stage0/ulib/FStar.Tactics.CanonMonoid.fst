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
module FStar.Tactics.CanonMonoid

open FStar.Algebra.Monoid
open FStar.List
open FStar.Reflection.V2
open FStar.Tactics.V2

private
let term_eq = FStar.Reflection.TermEq.Simple.term_eq

(* Only dump when debugging is on *)
let dump m = if debugging () then dump m

(* "A Monoid Expression Simplifier" ported from
   http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html *)

type exp (a:Type) : Type =
  | Unit : exp a
  | Var : a -> exp a
  | Mult : exp a -> exp a -> exp a

let rec exp_to_string (#a:Type) (a_to_string:a->string) (e:exp a) =
  match e with
  | Unit -> "Unit"
  | Var x -> "Var " ^ a_to_string x
  | Mult e1 e2 -> "Mult (" ^ exp_to_string a_to_string e1
                   ^ ") (" ^ exp_to_string a_to_string e2 ^ ")"

let rec mdenote (#a:Type) (m:monoid a) (e:exp a) : a =
  match e with
  | Unit -> Monoid?.unit m
  | Var x -> x
  | Mult e1 e2 -> Monoid?.mult m (mdenote m e1) (mdenote m e2)

let rec mldenote (#a:Type) (m:monoid a) (xs:list a) : a =
  match xs with
  | [] -> Monoid?.unit m
  | [x] -> x
  | x::xs' -> Monoid?.mult m x (mldenote m xs')

let rec flatten (#a:Type) (e:exp a) : list a =
  match e with
  | Unit -> []
  | Var x -> [x]
  | Mult e1 e2 -> flatten e1 @ flatten e2

(* This proof internally uses the monoid laws; the SMT solver picks up
   on them because they are written as squashed formulas in the
   definition of monoid; need to be careful with this since these are
   quantified formulas without any patterns. Dangerous stuff! *)
let rec flatten_correct_aux (#a:Type) (m:monoid a) ml1 ml2 :
  Lemma (mldenote m (ml1 @ ml2) == Monoid?.mult m (mldenote m ml1)
                                                  (mldenote m ml2)) =
  match ml1 with
  | [] -> ()
  | e::es1' -> flatten_correct_aux m es1' ml2

let rec flatten_correct (#a:Type) (m:monoid a) (e:exp a) :
    Lemma (mdenote m e == mldenote m (flatten e)) =
  match e with
  | Unit | Var _ -> ()
  | Mult e1 e2 -> flatten_correct_aux m (flatten e1) (flatten e2);
                  flatten_correct m e1; flatten_correct m e2

let monoid_reflect (#a:Type) (m:monoid a) (e1 e2:exp a)
    (_ : squash (mldenote m (flatten e1) == mldenote m (flatten e2)))
    : squash (mdenote m e1 == mdenote m e2) =
  flatten_correct m e1; flatten_correct m e2

// This expects that mult, unit, and me have already been normalized
let rec reification_aux (#a:Type) (mult unit me : term) : Tac (exp a) =
  let hd, tl = collect_app_ref me in
  let tl = list_unref tl in
  match inspect hd, tl with
  | Tv_FVar fv, [(me1, Q_Explicit) ; (me2, Q_Explicit)] ->
    if term_eq_old (pack (Tv_FVar fv)) mult
    then Mult (reification_aux mult unit me1) (reification_aux mult unit me2)
    else Var (unquote me)
  | _, _ ->
    if term_eq_old me unit
    then Unit
    else Var (unquote me)

let reification (#a:Type) (m:monoid a) (me:term) : Tac (exp a) =
    let mult = norm_term [delta;zeta;iota] (quote (Monoid?.mult m)) in
    let unit = norm_term [delta;zeta;iota] (quote (Monoid?.unit m)) in
    let me   = norm_term [delta;zeta;iota] me in
    // dump ("mult = " ^ term_to_string mult ^
    //     "; unit = " ^ term_to_string unit ^
    //     "; me   = " ^ term_to_string me);
    reification_aux mult unit me

let canon_monoid (#a:Type) (m:monoid a) : Tac unit =
  norm [];
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq (Some t)) me1 me2 ->
      (* First, make sure we have an equality at type ta, since otherwise
      we will fail to apply the reflection Lemma. We can just cut by the equality
      we want, since they should be equiprovable (though not equal). *)
      let b = tcut (`(squash (eq2 #(`#(quote a)) (`#me1) (`#me2)))) in
      smt (); // let the SMT prove it, it should really be trivial

      let r1 = reification m me1 in
      let r2 = reification m me2 in
      change_sq (quote (eq2 #a (mdenote m r1) (mdenote m r2)));
      apply (`monoid_reflect);
      norm [delta_only [`%mldenote;
                        `%flatten;
                        `%FStar.List.Tot.op_At;
                        `%FStar.List.Tot.append]]
  | _ -> fail "Goal should be an equality"
