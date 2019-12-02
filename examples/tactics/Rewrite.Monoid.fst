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
module Rewrite.Monoid
open FStar.Algebra.Monoid
open FStar.List
open FStar.Tactics
open FStar.Reflection
open FStar.Tactics.CanonMonoid


let is_reifiable (m_mult:term) (m_unit:term) (me:term) : Tac bool =
  let hd, tl = collect_app_ref me in
   match inspect hd with
   | Tv_FVar fv ->
      // if unify (pack (Tv_FVar fv)) (quote (Monoid?.mult m)) then -- doesn't work
     let t1 = norm_term [delta;zeta;iota] (pack (Tv_FVar fv)) in
     term_eq t1 m_mult
   | _ ->
     term_eq (norm_term [delta;zeta;iota] me) m_unit

let aux (#a:Type) (#rhs:a) (#lhs:a) (_:squash (lhs == rhs)) : Lemma (lhs == rhs) = ()

let monoid_reflect_rhs (a:Type) (m:monoid a) (rhs:exp a) (lhs:a)
    (_ : squash (lhs == mdenote m rhs))
    : Lemma (lhs == mldenote m (flatten rhs)) =
  flatten_correct m rhs

let replace_point (#a:Type) (m:monoid a) (rhs:exp a) =
   focus (fun () -> 
     let t =
       mk_app (`monoid_reflect_rhs) 
              [(quote a, Q_Explicit);
               (quote m, Q_Explicit);
               (quote rhs, Q_Explicit)] in
     (* dump "before replace point"; *)
     apply_lemma t;
     (* dump "after replace point"; *)
     norm [delta;primops;zeta;iota];
     (* dump "after replace norm"; *)
     trefl ())

let should_rewrite (#a:Type) (m:monoid a) (everywhere:bool) (t:term) : Tac (bool * int) =
  let m_mult = norm_term [delta;zeta;iota] (quote (Monoid?.mult m)) in
  let m_unit = norm_term [delta;zeta;iota] (quote (Monoid?.unit m)) in
  // debug "should_rewrite: ";
  // debug (term_to_string t);
  if is_reifiable m_mult m_unit t
  then true, (if everywhere then 1 else 2)
  else false, 0

let rewrite_monoid (#a:Type) (m:monoid a) () : Tac unit =
  norm [zeta;iota];
  let g = cur_goal () in
  match term_as_formula g with
  | Comp (Eq (Some t)) lhs _ ->
      debug (term_to_string g);
      if term_eq t (quote a) then
        // let _ = dump "Trying canon ... " in
        let lhs_exp : exp a = reification m lhs in
        replace_point m lhs_exp
        // dump "change"
      else trefl ()
  | _ ->
    fail "Unexpected goal to rewriter"

let rewrite_int (everywhere:bool) =
        topdown_rewrite 
          (should_rewrite int_plus_monoid everywhere)
          (rewrite_monoid int_plus_monoid)

let elim_implies #p #q  (_:(p ==> q)) (_:p) : squash q = ()
let apply_imp (h:binder) =
    mapply (mk_app (`elim_implies) [(pack (Tv_Var (bv_of_binder h)), Q_Explicit)])
let refl (#a:Type) (x:a) : (x==x) = FStar.Squash.return_squash Refl
let test (a b : int) (p:Type) =
    assert ((((a + b + 0) == (a + b)) ==> p) ==> p)
        by (norm [];
            rewrite_int true;
            apply_imp (implies_intro());
            norm [delta; zeta;iota; primops];
            apply (`refl))
    
(* TODO: should extend this to a commutative monoid and
         sort the list to prove things like a + b = b + a; *)

