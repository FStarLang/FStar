(*
   Copyright 2023 Microsoft Research

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

module PulseSyntaxExtension.SyntaxWrapper
open FStarC
open FStarC.Ident
let range = FStarC.Range.range
let var = nat
let index = nat

val universe: Type0
val u_zero : universe
val u_succ (u:universe) : universe
val u_var (s:string) : universe
val u_max (u0 u1:universe) : universe
val u_unknown : universe

new val bv : Type0
val mk_bv (i:index) (name:string) (r:range) : bv
val index_of_bv (bv:bv) : index
new val nm : Type0
val mk_nm (i:index) (name:string) (r:range) : nm

new val fv : Type0
val mk_fv (nm:lident) (r:range) : fv

new val qualifier : Type0
val as_qual (imp:bool)  : option qualifier
val tc_qual : option qualifier
let term : Type0 = FStarC.Syntax.Syntax.term (* pulse terms are just F* terms *)
new val binder : Type0 (* pulse binder *)
new val comp : Type0 (* pulse comp *)
val meta_qual : term -> option qualifier
let slprop = term
val mk_binder (x:ident) (t:term) : binder
val mk_binder_with_attrs (x:ident) (t:term) (attrs:list term) : binder

val tm_bvar (bv:bv) : term
val tm_var (x:nm) : term
val tm_fvar (x:fv) : term
val tm_uinst (l:fv) (us:list universe) : term
val tm_emp (_:range) : term
val tm_pure (p:term) (_:range) : term
val tm_star (p0 p1:term) (_:range) : term
val tm_exists (b:binder) (body:slprop) (_:range)  : term
val tm_forall (b:binder) (body:slprop) (_:range)  : term
val tm_arrow (b:binder) (q:FStarC.Syntax.Syntax.aqual) (body:comp) (_:range)  : term
val tm_expr (t:FStarC.Syntax.Syntax.term) (_:range) : term
val tm_unknown (_:range)  : term
val tm_emp_inames : term 
val mk_tot (t:term) : comp
val mk_comp (pre:term) (ret:binder) (post:term) : comp
val ghost_comp (opens:term) (pre:term) (ret:binder) (post:term) : comp
val atomic_comp (opens:term) (pre:term) (ret:binder) (post:term) : comp
val unobs_comp (opens:term) (pre:term) (ret:binder) (post:term) : comp

val is_tm_exists (x:term) : bool

val hint_type : Type0
val mk_wild_hint_type : hint_type
val mk_show_proof_state_hint_type (r:range) : hint_type
val mk_assert_hint_type (vp:slprop) : hint_type
val mk_unfold_hint_type (l:option (list string)) (vp:slprop) : hint_type
val mk_fold_hint_type (l:option (list string)) (vp:slprop) : hint_type
val mk_rename_hint_type (l:list (term & term)) (goal:option slprop) (tac_opt : option term) : hint_type
val mk_rewrite_hint_type (p1:term) (p2:term) (tac_opt : option term) : hint_type

new val constant : Type0
val inspect_const : FStarC.Const.sconst -> constant

new val pattern : Type0
val pat_var (ppname:string) (_:range) : pattern
val pat_constant (c:constant) (_:range) : pattern
val pat_cons (head:fv) (ps:list pattern) (_:range) : pattern

new val st_term : Type0
type branch
val mk_branch : pattern -> st_term -> norw:bool -> branch
val tm_return (t:term) (_:range) : st_term
val tm_ghost_return (t:term) (_:range) : st_term
val tm_abs (b:binder) (q:option qualifier) (_:option comp) (body:st_term) (_:range) : st_term
val tm_st_app (head:term) (q:FStarC.Syntax.Syntax.aqual) (arg:term) (_:range) : st_term
val tm_bind (x:binder) (e1:st_term) (e2:st_term) (_:range) : st_term
val tm_totbind (x:binder) (e1:term) (e2:st_term) (_:range) : st_term
val tm_let_mut (x:binder) (v:term) (k:st_term) (_:range) : st_term
val tm_let_mut_array (x:binder) (v:term) (n:term) (k:st_term) (_:range) : st_term
val tm_while (head:st_term) (invariant: (ident & slprop)) (body:st_term) (_:range) : st_term 
val tm_if (head:term) (returns_annot:option slprop) (then_ else_:st_term) (_:range) : st_term
val tm_match (head:term) (returns_:option slprop) (brs:list branch) (_:range) : st_term
val tm_intro_exists (vp:slprop) (witnesses:list term) (_:range) : st_term
val is_tm_intro_exists (x:st_term) : bool
val tm_protect (s:st_term) : st_term
val tm_par (p1:term) (p2:term) (q1:term) (q2:term) (b1:st_term) (b2:st_term) (_:range) : st_term
val tm_admit (_:range) : st_term
val tm_unreachable (_:range) : st_term
val tm_proof_hint_with_binders (_:hint_type) (_:list binder) (body:st_term) (_:range) : st_term
val tm_with_inv (iname:term) (body:st_term) (returns_:option (binder & term & term)) (_:range) : st_term
val tm_add_inv (inames:term) (n:term) (_:range) : term
val close_binders (bs:list binder) (xs:list var) : list binder
val close_term (t:term) (v:var) : term
val close_st_term (t:st_term) (v:var) : st_term
val close_st_term_n (t:st_term) (vs:list var) : st_term
val close_comp (t:comp) (v:var) : comp
val close_comp_n (t:comp) (vs:list var) : comp
val comp_pre (c:comp) : term
val comp_res (c:comp) : term
val comp_post (c:comp) : term
val mark_statement_sequence (s:st_term) : st_term
(* ^marks a statement as being the lhs of s1;s2, to perform more checks on it
(type must be unit) *)
val mark_not_source (s:st_term) : st_term

val print_exn (e:exn) : string
val binder_to_string (env:FStarC.TypeChecker.Env.env) (b:binder) : string
val term_to_string (env:FStarC.TypeChecker.Env.env) (_:term) : string
val st_term_to_string (env:FStarC.TypeChecker.Env.env) (_:st_term) : string
val comp_to_string (env:FStarC.TypeChecker.Env.env) (_:comp) : string
val bv_to_string (_:bv) : string
val subst : Type0
val bvs_as_subst (l:list var) : subst
val subst_term (s:subst) (t:term) : term
val subst_st_term (s:subst) (t:st_term) : st_term
val subst_proof_hint (s:subst) (h:hint_type) : hint_type

new
val decl : Type0
val decl_to_string (env:FStarC.TypeChecker.Env.env) (_:decl) : string

val fn_defn :
  range ->
  name:ident ->
  isrec:bool ->
  bs:list (option qualifier & binder & bv) ->
  comp:comp ->
  meas:option term ->
  body:st_term ->
  decl

val fn_decl :
  range ->
  name:ident ->
  bs:list (option qualifier & binder & bv) ->
  comp:comp ->
  decl
