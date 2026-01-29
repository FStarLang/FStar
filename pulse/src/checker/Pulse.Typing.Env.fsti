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

module Pulse.Typing.Env

open FStar.List.Tot

open Pulse.Syntax

module L = FStar.List.Tot

module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
module Pprint = FStar.Pprint

noeq type var_binding = { n: ppname; x: var; ty: typ }

noeq type binding =
  | BindingVar of var_binding
  | BindingGotoLabel { n: ppname; x: var; post: comp_st }
  | BindingPost { post: term }

let binding_dom : binding -> Set.set var = function
  | BindingVar { x }
  | BindingGotoLabel { x }
    -> Set.singleton x
  | BindingPost ..
    -> Set.empty

type env_bindings = list binding

let bindings_dom (g: env_bindings) : Set.set var =
  L.fold_right (fun b vs -> vs `Set.union` binding_dom b) g Set.empty

let binding_extend_env (f: R.env) : binding -> R.env = function
  | BindingVar { n; x; ty } -> R.push_binding f { ppname = n.name; uniq = x; sort = ty }
  | BindingGotoLabel .. | BindingPost .. -> f

let bindings_extend_env (f:R.env) (g:env_bindings) : R.env =
  L.fold_right (fun b g -> binding_extend_env g b) g f

let comp_add_pre (c: comp_st) (extra: term) =
  with_st_comp c { st_comp_of_comp c with pre = extra `tm_star` comp_pre c }

val env : Type0
val fstar_env (g:env) : RT.fstar_top_env
// most recent binding at the head of the list
val bindings (g:env) : env_bindings

let equal (g1 g2:env) =
  fstar_env g1 == fstar_env g2 /\
  bindings g1 == bindings g2

val equal_elim (g1 g2:env)
  : Lemma (requires equal g1 g2)
          (ensures g1 == g2)
          [SMTPat (equal g1 g2)]

(* Returns an F* reflection environment.
The result is the same as taking the initial F*
environment (fstar_env g) and extending it with
all the bindings, but this is O(1). *)
val elab_env (g:env) : g':R.env { g' == bindings_extend_env (fstar_env g) (bindings g) }

val fresh_anf (g:env) : T.Tac (env & nat)

let dom (g:env) : Set.set var =
  bindings_dom (bindings g)

let freshv (g:env) (x:var) : prop =
  ~(Set.mem x (dom g))

val mk_env (f:RT.fstar_top_env) : g:env {
    fstar_env g == f /\
    bindings g == [] }

val push (g: env) (b: binding { dom g `Set.disjoint` binding_dom b }) : g':env {
    fstar_env g' == fstar_env g /\
    bindings g' == b :: bindings g
  }

let push_binding (g:env) (x:var { freshv g x }) (n:ppname) (ty:typ) =
  push g (BindingVar { n; x; ty })

let push_goto (g: env) (x: var { freshv g x }) (n: ppname) (c: comp_st) =
  push g (BindingGotoLabel { x; n; post = c })

let push_post (g: env) (post: term) =
  push g (BindingPost { post })

let singleton_env (f:_) (x:var) (t:typ) : GTot _ =
  push_binding (mk_env f) x ppname_default t

let push_binding_def (g:env) (x:var { ~ (Set.mem x (dom g)) }) (t:typ) : GTot _
  = push_binding g x ppname_default t

val push_univ_vars (g: env) (us: list R.univ_name) : g':env { g' == g }

val lookup (g: env) (x: var) : option typ

val lookup_fresh g x : Lemma (requires freshv g x) (ensures lookup g x == None) [SMTPat (lookup g x)]

val lookup_push g x (b: binding {dom g `Set.disjoint` binding_dom b}) :
  Lemma (lookup (push g b) x == (match b with
    | BindingVar {n; x=y; ty} -> if x = y then Some ty else lookup g x
    | BindingGotoLabel .. | BindingPost .. -> lookup g x
  )) [SMTPat (lookup (push g b) x)]

val lookup_goto (g: env) (x: var) : option (ppname & comp_st)

val lookup_goto_push g x (b: binding {dom g `Set.disjoint` binding_dom b}) :
  Lemma (lookup_goto (push g b) x == (match b with
    | BindingVar .. -> lookup_goto g x
    | BindingGotoLabel { n; x=y; post } ->
      if x = y then Some (n, post) else lookup_goto g x
    | BindingPost { post } ->
      match lookup_goto g x with
      | None -> None
      | Some (n, post0) -> Some (n, comp_add_pre post0 post)
  )) [SMTPat (lookup (push g b) x)]

val fresh (g:env) : Dv (v:var { freshv g v })

let contains_var (g: env) (x: var) =
  L.existsb (function
    | BindingVar {x=y} -> x = y
    | _ -> false) (bindings g)

let disjoint (g1 g2:env) =
  fstar_env g1 == fstar_env g2 /\
  Set.disjoint (dom g1) (dom g2)

let pairwise_disjoint (g g' g'':env) =
  disjoint g g' /\ disjoint g' g'' /\ disjoint g g''

let disjoint_dom (g1 g2:env)
  : Lemma (requires disjoint g1 g2)
          (ensures dom g1 `Set.disjoint` dom g2) = ()

val push_env (g1:env) (g2:env { disjoint g1 g2 }) :
  g':env { fstar_env g' == fstar_env g1 /\ bindings g' == bindings g2 @ bindings g1 }

val push_env_dom g1 g2 : Lemma (dom (push_env g1 g2) == dom g1 `Set.union` dom g2) [SMTPat (dom (push_env g1 g2))]

val push_env_assoc (g1 g2 g3:env)
  : Lemma (requires disjoint g1 g2 /\ disjoint g2 g3 /\ disjoint g3 g1)
          (ensures push_env g1 (push_env g2 g3) == push_env (push_env g1 g2) g3)

// g1 extends g2 with g3, i.e. g1.bs == g3.bs @ g2.bs (recall most recent binding at the head)
let extends_with (g1 g2 g3:env) =
  disjoint g2 g3 /\
  g1 == push_env g2 g3

let env_extends (g1 g2:env) =
  exists g3. extends_with g1 g2 g3

val diff (g1 g2:env)
  : Pure env (requires g1 `env_extends` g2)
             (ensures fun g3 -> extends_with g1 g2 g3)

val env_extends_refl (g:env)
  : Lemma (g `env_extends` g)
          [SMTPat (g `env_extends` g)]

val env_extends_trans (g1 g2 g3:env)
  : Lemma (requires g1 `env_extends` g2 /\ g2 `env_extends` g3)
          (ensures g1 `env_extends` g3)
          [SMTPat (g1 `env_extends` g3); SMTPat (g1 `env_extends` g2)]

val env_extends_push (g:env) (b: binding { dom g `Set.disjoint` binding_dom b })
  : Lemma (push g b `env_extends` g)
          [SMTPat (push g b `env_extends` g)]

val extends_with_push (g1 g2 g3:env)
  (x:var { ~ (Set.mem x (dom g1)) }) (n:ppname) (t:typ)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures extends_with (push_binding g1 x n t) g2 (push_binding g3 x n t))
          [SMTPat (extends_with g1 g2 g3);
           SMTPat (push_binding g1 x n t);
           SMTPat (push_binding g3 x n t)]

let rec clear_goto_bindings : env_bindings -> env_bindings = function
  | [] -> []
  | BindingVar v :: bs -> BindingVar v :: clear_goto_bindings bs
  | _ :: bs -> clear_goto_bindings bs

val clear_goto (g: env) : g':env {
    fstar_env g' == fstar_env g /\
    elab_env g' == elab_env g /\
    bindings g' == clear_goto_bindings (bindings g) /\
    dom g' `Set.subset` dom g
  }

val push_context (g:env) (ctx:string) (r:range) : g':env { g' == g }
val push_context_no_range (g:env) (ctx:string) : g':env { g' == g }
val reset_context (g:env) (use_context_from:env) : g':env{ g' == g}
val get_context (g:env) : Pulse.RuntimeUtils.context
val range_of_env (g:env) : T.Tac range
val print_context (g:env) : T.Tac string
val env_to_string (g:env) : T.Tac string
val env_to_doc' (simplify:bool) (g:env) : T.Tac FStar.Pprint.document
val env_to_doc (g:env) : T.Tac FStar.Pprint.document
val get_range (g:env) (r:option range) : T.Tac range

val fail_doc_env (#a:Type) (with_env:bool)
                 (g:env) (r:option range) (msg:list Pprint.document)
  : T.TacH a (requires True) (ensures fun _ -> False)

let fail_doc (#a:Type) (g:env) (r:option range) (msg:list Pprint.document)
  : T.TacH a (requires True) (ensures fun _ -> False)
  = fail_doc_env false g r msg

val warn_doc (g:env) (r:option range) (msg:list Pprint.document)
  : T.Tac unit

val info_doc (g:env) (r:option range) (msg:list Pprint.document)
  : T.Tac unit

val info_doc_env (g:env) (r:option range) (msg:list Pprint.document)
  : T.Tac unit

val fail (#a:Type) (g:env) (r:option range) (msg:string) 
  : T.TacH a (requires True) (ensures fun _ -> False)

val warn (g:env) (r:option range) (msg:string)
  : T.Tac unit

val info (g:env) (r:option range) (msg:string)
  : T.Tac unit

val fail_doc_with_subissues #a (g:env) (ro : option range)
  (sub : list Issue.issue)
  (msg : list Pprint.document)
  : T.TacH a (requires True) (ensures fun _ -> False)

val info_doc_with_subissues (g:env) (r:option range)
  (sub : list Issue.issue)
  (msg : list Pprint.document)
  : T.Tac unit
