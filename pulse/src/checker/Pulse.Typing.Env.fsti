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

type binding = var & typ
type env_bindings = list binding

// This function is marked ghost because it should not be used as it renames all variables to "x"
let extend_env_l (f:R.env) (g:env_bindings) : GTot R.env =
  L.fold_right
    (fun (x, b) g ->
      RT.extend_env g x b)
     g
     f

val env : Type0

val fstar_env (g:env) : RT.fstar_top_env

//
// most recent binding at the head of the list
//
val bindings (g:env) : env_bindings
val bindings_with_ppname (g:env) : list (ppname & var & typ)

(* Returns an F* reflection environment.
The result is the same as taking the initial F*
environment (fstar_env g) and extending it with
all the bindings, but this is O(1). *)
val elab_env  (g:env) : R.env

val elab_env_lemma (g:env)
  : Lemma (elab_env g == extend_env_l (fstar_env g) (bindings g))
          [SMTPat (elab_env g)]

val fresh_anf (g:env) : T.Tac (env & nat)


val as_map (g:env) : Map.t var typ

val goto_bindings (g:env) : list (var & ppname & comp_st)

let is_related_to (bs:list (var & typ)) (m:Map.t var typ) =
  (forall (b:var & typ).{:pattern L.memP b bs}
          L.memP b bs ==> (Map.contains m (fst b) /\
                           Map.sel m (fst b) == snd b)) /\
  
  (forall (x:var).{:pattern Map.contains m x} Map.contains m x ==> (L.memP (x, Map.sel m x) bs))

val bindings_as_map (g:env)
  : Lemma (bindings g `is_related_to` as_map g)
          [SMTPat (bindings g); SMTPat (as_map g)]

let goto_dom (g: env) : GTot (Set.set var) =
  let rec go xs =
    match xs with
    | [] -> Set.empty
    | (x,_,_)::xs -> Set.add x (go xs)
  in
  go (goto_bindings g)

let var_dom (g: env) : Set.set var = Map.domain (as_map g)

let dom (g:env) : GTot (Set.set var) = Set.union (var_dom g) (goto_dom g)

let equal (g1 g2:env) =
  fstar_env g1 == fstar_env g2 /\
  goto_bindings g1 == goto_bindings g2 /\
  bindings g1 == bindings g2

val equal_elim (g1 g2:env)
  : Lemma (requires equal g1 g2)
          (ensures g1 == g2)
          [SMTPat (equal g1 g2)]

val mk_env (f:RT.fstar_top_env) : g:env { fstar_env g == f }

val mk_env_bs (f:RT.fstar_top_env)
  : Lemma (bindings (mk_env f) == [])
          [SMTPat (bindings (mk_env f))]

val mk_env_goto_bindings (f:RT.fstar_top_env)
  : Lemma (goto_bindings (mk_env f) == [])
          [SMTPat (goto_bindings (mk_env f))]

val mk_env_dom (f:RT.fstar_top_env)
  : Lemma (dom (mk_env f) == Set.empty)
          [SMTPat (dom (mk_env f))]

val push_binding (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : g':env { fstar_env g' == fstar_env g }

val push_goto (g: env) (x: var { ~ (Set.mem x (dom g)) }) (n: ppname) (c: comp_st)
  : g':env { fstar_env g' == fstar_env g }

let singleton_env (f:_) (x:var) (t:typ) = push_binding (mk_env f) x ppname_default t

let push_binding_def (g:env) (x:var { ~ (Set.mem x (dom g)) }) (t:typ)
  = push_binding g x ppname_default t

val dom_push_goto (g: env) x n c
  : Lemma (goto_dom (push_goto g x n c) == Set.add x (goto_dom g))
      [SMTPat (goto_dom (push_goto g x n c))]
val bindings_push_goto (g: env) x n c
  : Lemma (bindings (push_goto g x n c) == bindings g)
      [SMTPat (bindings (push_goto g x n c))]
val as_map_push_goto (g: env) x n c
  : Lemma (as_map (push_goto g x n c) == as_map g)
      [SMTPat (as_map (push_goto g x n c))]

val push_binding_bs (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : Lemma (bindings (push_binding g x n t) == (x, t) :: bindings g)
          [SMTPat (bindings (push_binding g x n t))]

val push_binding_goto_bindings (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : Lemma (goto_bindings (push_binding g x n t) == goto_bindings g)
          [SMTPat (goto_bindings (push_binding g x n t))]

val push_binding_as_map (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : Lemma (as_map (push_binding g x n t) == Map.upd (as_map g) x t)
          [SMTPat (as_map (push_binding g x n t))]

val push_univ_vars (g: env) (us: list R.univ_name) : g':env { g' == g }

let lookup (g:env) (x:var) : option typ =
  let m = as_map g in
  if Map.contains m x then Some (Map.sel m x) else None

let lookup_goto (g: env) (x: var) : option (ppname & comp_st) =
  let go ys =
    match ys with
    | [] -> None
    | (y,n,c)::ys ->
      if x = y then Some (n,c) else None
  in
  go (goto_bindings g)

val fresh (g:env) : Dv (v:var { ~ (Set.mem v (dom g)) })

let contains (g:env) (x:var) = Map.contains (as_map g) x

let disjoint (g1 g2:env) =
  fstar_env g1 == fstar_env g2 /\
  Set.disjoint (dom g1) (dom g2)

let pairwise_disjoint (g g' g'':env) =
  disjoint g g' /\ disjoint g' g'' /\ disjoint g g''

let disjoint_dom (g1 g2:env)
  : Lemma (requires disjoint g1 g2)
          (ensures dom g1 `Set.disjoint` dom g2) = ()

val push_env (g1:env) (g2:env { disjoint g1 g2 }) : env

val push_env_fstar_env (g1:env) (g2:env { disjoint g1 g2 })
  : Lemma (fstar_env (push_env g1 g2) == fstar_env g1)
          [SMTPat (fstar_env (push_env g1 g2))]

val push_env_bindings (g1 g2:env)
  : Lemma (requires disjoint g1 g2)
          (ensures bindings (push_env g1 g2) == bindings g2 @ bindings g1)
          [SMTPat (bindings (push_env g1 g2))]

val push_env_goto_bindings (g1 g2:env)
  : Lemma (requires disjoint g1 g2)
          (ensures goto_bindings (push_env g1 g2) == goto_bindings g2 @ goto_bindings g1)
          [SMTPat (goto_bindings (push_env g1 g2))]

val push_env_as_map (g1 g2:env)
  : Lemma (requires disjoint g1 g2)
          (ensures as_map (push_env g1 g2) == Map.concat (as_map g2) (as_map g1))
          [SMTPat (as_map (push_env g1 g2))]

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
  : Ghost env (requires g1 `env_extends` g2)
             (ensures fun g3 -> extends_with g1 g2 g3)

val env_extends_refl (g:env)
  : Lemma (g `env_extends` g)
          [SMTPat (g `env_extends` g)]

val env_extends_trans (g1 g2 g3:env)
  : Lemma (requires g1 `env_extends` g2 /\ g2 `env_extends` g3)
          (ensures g1 `env_extends` g3)
          [SMTPat (g1 `env_extends` g3); SMTPat (g1 `env_extends` g2)]

val env_extends_push (g:env) (x:var { ~ (Set.mem x (dom g)) }) (n:ppname) (t:typ)
  : Lemma (push_binding g x n t `env_extends` g)
          [SMTPat ((push_binding g x n t) `env_extends` g)]

val extends_with_push (g1 g2 g3:env)
  (x:var { ~ (Set.mem x (dom g1)) }) (n:ppname) (t:typ)
  : Lemma (requires extends_with g1 g2 g3)
          (ensures extends_with (push_binding g1 x n t) g2 (push_binding g3 x n t))
          [SMTPat (extends_with g1 g2 g3);
           SMTPat (push_binding g1 x n t);
           SMTPat (push_binding g3 x n t)]

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
