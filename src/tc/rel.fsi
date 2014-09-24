(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"
module Microsoft.FStar.Tc.Rel

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Tc.Env
open Microsoft.FStar.Absyn.Syntax

(* relations on types, kinds, etc. *)
type guard_t = 
  | Trivial
  | NonTrivial of formula
  
val new_kvar: Range.range -> binders -> knd * uvar_k
val new_tvar: Range.range -> binders -> knd -> typ * typ
val new_evar: Range.range -> binders -> typ -> exp * exp
val new_cvar: Range.range -> binders -> typ -> comp * typ


(* private *)
//val is_trivial: typ -> bool 
//val simplify_guard: env -> guard_t -> guard_t
//val subst_binder: binder -> binder -> subst -> subst
//
//type rel = 
//  | EQ 
//  | SUB
//type prob = 
//  | KProb of rel * knd * knd 
//  | TProb of rel * typ * typ
//  | EProb of rel * exp * exp 
//  | CProb of rel * comp * comp 
//val prob_to_string: env -> prob -> string
//
//type reason = string
//type uvar_inst =  //never a uvar in the co-domain of this map
//  | UK of uvar_k * knd 
//  | UT of (uvar_t * knd) * typ 
//  | UE of (uvar_e * typ) * exp
//  | UC of (uvar_t * knd) * typ
//type worklist = {
//    attempting: list<prob>;
//    deferred: list<(int * prob * reason)>;
//    subst: list<uvar_inst>;
//    top_t: option<typ>;      //the guard is either trivial; or a type of kind top_t => Type, where None => Type = Type and (Some t) => Type = t => Type
//    guard: guard_t;
//    ctr: int;
//}
//type solution = 
//    | Success of list<uvar_inst> * guard_t
//    | Failed of list<(int * prob * reason)>
//type match_result = 
//  | MisMatch
//  | HeadMatch
//  | FullMatch
//type flex_t = (typ * uvar_t * knd * args)
//type im_or_proj_t = ((uvar_t * knd) * list<arg> * binders * ((list<ktec> -> typ) * (typ -> bool) * list<(binders * ktec)>))
//type im_or_proj_k = (uvar_k * list<arg> * binders * ((list<ktec> -> knd) *  list<(binders * ktec)>))
//type uvis = list<uvar_inst>
//val guard : env -> bool -> guard_t -> worklist -> worklist
//val commit: env -> uvis -> unit
//val compress_k: env -> uvis -> knd -> knd
//val compress: env -> uvis -> typ -> typ
//val compress_e: env -> uvis -> exp -> exp
//val comp_comp: env -> uvis -> comp -> comp
//val head_matches_delta: env -> typ -> typ -> (match_result * option<(typ * typ)>)
//val pat_vars: env -> binders -> args -> option<binders>
//val decompose_binder: binders -> ktec -> (binders -> ktec -> 'a) ->  ((list<ktec> -> 'a) * list<(binders * ktec)>) 
//val decompose_kind: env -> knd -> (list<ktec> -> knd) * list<(binders*ktec)>
//val decompose_typ:env -> typ -> (list<ktec> -> typ) * (typ -> bool) * list<(binders * ktec)>
//val solve: bool -> env -> worklist -> solution
//val solve_t: bool -> env -> rel -> typ -> typ -> worklist -> solution
//val solve_k: bool -> env -> rel -> knd -> knd -> worklist -> solution
//val solve_c: bool -> env -> rel -> comp -> comp -> worklist -> solution
//val solve_e: bool -> env -> rel -> exp -> exp -> worklist -> solution
//val imitate: env -> worklist -> im_or_proj_t -> solution
//val project: env -> worklist -> int -> im_or_proj_t -> solution
//val imitate_k: bool -> env -> worklist -> im_or_proj_k -> solution 
//val solve_binders: env -> binders -> binders -> rel -> prob -> worklist 
//               -> (list<subst_elt> -> list<prob> -> solution)
//               -> solution 
//val solve_t_flex_flex: bool -> env -> prob -> flex_t -> flex_t -> worklist -> solution
//val solve_t_flex_rigid: bool -> env -> prob -> flex_t -> typ -> worklist -> solution 
//   

val guard_to_string : env -> guard_t -> string
val trivial : guard_t -> unit
val conj_guard: guard_t -> guard_t -> guard_t
val keq : env -> option<typ> -> knd -> knd -> guard_t
val subkind: env -> knd -> knd -> guard_t
val teq : env -> typ -> typ -> guard_t
val try_subtype: env -> typ -> typ -> option<guard_t>
val subtype: env -> typ -> typ -> guard_t
val trivial_subtype: env -> option<exp> -> typ -> typ -> unit
val sub_comp: env -> comp -> comp -> option<guard_t>