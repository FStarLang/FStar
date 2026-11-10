(*
   Copyright 2008-2025 Microsoft Research

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
module FStarC.TypeChecker.TcResolve

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Syntax.Syntax
open FStarC.Syntax.Print {}
open FStarC.Syntax.Hash {}
open FStarC.TypeChecker.Env
module Env = FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.Class.Show
open FStarC.Class.PP
open FStarC.Class.Setlike
open FStarC.Errors.Msg
open FStarC.Pprint

module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U = FStarC.Syntax.Util
module UF = FStarC.Syntax.Unionfind
module Free = FStarC.Syntax.Free
module Compress = FStarC.Syntax.Compress
module Visit = FStarC.Syntax.Visit
module N = FStarC.TypeChecker.Normalize
module Rel = FStarC.TypeChecker.Rel
module CoreRel = FStarC.TypeChecker.CoreRel
module PC = FStarC.Parser.Const
module HM = FStarC.HashMap
module BU = FStarC.Util
module Listlike = FStarC.Class.Listlike

let dbg = Debug.get_toggle "TcResolve"

(* A safeguard against non-termination only: the search is cut, with a
   warning, after this many steps or at this depth. *)
let max_steps = 100000
let max_depth = 1000

let norm_steps = [Env.Beta; Env.Primops; Env.Iota; Env.UnfoldQual ["unfold"]]

let is_class (env:env) (l:Ident.lident) : ML bool =
  match Env.lookup_attrs_of_lid env l with
  | Some attrs -> List.existsb (U.is_fvar PC.tcclass_lid) attrs
  | None -> false

let is_unfold (env:env) (l:Ident.lident) : ML bool =
  match Env.quals_of_qninfo (Env.lookup_qname env l) with
  | Some qs -> List.existsb (function Unfold_for_unification_and_vcgen -> true | _ -> false) qs
  | None -> false

let head_fv (t:term) : ML (option (fv & term & args)) =
  let hd, args = U.head_and_args_full t in
  match (SS.compress (U.un_uinst hd)).n with
  | Tm_fvar fv -> Some (fv, hd, args)
  | _ -> None

let rec class_of_typ' (fuel:int) (env:env) (t:typ) : ML (option Ident.lident) =
  let t = U.unrefine (SS.compress t) in
  match (SS.compress t).n with
  | Tm_arrow _ ->
    let _, c = U.arrow_formals_comp_strict t in
    if U.is_tot_or_gtot_comp c
    then class_of_typ' fuel env (U.comp_result c)
    else None
  | _ ->
    match head_fv t with
    | None -> None
    | Some (fv, _, _) ->
      let l = S.lid_of_fv fv in
      if is_class env l then Some l
      else if fuel > 0 && is_unfold env l
      then class_of_typ' (fuel - 1) env (N.normalize (Env.HNF :: Env.Weak :: norm_steps) env t)
      else None

let class_of_typ (env:env) (t:typ) : ML (option Ident.lident) =
  class_of_typ' 8 env t

(* The global instances, with their classes, most recent first.  Computed
   once for each [tc_global] scope, which is replaced whenever an instance is
   added. *)
let global_instances_cache
  : ref (option (ref (HM.t term (option (list univ_name & term & typ))) & list (Ident.lident & Ident.lident)))
  = mk_ref None

let global_instances (env:env) : ML (list (Ident.lident & Ident.lident)) =
  match !global_instances_cache with
  | Some (r, l) when BU.physical_equality r env.tc_global.tc_cache -> l
  | _ ->
    let l =
      Env.lookup_attr env (Ident.string_of_lid PC.tcinstance_lid)
      |> List.collect (fun se ->
           U.lids_of_sigelt se |> List.collect (fun lid ->
             match Env.try_lookup_lid env lid with
             | None -> []
             | Some ((_, t), _) ->
               match class_of_typ env t with
               | Some cls -> [(cls, lid)]
               | None -> []))
    in
    global_instances_cache := Some (env.tc_global.tc_cache, l);
    l

(* The cache works modulo universe unification variables, which are
   created afresh for every instance that is tried: they are erased from
   the keys, and cached results are instantiated with fresh ones on every
   hit, before [try_teq] unifies them with the goal. Unsolved universe
   variables are unconstrained, so a failure for one of them is a failure
   for all. *)
let erase_univ_uvars (t:term) : ML term =
  Visit.visit_term_univs false (fun t -> t)
    (fun u -> match u with U_unif _ -> U_unknown | _ -> u) t

(* Cached results cannot keep universe uvars: the transaction that created
   them may be rolled back, after which the union-find rejects them. They
   are replaced by private universe names when storing ... *)
let abstract_univ_uvars (e ty:term) : ML (list univ_name & term & term) =
  let m : ref (list (int & univ_name)) = mk_ref [] in
  let fu (u:universe) : ML universe =
    match u with
    | U_unif uv ->
      let id = UF.univ_uvar_id uv in
      (match List.assoc id !m with
       | Some x -> U_name x
       | None ->
         let x = Ident.mk_ident ("'tcu" ^ show (List.length !m), Range.dummyRange) in
         m := (id, x) :: !m;
         U_name x)
    | _ -> u
  in
  let e = Visit.visit_term_univs false (fun t -> t) fu e in
  let ty = Visit.visit_term_univs false (fun t -> t) fu ty in
  List.map snd !m, e, ty

(* ... and instantiated with fresh uvars on every hit. *)
let instantiate_univ_names (xs:list univ_name) (e ty:term) : ML (term & term) =
  if Nil? xs then e, ty else
  let m = List.map (fun x -> x, Env.new_u_univ ()) xs in
  let fu (u:universe) : ML universe =
    match u with
    | U_name x ->
      (match List.tryFind (fun (y, _) -> Ident.ident_equals x y) m with
       | Some (_, u') -> u'
       | None -> u)
    | _ -> u
  in
  Visit.visit_term_univs false (fun t -> t) fu e,
  Visit.visit_term_univs false (fun t -> t) fu ty

(* Global state of a search. *)
noeq
type gst = {
  steps  : ref int;
  cuts   : ref int;  (* the number of times the search was cut; results that
                        depend on a cut are not cached *)
  warned : ref bool;
  rng    : Range.t;
}

(* State of a goal. *)
noeq
type st = {
  env   : env;        (* its scope is [scope] *)
  scope : tc_scope;
  seen  : list term;  (* the keys of the goals being solved, to detect loops *)
  depth : int;
}

type result = option (term & list implicit)

let with_scope (env:Env.env) (scope:tc_scope) : Env.env =
  {env with tc_scope = scope; tc_scope_gamma = env.gamma}

let debug (f : unit -> ML string) : ML unit =
  if !dbg then Format.print1 "TcResolve: %s\n" (f ())

let cut (gs:gst) (why:string) : ML unit =
  gs.cuts := !gs.cuts + 1;
  debug (fun () -> "cut: " ^ why);
  if not !gs.warned && why <> "loop" then (
    gs.warned := true;
    Errors.log_issue gs.rng Errors.Warning_TypeclassResolutionBudget [
      text "Typeclass resolution exceeded its budget, the search was cut.";
      text "This usually indicates a loop in your instances."
    ])

let unresolved (u:term) : ML bool =
  match (SS.compress u).n with
  | Tm_uvar _ -> true
  | _ -> false

(* Like the tactic's [apply]: Core decides the equality, so that a
   unification that only succeeds by deferring a problem is rejected. Errors
   count as failures. *)
let try_teq (env:Env.env) (t1 t2:typ) : ML (option guard_t) =
  try CoreRel.try_teq false env t1 t2
  with Errors.Error _ -> None

let guard_imps (g:guard_t) : ML (list implicit) = Listlike.to_list g.implicits

(* [e] as the solution of a fresh uvar of type [goal], to be checked
   against it. *)
let checked (gs:gst) (st:st) (goal:typ) (e:term) : ML result =
  let u, _, g = Env.new_implicit_var_aux "typeclass solution" gs.rng st.env goal Strict None false in
  match Rel.teq_nosmt st.env u e with
  | None -> None
  | Some g' -> Some (u, guard_imps g @ guard_imps g')

let mark_checked (u:term) : ML unit =
  match (SS.compress u).n with
  | Tm_uvar (ctx_u, _) ->
    let dec = UF.find_decoration ctx_u.ctx_uvar_head in
    UF.change_decoration ctx_u.ctx_uvar_head { dec with uvar_decoration_should_check = Already_checked }
  | _ -> ()

let is_unit_or_squash (t:typ) : ML bool =
  let ut = U.unrefine t in
  U.is_unit ut || Some? (U.is_squash ut)

(* Whether an explicit instance argument of this type is solved as a goal. *)
let is_subgoal_typ (env:Env.env) (t:typ) : ML bool =
  is_unit_or_squash t || Some? (class_of_typ env t)

let rec solve (gs:gst) (st:st) (goal:typ) : ML result =
  gs.steps := !gs.steps + 1;
  if !gs.steps > max_steps then (cut gs "steps"; None) else
  if st.depth > max_depth then (cut gs "depth"; None) else
  let st = { st with depth = st.depth + 1 } in
  let goal = N.normalize norm_steps st.env goal in
  debug (fun () -> "goal " ^ show goal);
  match (SS.compress goal).n with
  | Tm_arrow _ ->
    let bs, c = U.arrow_formals_comp_strict goal in
    if not (U.is_tot_or_gtot_comp c) then None else
    let env = Env.push_binders (with_scope st.env st.scope) bs in
    let scope = Env.tc_scope_of env in
    (match solve gs { st with env; scope } (U.comp_result c) with
     | None -> None
     | Some (e, imps) -> Some (U.abs bs e None, imps))
  | _ ->
    let ug = U.unrefine goal in
    if U.is_unit ug || Some? (U.is_squash ug) then checked gs st goal U.exp_unit else
    match (SS.compress goal).n with
    | Tm_refine {b} ->
      (match solve gs st b.sort with
       | None -> None
       | Some (e, imps) ->
         match checked gs st goal e with
         | None -> None
         | Some (u, imps') -> Some (u, imps @ imps'))
    | _ -> solve_class gs st goal

and solve_class (gs:gst) (st:st) (goal:typ) : ML result =
  match head_fv goal with
  | Some (fv, hd, args) when is_class st.env (S.lid_of_fv fv) -> (
    let cls = S.lid_of_fv fv in
    let fds = Rel.class_fundeps st.env cls in
    let key = S.mk_Tm_app hd (args |> List.mapi (fun i (a, q) -> if List.mem i fds then (S.tun, q) else (a, q))) goal.pos in
    if not (is_empty (Free.uvars_uncached key)) then (
      debug (fun () -> "open goal " ^ show goal);
      None
    ) else
    let key = erase_univ_uvars (Compress.deep_compress true true key) in
    if List.existsb (U.term_eq key) st.seen then (cut gs "loop"; None) else
    let cache = st.scope.tc_cache in
    match HM.lookup key !cache with
    | Some None ->
      debug (fun () -> "cached failure " ^ show key);
      None
    | Some (Some (xs, e, ty)) ->
      debug (fun () -> "cached " ^ show key ^ " := " ^ show e);
      let e, ty = instantiate_univ_names xs e ty in
      (match try_teq st.env goal ty with
       | None -> None
       | Some g ->
         match checked gs st goal e with
         | None -> None
         | Some (u, imps) -> Some (u, imps @ guard_imps g))
    | None ->
      let cuts0 = !gs.cuts in
      let tx = UF.new_transaction () in
      let sgoal, imps0 = fresh_fundeps st cls hd args fds in
      let res = search gs { st with seen = key :: st.seen } cls sgoal in
      let clean = !gs.cuts = cuts0 in
      match res with
      | None ->
        UF.rollback tx;
        if clean then cache := HM.add key None !cache;
        None
      | Some (e, imps) ->
        (if clean then
          let e = Compress.deep_compress true true e in
          let sgoal' = Compress.deep_compress true true sgoal in
          if is_empty (Free.uvars_uncached e) && is_empty (Free.uvars_uncached sgoal') then
            cache := HM.add key (Some (abstract_univ_uvars e sgoal')) !cache);
        match try_teq st.env goal sgoal with
        | None ->
          UF.rollback tx;
          None
        | Some g ->
          UF.commit tx;
          debug (fun () -> "solved " ^ show goal ^ " := " ^ show e);
          Some (e, imps0 @ imps @ guard_imps g)
  )
  | _ ->
    debug (fun () -> "not a class: " ^ show goal);
    None

(* The goal with its functional dependencies replaced by fresh uvars. *)
and fresh_fundeps (st:st) (cls:Ident.lident) (hd:term) (args:S.args) (fds:list int)
  : ML (typ & list implicit) =
  if Nil? fds then S.mk_Tm_app hd args hd.pos, [] else
  let us = match (SS.compress hd).n with Tm_uinst (_, us) -> us | _ -> [] in
  match Env.try_lookup_and_inst_lid st.env us cls with
  | None -> S.mk_Tm_app hd args hd.pos, []
  | Some (k, _) ->
    let bs, _ = U.arrow_formals k in
    let rec go (i:int) (subst:list subst_elt) (bs:binders) (args:S.args) (acc:S.args) (imps:list implicit)
      : ML (S.args & list implicit) =
      match bs, args with
      | b :: bs, (a, q) :: args ->
        let a, imps =
          if List.mem i fds then
            let sort = SS.subst subst b.binder_bv.sort in
            let u, _, g = Env.new_implicit_var_aux "typeclass functional dependency" a.pos st.env sort
                            (Allow_untyped "typeclass functional dependency") None false in
            u, imps @ guard_imps g
          else a, imps
        in
        go (i + 1) (subst @ [NT (b.binder_bv, a)]) bs args ((a, q) :: acc) imps
      | _, args -> List.rev acc @ args, imps
    in
    let args, imps = go 0 [] bs args [] [] in
    S.mk_Tm_app hd args hd.pos, imps

and search (gs:gst) (st:st) (cls:Ident.lident) (goal:typ) : ML result =
  let locals =
    st.scope.tc_locals |> List.filter (fun x ->
      match class_of_typ st.env x.sort with
      | Some c -> Ident.lid_equals c cls
      | None -> false)
  in
  let rec try_locals (xs:list bv) : ML result =
    match xs with
    | [] -> try_globals (global_instances st.env)
    | x :: xs ->
      match try_instance gs st goal (S.bv_to_name x) x.sort with
      | Some r -> Some r
      | None -> try_locals xs
  and try_globals (l:list (Ident.lident & Ident.lident)) : ML result =
    match l with
    | [] -> None
    | (c, lid) :: l ->
      if not (Ident.lid_equals c cls) then try_globals l else
      match Env.try_lookup_lid st.env lid with
      | None -> try_globals l
      | Some ((us, t), _) ->
        match try_instance gs st goal (S.mk_Tm_uinst (S.fvar lid None) us) t with
        | Some r -> Some r
        | None -> try_globals l
  in
  try_locals locals

(* Apply the instance [inst : t] to fresh uvars, unify its result type with
   the goal, and solve the typeclass arguments (and the explicit ones whose
   type is a class, unit or squash, and the implicit ones of type unit or
   squash) as goals of their own.  The other
   arguments must be determined by unification. *)
and try_instance (gs:gst) (st:st) (goal:typ) (inst:term) (t:typ) : ML result =
  debug (fun () -> "trying " ^ show inst ^ " for " ^ show goal);
  let tx = UF.new_transaction () in
  let env = with_scope st.env st.scope in
  let bs, c = U.arrow_formals_comp_strict t in
  let uvs, g0 = Env.uvars_for_binders env bs [] (fun b -> "typeclass instance argument " ^ show b) gs.rng in
  let subst = List.map2 (fun b u -> NT (b.binder_bv, u)) bs uvs in
  let res_ty = U.unrefine (SS.subst subst (U.comp_result c)) in
  let e = S.mk_Tm_app inst (List.map2 (fun b u -> (u, U.aqual_of_binder b)) bs uvs) gs.rng in
  let fail () : ML result = UF.rollback tx; None in
  match try_teq env res_ty goal with
  | None -> fail ()
  | Some g1 ->
    let subgoals =
      List.zip bs uvs |> List.filter (fun (b, _) ->
        U.is_tc_bqual b.binder_qual ||
        (None? b.binder_qual && is_subgoal_typ env b.binder_bv.sort) ||
        ((match b.binder_qual with Some (Implicit _) -> true | _ -> false) && is_unit_or_squash b.binder_bv.sort))
      |> List.map snd
    in
    (* Solve the subgoals whose type is closed first: solving one may close
       another. *)
    let rec go (pending:list term) (imps:list implicit) : ML (option (list implicit)) =
      match List.filter unresolved pending with
      | [] -> Some imps
      | pending ->
        let ty_of (u:term) : ML typ =
          match (SS.compress u).n with
          | Tm_uvar (ctx_u, _) -> U.ctx_uvar_typ ctx_u
          | _ -> failwith "impossible"
        in
        let u =
          match List.tryFind (fun u -> not (Rel.typeclass_goal_is_open env (ty_of u))) pending with
          | Some u -> u
          | None -> List.hd pending
        in
        match solve gs st (ty_of u) with
        | None -> None
        | Some (e', imps') ->
          match Rel.teq_nosmt env u e' with
          | None -> None
          | Some g ->
            (* [e'] is well-typed by construction, modulo [imps']. *)
            mark_checked u;
            go pending (imps @ imps' @ guard_imps g)
    in
    match go subgoals [] with
    | None -> fail ()
    | Some imps ->
      UF.commit tx;
      Some (e, guard_imps g0 @ guard_imps g1 @ imps)

let resolve (env:Env.env) (scope:tc_scope) (goal:typ) (rng:Range.t) : ML (term & list implicit) =
  let gs = { steps = mk_ref 0; cuts = mk_ref 0; warned = mk_ref false; rng } in
  let st = { env = with_scope env scope; scope; seen = []; depth = 0 } in
  debug (fun () -> "resolve " ^ show goal);
  match solve gs st goal with
  | Some r -> r
  | None ->
    Errors.raise_error rng Errors.Fatal_UserTacticFailure [
      prefix 2 1 (text "Could not solve typeclass constraint")
        (fquotes (N.term_to_doc env goal));
    ]
