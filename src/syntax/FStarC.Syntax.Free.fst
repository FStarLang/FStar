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
module FStarC.Syntax.Free
open FStarC.Effect
open FStarC.List

open FStarC
open FStarC.Util
open FStarC.Syntax
open FStarC.Syntax.Syntax
module UF = FStarC.Syntax.Unionfind

open FStarC.Class.Ord
open FStarC.Class.Show
open FStarC.Class.Setlike

let compare_uv uv1 uv2 = UF.uvar_id uv1.ctx_uvar_head - UF.uvar_id uv2.ctx_uvar_head
let compare_universe_uvar x y = UF.univ_uvar_id x - UF.univ_uvar_id y

instance deq_ctx_uvar : deq ctx_uvar = {
  (=?) = (fun u v -> UF.uvar_id u.ctx_uvar_head =? UF.uvar_id v.ctx_uvar_head);
}
instance ord_ctx_uvar : ord ctx_uvar = {
  super = Tactics.Typeclasses.solve;
  cmp = (fun u v -> UF.uvar_id u.ctx_uvar_head `cmp` UF.uvar_id v.ctx_uvar_head);
}
instance deq_univ_uvar : deq universe_uvar = {
  (=?) = (fun u v -> UF.univ_uvar_id u =? UF.univ_uvar_id v);
}
instance ord_univ_uvar : ord universe_uvar = {
  super = Tactics.Typeclasses.solve;
  cmp = (fun u v -> UF.univ_uvar_id u `cmp` UF.univ_uvar_id v);
}

let ctx_uvar_typ (u:ctx_uvar) = 
    (UF.find_decoration u.ctx_uvar_head).uvar_decoration_typ


(********************************************************************************)
(************************* Free names and unif variables ************************)
(********************************************************************************)

type use_cache_t =
  | Def
  | NoCache
  | Full

(* We use an RBSet for the fvars, as order definitely does not matter here
and it's faster. *)
type free_vars_and_fvars = free_vars & RBSet.t Ident.lident

(* Snoc without duplicates *)
val snoc : #a:Type -> {| deq a |} -> list a -> a -> list a
let rec snoc xx y =
  match xx with
  | [] -> [y]
  | x::xx' -> if x =? y then xx
                        else x :: snoc xx' y

(* Concatenation without duplicates *)
val (@@) : #a:Type -> {| deq a |} -> list a -> list a -> list a
let (@@) xs ys = List.fold_left (fun xs y -> snoc xs y) xs ys

let no_free_vars : free_vars_and_fvars = {
    free_names      = empty();
    free_uvars      = empty();
    free_univs      = empty();
    free_univ_names = empty();
}, empty ()

let singleton_fvar fv : free_vars_and_fvars =
    fst no_free_vars,
    add fv.fv_name.v (empty ())

let singleton_bv x =
  {fst no_free_vars with free_names = singleton x}, snd no_free_vars
let singleton_uv x =
  {fst no_free_vars with free_uvars = singleton x}, snd no_free_vars
let singleton_univ x =
  {fst no_free_vars with free_univs = singleton x}, snd no_free_vars
let singleton_univ_name x =
  {fst no_free_vars with free_univ_names = singleton x}, snd no_free_vars

(* Union of free vars *)
let ( ++ ) (f1 : free_vars_and_fvars) (f2 : free_vars_and_fvars) = {
    free_names=(fst f1).free_names `union` (fst f2).free_names;
    free_uvars=(fst f1).free_uvars `union` (fst f2).free_uvars;
    free_univs=(fst f1).free_univs `union` (fst f2).free_univs;
    free_univ_names=(fst f1).free_univ_names `union` (fst f2).free_univ_names; //THE ORDER HERE IS IMPORTANT!
    //We expect the free_univ_names list to be in fifo order to get the right order of universe generalization
}, union (snd f1) (snd f2)

let rec free_univs u = match Subst.compress_univ u with
  | U_zero
  | U_bvar   _
  | U_unknown -> no_free_vars
  | U_name uname -> singleton_univ_name uname
  | U_succ u -> free_univs u
  | U_max us -> List.fold_left (fun out x -> out ++ free_univs x) no_free_vars us
  | U_unif u -> singleton_univ u

//the interface of Syntax.Free now supports getting fvars in a term also
//however, fvars are added unlike free names, free uvars, etc. which are part of a record free_vars, that is memoized at **every** AST node
//if we added fvars also to the record, it would affect every AST node
//instead of doing that, the functions below compute a tuple, free_vars * set lident, where the second component is the fvars lids
//but this raises a compilication, what should happen when the functions below just return from the cache from the AST nodes
//to handle that, use_cache flag is UNSET when asking for free_fvars, so that all the terms are traversed completely
//on the other hand, for earlier interface use_cache is true
//this flag is propagated, and is used in the function should_invalidate_cache below
let rec free_names_and_uvs' tm (use_cache:use_cache_t) : free_vars_and_fvars =
    let aux_binders (bs : binders) (from_body : free_vars_and_fvars) =
        let from_binders = free_names_and_uvars_binders bs use_cache in
        from_binders ++ from_body
    in
    let t = Subst.compress tm in
    match t.n with
      | Tm_delayed _ -> failwith "Impossible"

      | Tm_name x ->
        singleton_bv x

      | Tm_uvar (uv, (s, _)) ->
        singleton_uv uv ++
        (if use_cache = Full
         then free_names_and_uvars (ctx_uvar_typ uv) use_cache
         else no_free_vars)

      | Tm_type u ->
        free_univs u

      | Tm_bvar _ -> no_free_vars
      | Tm_fvar fv -> singleton_fvar fv

      | Tm_constant _
      | Tm_lazy _
      | Tm_unknown ->
        no_free_vars

      | Tm_uinst(t, us) ->
        let f = free_names_and_uvars t use_cache in
        List.fold_left (fun out u -> out ++ free_univs u) f us

      | Tm_abs {bs; body=t; rc_opt=ropt} ->
        aux_binders bs (free_names_and_uvars t use_cache) ++
        (match ropt with
         | Some { residual_typ = Some t } ->  free_names_and_uvars t use_cache
         | _ -> no_free_vars)

      | Tm_arrow {bs; comp=c} ->
        aux_binders bs (free_names_and_uvars_comp c use_cache)

      | Tm_refine {b=bv; phi=t} ->
        aux_binders [mk_binder bv] (free_names_and_uvars t use_cache)

      | Tm_app {hd=t; args} ->
        free_names_and_uvars_args args (free_names_and_uvars t use_cache) use_cache

      | Tm_match {scrutinee=t; ret_opt=asc_opt; brs=pats; rc_opt} ->
        (match rc_opt with
         | Some { residual_typ = Some t } -> free_names_and_uvars t use_cache
         | _ -> no_free_vars) ++
        begin
        pats |> List.fold_left (fun n (p, wopt, t) ->
            let n1 = match wopt with
                | None ->   no_free_vars
                | Some w -> free_names_and_uvars w use_cache
            in
            let n2 = free_names_and_uvars t use_cache in
            let n =
              pat_bvs p |> List.fold_left (fun n x -> n ++ free_names_and_uvars x.sort use_cache) n
            in
            n ++ n1 ++ n2)
            (free_names_and_uvars t use_cache
             ++ (match asc_opt with
                 | None -> no_free_vars
                 | Some (b, asc) ->
                   free_names_and_uvars_binders [b] use_cache ++
                   free_names_and_uvars_ascription asc use_cache))
        end

      | Tm_ascribed {tm=t1; asc} ->
        free_names_and_uvars t1 use_cache ++
        free_names_and_uvars_ascription asc use_cache

      | Tm_let {lbs; body=t} ->
        snd lbs |> List.fold_left (fun n lb ->
          n ++
          free_names_and_uvars lb.lbtyp use_cache ++
          free_names_and_uvars lb.lbdef use_cache)
        (free_names_and_uvars t use_cache)

      | Tm_quoted (tm, qi) ->
        begin match qi.qkind with
        | Quote_static  -> List.fold_left (fun n t -> n ++ free_names_and_uvars t use_cache) no_free_vars (snd qi.antiquotations)
        | Quote_dynamic -> free_names_and_uvars tm use_cache
        end

      | Tm_meta {tm=t; meta=m} ->
        let u1 = free_names_and_uvars t use_cache in
        begin match m with
        | Meta_pattern (_, args) ->
            List.fold_right (fun a acc -> free_names_and_uvars_args a acc use_cache) args u1

        | Meta_monadic(_, t') ->
          u1 ++ free_names_and_uvars t' use_cache

        | Meta_monadic_lift(_, _, t') ->
          u1 ++ free_names_and_uvars t' use_cache

        | Meta_labeled _
        | Meta_desugared _
        | Meta_named _ -> u1
        end


and free_names_and_uvars_binders bs use_cache =
  bs |> List.fold_left (fun n b ->
    n ++ free_names_and_uvars b.binder_bv.sort use_cache) no_free_vars


and free_names_and_uvars_ascription asc use_cache =
  let asc, tacopt, _ = asc in
  (match asc with
   | Inl t -> free_names_and_uvars t use_cache
   | Inr c -> free_names_and_uvars_comp c use_cache) ++
  (match tacopt with
   | None -> no_free_vars
   | Some tac -> free_names_and_uvars tac use_cache)

and free_names_and_uvars t use_cache =
  let t = Subst.compress t in
  match !t.vars with
  | Some n when not (should_invalidate_cache n use_cache) -> n, empty ()
  | _ ->
      t.vars := None;
      let n = free_names_and_uvs' t use_cache in
      if use_cache <> Full then t.vars := Some (fst n);
      n

and free_names_and_uvars_args args (acc : free_vars_and_fvars) use_cache =
   args |> List.fold_left (fun n (x, _) -> n ++ (free_names_and_uvars x use_cache)) acc

and free_names_and_uvars_comp c use_cache =
    match !c.vars with
        | Some n ->
          if should_invalidate_cache n use_cache
          then (c.vars := None; free_names_and_uvars_comp c use_cache)
          else n, empty ()
        | _ ->
         let n = match c.n with
            | GTotal t
            | Total t ->
              free_names_and_uvars t use_cache

            | Comp ct ->
              //collect from the decreases clause
              let decreases_vars =
                match List.tryFind (function DECREASES _ -> true | _ -> false) ct.flags with
                | None -> no_free_vars
                | Some (DECREASES dec_order) ->
                  free_names_and_uvars_dec_order dec_order use_cache
              in
              //decreases clause + return type
              let us = free_names_and_uvars ct.result_typ use_cache ++ decreases_vars in
              //decreases clause + return type + effect args
              let us = free_names_and_uvars_args ct.effect_args us use_cache in
              //decreases clause + return type + effect args + comp_univs
              List.fold_left (fun us u -> us ++ free_univs u) us ct.comp_univs
         in
         c.vars := Some (fst n);
         n

and free_names_and_uvars_dec_order dec_order use_cache =
  match dec_order with
  | Decreases_lex l ->
    l |> List.fold_left (fun acc t -> acc ++ free_names_and_uvars t use_cache) no_free_vars
  | Decreases_wf (rel, e) ->
    free_names_and_uvars rel use_cache ++
    free_names_and_uvars e use_cache

and should_invalidate_cache n use_cache =
    (use_cache <> Def) ||
    (n.free_uvars |> for_any (fun u ->
         match UF.find u.ctx_uvar_head with
         | Some _ -> true
         | _ -> false)) ||
    (n.free_univs |> for_any (fun u ->
           match UF.univ_find u with
           | Some _ -> true
           | None -> false))

//note use_cache is set false ONLY for fvars, which is not maintained at each AST node
//see the comment above

let names t = (fst (free_names_and_uvars t Def)).free_names
let uvars t = (fst (free_names_and_uvars t Def)).free_uvars
let univs t = (fst (free_names_and_uvars t Def)).free_univs

let univnames t = (fst (free_names_and_uvars t Def)).free_univ_names
let univnames_comp c = (fst (free_names_and_uvars_comp c Def)).free_univ_names

let fvars t = snd (free_names_and_uvars t NoCache)
let names_of_binders (bs:binders) =
  ((fst (free_names_and_uvars_binders bs Def)).free_names)

let uvars_uncached t = (fst (free_names_and_uvars t NoCache)).free_uvars
let uvars_full t = (fst (free_names_and_uvars t Full)).free_uvars
