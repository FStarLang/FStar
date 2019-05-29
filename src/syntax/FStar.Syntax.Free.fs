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
// (c) Microsoft Corporation. All rights reserved
module FStar.Syntax.Free
open FStar.ST
open FStar.All

open Prims
open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
module Util = FStar.Util
module UF = FStar.Syntax.Unionfind


(********************************************************************************)
(************************* Free names and unif variables ************************)
(********************************************************************************)

type free_vars_and_fvars = free_vars * set<Ident.lident>

let no_free_vars = {
    free_names=[];
    free_uvars=[];
    free_univs=[];
    free_univ_names=[];
}, new_fv_set ()

let singleton_fvar fv =
    fst no_free_vars,
    Util.set_add fv.fv_name.v (new_fv_set ())

let singleton_bv x   = {fst no_free_vars with free_names=[x]}, snd no_free_vars
let singleton_uv x   = {fst no_free_vars with free_uvars=[x]}, snd no_free_vars
let singleton_univ x = {fst no_free_vars with free_univs=[x]}, snd no_free_vars
let singleton_univ_name x = {fst no_free_vars with free_univ_names=[x]}, snd no_free_vars

let union (f1 : free_vars_and_fvars) (f2 : free_vars_and_fvars) = {
    free_names=(fst f1).free_names @ (fst f2).free_names;
    free_uvars=(fst f1).free_uvars @ (fst f2).free_uvars;
    free_univs=(fst f1).free_univs @ (fst f2).free_univs;
    free_univ_names=(fst f1).free_univ_names @ (fst f2).free_univ_names; //THE ORDER HERE IS IMPORTANT!
    //We expect the free_univ_names list to be in fifo order to get the right order of universe generalization
}, Util.set_union (snd f1) (snd f2)

let rec free_univs u = match Subst.compress_univ u with
  | U_zero
  | U_bvar   _
  | U_unknown -> no_free_vars
  | U_name uname -> singleton_univ_name uname
  | U_succ u -> free_univs u
  | U_max us -> List.fold_left (fun out x -> union out (free_univs x)) no_free_vars us
  | U_unif u -> singleton_univ u

//the interface of Syntax.Free now supports getting fvars in a term also
//however, fvars are added unlike free names, free uvars, etc. which are part of a record free_vars, that is memoized at **every** AST node
//if we added fvars also to the record, it would affect every AST node
//instead of doing that, the functions below compute a tuple, free_vars * set<lident>, where the second component is the fvars lids
//but this raises a compilication, what should happen when the functions below just return from the cache from the AST nodes
//to handle that, use_cache flag is UNSET when asking for free_fvars, so that all the terms are traversed completely
//on the other hand, for earlier interface use_cache is true
//this flag is propagated, and is used in the function should_invalidate_cache below
let rec free_names_and_uvs' tm use_cache : free_vars_and_fvars =
    let aux_binders (bs : binders) (from_body : free_vars_and_fvars) =
        let from_binders = bs |> List.fold_left (fun n (x, _) -> union n (free_names_and_uvars x.sort use_cache)) no_free_vars in
        union from_binders from_body
    in
    let t = Subst.compress tm in
    match t.n with
      | Tm_delayed _ -> failwith "Impossible"

      | Tm_name x ->
        singleton_bv x

      | Tm_uvar (uv, _) ->
        singleton_uv uv

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
        List.fold_left (fun out u -> union out (free_univs u)) f us

      | Tm_abs(bs, t, _) ->
        aux_binders bs (free_names_and_uvars t use_cache)

      | Tm_arrow (bs, c) ->
        aux_binders bs (free_names_and_uvars_comp c use_cache)

      | Tm_refine(bv, t) ->
        aux_binders [bv, None] (free_names_and_uvars t use_cache)

      | Tm_app(t, args) ->
        free_names_and_uvars_args args (free_names_and_uvars t use_cache) use_cache

      | Tm_match(t, pats) ->
        pats |> List.fold_left (fun n (p, wopt, t) ->
            let n1 = match wopt with
                | None ->   no_free_vars
                | Some w -> free_names_and_uvars w use_cache
            in
            let n2 = free_names_and_uvars t use_cache in
            let n =
              pat_bvs p |> List.fold_left (fun n x -> union n (free_names_and_uvars x.sort use_cache)) n
            in
            union n (union n1 n2) )
            (free_names_and_uvars t use_cache)

      | Tm_ascribed(t1, asc, _) ->
        let u1 = free_names_and_uvars t1 use_cache in
        let u2 = match fst asc with
         | Inl t2 -> free_names_and_uvars t2 use_cache
         | Inr c2 -> free_names_and_uvars_comp c2 use_cache in
        (match snd asc with
         | None -> union u1 u2
         | Some tac -> union (union u1 u2) (free_names_and_uvars tac use_cache))

      | Tm_let(lbs, t) ->
        snd lbs |> List.fold_left (fun n lb ->
          union n (union (free_names_and_uvars lb.lbtyp use_cache) (free_names_and_uvars lb.lbdef use_cache)))
          (free_names_and_uvars t use_cache)

      | Tm_quoted (tm, qi) ->
        begin match qi.qkind with
        | Quote_static  -> no_free_vars
        | Quote_dynamic -> free_names_and_uvars tm use_cache
        end

      | Tm_meta(t, m) ->
        let u1 = free_names_and_uvars t use_cache in
        begin match m with
        | Meta_pattern (_, args, _) ->
            List.fold_right (fun a acc -> free_names_and_uvars_args a acc use_cache) args u1

        | Meta_monadic(_, t') ->
          union u1 (free_names_and_uvars t' use_cache)

        | Meta_monadic_lift(_, _, t') ->
          union u1 (free_names_and_uvars t' use_cache)

        | Meta_labeled _
        | Meta_desugared _
        | Meta_named _ -> u1
        end


and free_names_and_uvars t use_cache =
  let t = Subst.compress t in
  match !t.vars with
  | Some n when not (should_invalidate_cache n use_cache) -> n, new_fv_set ()
  | _ ->
      t.vars := None;
      let n = free_names_and_uvs' t use_cache in
      t.vars := Some (fst n);
      n

and free_names_and_uvars_args args (acc:free_vars * set<Ident.lident>) use_cache =
        args |> List.fold_left (fun n (x, _) -> union n (free_names_and_uvars x use_cache)) acc

and free_names_and_uvars_binders (bs:binders) acc use_cache =
        bs |> List.fold_left (fun n (x, _) -> union n (free_names_and_uvars x.sort use_cache)) acc

and free_names_and_uvars_comp c use_cache =
    match !c.vars with
        | Some n ->
          if should_invalidate_cache n use_cache
          then (c.vars := None; free_names_and_uvars_comp c use_cache)
          else n, new_fv_set ()
        | _ ->
         let n = match c.n with
            | GTotal (t, None)
            | Total (t, None) ->
              free_names_and_uvars t use_cache

            | GTotal (t, Some u)
            | Total (t, Some u) ->
              union (free_univs u) (free_names_and_uvars t use_cache)

            | Comp ct ->
              let us = free_names_and_uvars_args ct.effect_args (free_names_and_uvars ct.result_typ use_cache) use_cache in
              List.fold_left (fun us u -> union us (free_univs u)) us ct.comp_univs in
         c.vars := Some (fst n);
         n

and should_invalidate_cache n use_cache =
    not use_cache ||
      (n.free_uvars |> Util.for_some (fun u ->
         match UF.find u.ctx_uvar_head with
         | Some _ -> true
         | _ -> false)
   || n.free_univs |> Util.for_some (fun u ->
           match UF.univ_find u with
           | Some _ -> true
           | None -> false)
      )

//note use_cache is set false ONLY for fvars, which is not maintained at each AST node
//see the comment above
let compare_uv uv1 uv2 = UF.uvar_id uv1.ctx_uvar_head - UF.uvar_id uv2.ctx_uvar_head
let new_uv_set () : uvars = Util.new_set compare_uv

let compare_universe_uvar x y = UF.univ_uvar_id x - UF.univ_uvar_id y
let new_universe_uvar_set () : set<universe_uvar> =
    Util.new_set compare_universe_uvar

let empty = Util.new_set Syntax.order_bv
let names t = FStar.Util.as_set (fst (free_names_and_uvars t true)).free_names Syntax.order_bv
let uvars t = FStar.Util.as_set (fst (free_names_and_uvars t true)).free_uvars compare_uv
let univs t = FStar.Util.as_set (fst (free_names_and_uvars t true)).free_univs compare_universe_uvar
let univnames t = FStar.Util.as_set (fst (free_names_and_uvars t true)).free_univ_names Syntax.order_univ_name
let univnames_comp c = FStar.Util.as_set (fst (free_names_and_uvars_comp c true)).free_univ_names Syntax.order_univ_name
let fvars t = snd (free_names_and_uvars t false)
let names_of_binders (bs:binders) = FStar.Util.as_set ((fst (free_names_and_uvars_binders bs no_free_vars true)).free_names) Syntax.order_bv
