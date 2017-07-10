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

type free_vars = {
    free_names:set<bv>;
    free_uvars:uvars;
    free_univs:set<universe_uvar>;
    free_univ_names:fifo_set<univ_name>;
    free_fvars:set<Ident.lident>
}

let new_uv_set () : uvars   = Util.new_set (fun (x, _) (y, _) -> UF.uvar_id x - UF.uvar_id y)
                                           (fun (x, _) -> UF.uvar_id x)
let new_universe_uvar_set () : set<universe_uvar> =
    Util.new_set (fun x y -> UF.univ_uvar_id x - UF.univ_uvar_id y)
                 (fun x -> UF.univ_uvar_id x)

let no_uvs : uvars = new_uv_set()
let no_universe_uvars = new_universe_uvar_set()

let no_free_vars = {
    free_names=no_names;
    free_uvars=no_uvs;
    free_univs=no_universe_uvars;
    free_univ_names=no_universe_names;
    free_fvars=new_fv_set()
}

let singleton_bv x   = { no_free_vars with
    free_names=Util.set_add x no_free_vars.free_names
}
let singleton_uv x   = { no_free_vars with
    free_uvars=Util.set_add x no_free_vars.free_uvars
}
let singleton_univ x = { no_free_vars with
    free_univs=Util.set_add x no_free_vars.free_univs
}
let singleton_univ_name x = { no_free_vars with
    free_univ_names=Util.fifo_set_add x no_free_vars.free_univ_names
}
let singleton_fvar fv = { no_free_vars with
    free_fvars=Util.set_add fv.fv_name.v no_free_vars.free_fvars
}
let union f1 f2 = {
    free_names=Util.set_union f1.free_names f2.free_names;
    free_uvars=Util.set_union f1.free_uvars f2.free_uvars;
    free_univs=Util.set_union f1.free_univs f2.free_univs;
    free_univ_names=Util.fifo_set_union f1.free_univ_names f2.free_univ_names;
    free_fvars=Util.set_union f1.free_fvars f2.free_fvars
}

let rec free_univs u = match Subst.compress_univ u with
  | U_zero
  | U_bvar   _
  | U_unknown -> no_free_vars
  | U_name uname -> singleton_univ_name uname
  | U_succ u -> free_univs u
  | U_max us -> List.fold_left (fun out x -> union out (free_univs x)) no_free_vars us
  | U_unif u -> singleton_univ u

let rec free_names_and_uvs' tm : free_vars =
    let aux_binders bs from_body =
        let from_binders = bs |> List.fold_left (fun n (x, _) -> union n (free_names_and_uvars x.sort)) no_free_vars in
        union from_binders from_body
    in
    let t = Subst.compress tm in
    match t.n with
      | Tm_delayed _ -> failwith "Impossible"

      | Tm_name x ->
        singleton_bv x

      | Tm_uvar (x, t) ->
        singleton_uv (x,t)

      | Tm_type u ->
        free_univs u

      | Tm_bvar _ -> no_free_vars
      | Tm_fvar fv -> singleton_fvar fv
      | Tm_constant _
      | Tm_unknown ->
        no_free_vars

      | Tm_uinst(t, us) ->
        let f = free_names_and_uvars t in
        List.fold_left (fun out u -> union out (free_univs u)) f us

      | Tm_abs(bs, t, _) ->
        aux_binders bs (free_names_and_uvars t)

      | Tm_arrow (bs, c) ->
        aux_binders bs (free_names_and_uvars_comp c)

      | Tm_refine(bv, t) ->
        aux_binders [bv, None] (free_names_and_uvars t)

      | Tm_app(t, args) ->
        free_names_and_uvars_args args (free_names_and_uvars t)

      | Tm_match(t, pats) ->
        pats |> List.fold_left (fun n (p, wopt, t) ->
            let n1 = match wopt with
                | None ->   no_free_vars
                | Some w -> free_names_and_uvars w
            in
            let n2 = free_names_and_uvars t in
            let n =
              pat_bvs p |> List.fold_left (fun n x -> union n (free_names_and_uvars x.sort)) n
            in
            union n (union n1 n2) )
            (free_names_and_uvars t)

      | Tm_ascribed(t1, asc, _) ->
        let u1 = free_names_and_uvars t1 in
        let u2 = match fst asc with
         | Inl t2 -> free_names_and_uvars t2
         | Inr c2 -> free_names_and_uvars_comp c2 in
        (match snd asc with
         | None -> union u1 u2
         | Some tac -> union (union u1 u2) (free_names_and_uvars tac))

      | Tm_let(lbs, t) ->
        snd lbs |> List.fold_left (fun n lb ->
          union n (union (free_names_and_uvars lb.lbtyp) (free_names_and_uvars lb.lbdef)))
          (free_names_and_uvars t)

      | Tm_meta(t, Meta_pattern args) ->
        List.fold_right (fun a acc -> free_names_and_uvars_args a acc) args (free_names_and_uvars t)

      | Tm_meta(t, Meta_monadic(_, t')) ->
        union (free_names_and_uvars t) (free_names_and_uvars t')

      | Tm_meta(t, _) ->
        free_names_and_uvars t

and free_names_and_uvars t =
  let t = Subst.compress t in
  free_names_and_uvs' t

and free_names_and_uvars_args args (acc:free_vars) =
        args |> List.fold_left (fun n (x, _) -> union n (free_names_and_uvars x)) acc

and free_names_and_uvars_binders (bs:binders) acc =
        bs |> List.fold_left (fun n (x, _) -> union n (free_names_and_uvars x.sort)) acc

and free_names_and_uvars_comp c =
    match c.n with
    | GTotal (t, None)
    | Total (t, None) ->
        free_names_and_uvars t

    | GTotal (t, Some u)
    | Total (t, Some u) ->
        union (free_univs u) (free_names_and_uvars t)

    | Comp ct ->
        let us = free_names_and_uvars_args ct.effect_args (free_names_and_uvars ct.result_typ) in
        List.fold_left (fun us u -> union us (free_univs u)) us ct.comp_univs

let names t = (free_names_and_uvars t).free_names
let uvars t = (free_names_and_uvars t).free_uvars
let univs t = (free_names_and_uvars t).free_univs
let univnames t = (free_names_and_uvars t).free_univ_names
let fvars t = (free_names_and_uvars t).free_fvars
let names_of_binders (bs:binders) = (free_names_and_uvars_binders bs no_free_vars).free_names
