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

open Prims
open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax

// VALS_HACK_HERE

(********************************************************************************)
(************************* Free names and unif variables ************************)
(********************************************************************************)
let no_free_vars = {
    free_names=no_names;
    free_uvars=no_uvs;
    free_univs=no_universe_uvars;
    free_univ_names=no_universe_names;
}
let singleton_bv x   = {
    free_names=Util.set_add x (new_bv_set());
    free_uvars=no_uvs;
    free_univs=no_universe_uvars;
    free_univ_names=no_universe_names;
}
let singleton_uv x   = {
    free_names=no_names;
    free_uvars=Util.set_add x (new_uv_set());
    free_univs=no_universe_uvars;
    free_univ_names=no_universe_names;
}
let singleton_univ x = {
    free_names=no_names;
    free_uvars=no_uvs;
    free_univs=Util.set_add x (new_universe_uvar_set());
    free_univ_names=no_universe_names;
}


let singleton_univ_name x = {
    free_names=no_names;
    free_uvars=no_uvs;
    free_univs=no_universe_uvars;
    free_univ_names=Util.fifo_set_add x (new_universe_names_fifo_set ())
}

let union f1 f2 = {
    free_names=Util.set_union f1.free_names f2.free_names;
    free_uvars=Util.set_union f1.free_uvars f2.free_uvars;
    free_univs=Util.set_union f1.free_univs f2.free_univs;
    free_univ_names=Util.fifo_set_union f1.free_univ_names f2.free_univ_names
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

      | Tm_bvar _
      | Tm_fvar _
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

      | Tm_ascribed(t1, Inl t2, _) ->
        union (free_names_and_uvars t1) (free_names_and_uvars t2)

      | Tm_ascribed(t1, Inr c, _) ->
        union (free_names_and_uvars t1) (free_names_and_uvars_comp c)

      | Tm_let(lbs, t) ->
        snd lbs |> List.fold_left (fun n lb ->
          union n (union (free_names_and_uvars lb.lbtyp) (free_names_and_uvars lb.lbdef)))
          (free_names_and_uvars t)

      | Tm_meta(t, Meta_pattern args) ->
        List.fold_right free_names_and_uvars_args args (free_names_and_uvars t)

      | Tm_meta(t, Meta_monadic(_, t')) ->
        union (free_names_and_uvars t) (free_names_and_uvars t')

      | Tm_meta(t, _) ->
        free_names_and_uvars t

and free_names_and_uvars t =
  let t = Subst.compress t in
  match !t.vars with
  | Some n when not (should_invalidate_cache n) -> n
  | _ ->
      t.vars := None;
      let n = free_names_and_uvs' t in
      t.vars := Some n;
      n

and free_names_and_uvars_args args acc =
        args |> List.fold_left (fun n (x, _) -> union n (free_names_and_uvars x)) acc

and free_names_and_uvars_binders bs acc =
        bs |> List.fold_left (fun n (x, _) -> union n (free_names_and_uvars x.sort)) acc

and free_names_and_uvars_comp c =
    match !c.vars with
        | Some n ->
          if should_invalidate_cache n
          then (c.vars := None; free_names_and_uvars_comp c)
          else n
        | _ ->
         let n = match c.n with
            | GTotal (t, None)
            | Total (t, None) ->
              free_names_and_uvars t

            | GTotal (t, Some u)
            | Total (t, Some u) ->
              union (free_univs u) (free_names_and_uvars t)

            | Comp ct ->
              let us = free_names_and_uvars_args ct.effect_args (free_names_and_uvars ct.result_typ) in
              List.fold_left (fun us u -> union us (free_univs u)) us ct.comp_univs in
         c.vars := Some n;
         n

and should_invalidate_cache n =
    n.free_uvars |> Util.set_elements |> Util.for_some (fun (u, _) -> match Unionfind.find u with
        | Fixed _ -> true
        | _ -> false)
    || n.free_univs |> Util.set_elements |> Util.for_some (fun u -> match Unionfind.find u with
         | Some _ -> true
         | None -> false)

let names t = (free_names_and_uvars t).free_names
let uvars t = (free_names_and_uvars t).free_uvars
let univs t = (free_names_and_uvars t).free_univs
let univnames t = (free_names_and_uvars t).free_univ_names
let names_of_binders (bs:binders) = (free_names_and_uvars_binders bs no_free_vars).free_names
