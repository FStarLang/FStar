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

let rec collect_k (l:list<'a>) (f:'a -> ('b -> 'c) -> 'c) (acc:'b) (sum:'b -> 'b -> 'b) (k:'b -> 'c) : 'c =
    match l with
    | [] -> k acc
    | hd::tl -> f hd (fun next -> collect_k tl f (sum acc next) sum k)

let rec free_names_and_uvars tm (k:free_vars -> 'z) : 'z =
    let aux_binders bs from_body k =
        collect_k bs (fun (x, _) -> free_names_and_uvars x.sort) from_body union k
    in
    let t = Subst.compress tm in
    match t.n with
      | Tm_delayed _ ->
        failwith "Impossible"

      | Tm_name x ->
        k (singleton_bv x)

      | Tm_uvar (x, t) ->
        k (singleton_uv (x,t))

      | Tm_type u ->
        k (free_univs u)

      | Tm_bvar _ ->
        k no_free_vars

      | Tm_fvar fv ->
        k (singleton_fvar fv)

      | Tm_constant _
      | Tm_unknown ->
        k no_free_vars

      | Tm_uinst(t, us) ->
        free_names_and_uvars t (fun f ->
        k (List.fold_left (fun out u -> union out (free_univs u)) f us))

      | Tm_abs(bs, t, _) ->
        free_names_and_uvars t (fun f ->
        aux_binders bs f k)

      | Tm_arrow (bs, c) ->
        free_names_and_uvars_comp c (fun f ->
        aux_binders bs f k)

      | Tm_refine(bv, t) ->
        free_names_and_uvars t (fun f ->
        aux_binders [bv, None] f k)

      | Tm_app(t, args) ->
        free_names_and_uvars t (fun f ->
        free_names_and_uvars_args args f k)

      | Tm_match(t, pats) ->
        let free_pat (p, wopt, t) k =
             (match wopt with
              | None ->   (fun k -> k no_free_vars)
              | Some w -> free_names_and_uvars w)
             (fun n1 ->
               free_names_and_uvars t
             (fun n2 ->
               collect_k (pat_bvs p) (fun x -> free_names_and_uvars x.sort) (union n1 n2) union k))
        in
        free_names_and_uvars t (fun n ->
        collect_k pats free_pat n union k)

      | Tm_ascribed(t1, asc, _) ->
        free_names_and_uvars t1
        (fun u1 ->
            (match fst asc with
             | Inl t2 -> free_names_and_uvars t2
             | Inr c2 -> free_names_and_uvars_comp c2)
        (fun u2 ->
            let u12 = union u1 u2 in
            (match snd asc with
            | None -> k u12
            | Some tac -> free_names_and_uvars tac (fun u3 ->
                          k (union u12 u3)))))

      | Tm_let(lbs, t) ->
        let free_lb lb k =
            free_names_and_uvars lb.lbtyp (fun n1 ->
            free_names_and_uvars lb.lbdef (fun n2 ->
            k (union n1 n2)))
        in
        free_names_and_uvars t (fun n ->
        collect_k (snd lbs) free_lb n union k)

      | Tm_meta(t, Meta_pattern args_l) ->
        free_names_and_uvars t (fun f ->
        free_names_and_uvars_args (List.flatten args_l) f k)

      | Tm_meta(t, Meta_monadic(_, t')) ->
        free_names_and_uvars t (fun f ->
        free_names_and_uvars t' (fun g -> k (union f g)))

      | Tm_meta(t, _) ->
        free_names_and_uvars t k

and free_names_and_uvars_args args (acc:free_vars) (k:free_vars -> 'z) : 'z =
    collect_k args (fun (x, _) -> free_names_and_uvars x) acc union k

and free_names_and_uvars_binders (bs:binders) acc k =
    collect_k bs (fun (x, _) -> free_names_and_uvars x.sort) acc union k

and free_names_and_uvars_comp c k =
    match c.n with
    | GTotal (t, None)
    | Total (t, None) ->
      free_names_and_uvars t k

    | GTotal (t, Some u)
    | Total (t, Some u) ->
      free_names_and_uvars t (fun f -> k (union (free_univs u) f))

    | Comp ct ->
      let free_univs = List.fold_left (fun us u -> union us (free_univs u)) no_free_vars ct.comp_univs in
      free_names_and_uvars_args ct.effect_args free_univs (fun f ->
      free_names_and_uvars ct.result_typ (fun g -> k (union f g)))

let free t = free_names_and_uvars t (fun x -> x)
let names t = (free t).free_names
let uvars t = (free t).free_uvars
let univs t = (free t).free_univs
let univnames t = (free t).free_univ_names
let fvars t = (free t).free_fvars
let names_of_binders (bs:binders) = (free_names_and_uvars_binders bs no_free_vars (fun x -> x)).free_names
