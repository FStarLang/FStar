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
module FStar.Syntax.InstFV
open FStar.ST
open FStar.All
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Util
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Util
type inst_t = list<(lident * universes)>



let mk t s = S.mk s None t.pos

let rec inst (s:term -> fv -> term) t =
    let t = SS.compress t in
    let mk = mk t in
    match t.n with
      | Tm_delayed _ -> failwith "Impossible"

      | Tm_name _
      | Tm_uvar _
      | Tm_uvar _
      | Tm_type _
      | Tm_bvar _
      | Tm_constant _
      | Tm_quoted _
      | Tm_unknown
      | Tm_uinst _ -> t

      | Tm_lazy _ -> t

      | Tm_fvar fv ->
        s t fv

      | Tm_abs(bs, body, lopt) ->
        let bs = inst_binders s bs in
        let body = inst s body in
        mk (Tm_abs(bs, body, inst_lcomp_opt s lopt))

      | Tm_arrow (bs, c) ->
        let bs = inst_binders s bs in
        let c = inst_comp s c in
        mk (Tm_arrow(bs, c))

      | Tm_refine(bv, t) ->
        let bv = {bv with sort=inst s bv.sort} in
        let t = inst s t in
        mk (Tm_refine(bv, t))

      | Tm_app(t, args) ->
        mk (Tm_app(inst s t, inst_args s args))

      | Tm_match(t, pats) ->
        let pats = pats |> List.map (fun (p, wopt, t) ->
            let wopt = match wopt with
                | None ->   None
                | Some w -> Some (inst s w) in
            let t = inst s t in
            (p, wopt, t)) in
        mk (Tm_match(inst s t, pats))

      | Tm_ascribed(t1, asc, f) ->
        let inst_asc (annot, topt) =
            let topt = FStar.Util.map_opt topt (inst s) in
            let annot = match annot with
                | Inl t -> Inl (inst s t)
                | Inr c -> Inr (inst_comp s c) in
            annot, topt
        in
        mk (Tm_ascribed(inst s t1, inst_asc asc, f))

      | Tm_let(lbs, t) ->
        let lbs = fst lbs, snd lbs |> List.map (fun lb -> {lb with lbtyp=inst s lb.lbtyp; lbdef=inst s lb.lbdef}) in
        mk (Tm_let(lbs, inst s t))

      | Tm_meta(t, Meta_pattern (bvs, args)) ->
        mk (Tm_meta(inst s t, Meta_pattern (bvs, args |> List.map (inst_args s))))

      | Tm_meta(t, Meta_monadic (m, t')) ->
        mk (Tm_meta(inst s t, Meta_monadic(m, inst s t')))

      | Tm_meta(t, tag) ->
        mk (Tm_meta(inst s t, tag))

and inst_binders s bs = bs |> List.map (fun (x, imp) -> {x with sort=inst s x.sort}, imp)

and inst_args s args = args |> List.map (fun (a, imp) -> inst s a, imp)

and inst_comp s c = match c.n with
    | Total (t, uopt) -> S.mk_Total' (inst s t) uopt
    | GTotal (t, uopt) -> S.mk_GTotal' (inst s t) uopt
    | Comp ct -> let ct = {ct with result_typ=inst s ct.result_typ;
                                   effect_args=inst_args s ct.effect_args;
                                   flags=ct.flags |> List.map (function
                                        | DECREASES t -> DECREASES (inst s t)
                                        | f -> f)} in
                 S.mk_Comp ct


and inst_lcomp_opt s l = match l with
    | None -> None
    | Some rc -> Some ({rc with residual_typ = FStar.Util.map_opt rc.residual_typ (inst s)})

let instantiate i t = match i with
    | [] -> t
    | _ ->
      let inst_fv (t: term) (fv: S.fv) : term =
        begin match U.find_opt (fun (x, _) -> lid_equals x fv.fv_name.v) i with
            | None -> t
            | Some (_, us) -> mk t (Tm_uinst(t, us))
        end
      in
        inst inst_fv t

